pub mod c_lib;
pub mod util;
pub use c_lib as c;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::{iter, mem, ops, str, usize};
use tree_sitter::{Language, Parser, Query, QueryCursor, QueryError, QueryMatch, Tree};

const CANCELLATION_CHECK_INTERVAL: usize = 100;

#[derive(Copy, Clone, Debug)]
pub struct Highlight(pub usize);

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Cancelled,
    InvalidLanguage,
    Unknown,
}

#[derive(Debug)]
struct LocalScope<'a> {
    inherits: bool,
    range: ops::Range<usize>,
    local_defs: Vec<(&'a str, Option<Highlight>)>,
}

#[derive(Copy, Clone, Debug)]
pub enum HighlightEvent {
    Source { start: usize, end: usize },
    HighlightStart(Highlight),
    HighlightEnd,
}

pub struct HighlightConfiguration {
    language: Language,
    query: Query,
    locals_pattern_index: usize,
    highlights_pattern_index: usize,
    highlight_indices: Vec<Option<Highlight>>,
    non_local_variable_patterns: Vec<bool>,
}

#[derive(Clone, Debug)]
pub struct Highlighter {
    pub highlight_names: Vec<String>,
}

pub struct HighlightContext {
    parser: Parser,
    cursors: Vec<QueryCursor>,
}

struct HighlightIter<'a, F, C>
where
    F: Fn(&str) -> Option<&'a HighlightConfiguration> + 'a,
    C: Iterator<Item = (QueryMatch<'a>, usize)>,
{
    context: &'a mut HighlightContext,
    _tree: Tree,
    cursor: Option<QueryCursor>,
    captures: iter::Peekable<C>,
    config: &'a HighlightConfiguration,
    source: &'a [u8],
    cancellation_flag: Option<&'a AtomicUsize>,
    injection_callback: F,
    byte_offset: usize,
    iter_count: usize,
    local_scope_capture_index: Option<u32>,
    local_def_capture_index: Option<u32>,
    local_ref_capture_index: Option<u32>,
    highlight_end_stack: Vec<usize>,
    scope_stack: Vec<LocalScope<'a>>,
    next_event: Option<HighlightEvent>,
}

impl HighlightContext {
    pub fn new() -> Self {
        HighlightContext {
            parser: Parser::new(),
            cursors: Vec::new(),
        }
    }
}

impl Highlighter {
    pub fn new(highlight_names: Vec<String>) -> Self {
        Highlighter { highlight_names }
    }

    pub fn load_configuration(
        &self,
        language: Language,
        highlights_query: &str,
        injection_query: &str,
        locals_query: &str,
    ) -> Result<HighlightConfiguration, QueryError> {
        // Concatenate the query strings, keeping track of the start offset of each section.
        let mut query_source = String::new();
        query_source.push_str(injection_query);
        let locals_query_offset = query_source.len();
        query_source.push_str(locals_query);
        let highlights_query_offset = query_source.len();
        query_source.push_str(highlights_query);

        // Construct a query with the concatenated string.
        let query = Query::new(language, &query_source)?;

        // Determine the range of pattern indices that belong to each section of the query.
        let mut locals_pattern_index = 0;
        let mut highlights_pattern_index = 0;
        for i in 0..(query.pattern_count()) {
            let pattern_offset = query.start_byte_for_pattern(i);
            if pattern_offset < highlights_query_offset {
                if pattern_offset < highlights_query_offset {
                    highlights_pattern_index += 1;
                }
                if pattern_offset < locals_query_offset {
                    locals_pattern_index += 1;
                }
            }
        }

        // Compute a mapping from the query's capture ids to the indices of the highlighter's
        // recognized highlight names.
        let highlight_indices = query
            .capture_names()
            .iter()
            .map(move |capture_name| {
                let mut best_index = None;
                let mut best_name_len = 0;
                let mut best_common_prefix_len = 0;
                for (i, highlight_name) in self.highlight_names.iter().enumerate() {
                    if highlight_name.len() > capture_name.len() {
                        continue;
                    }

                    let capture_parts = capture_name.split('.');
                    let highlight_parts = highlight_name.split('.');
                    let common_prefix_len = capture_parts
                        .zip(highlight_parts)
                        .take_while(|(a, b)| a == b)
                        .count();
                    let is_best_match = common_prefix_len > best_common_prefix_len
                        || (common_prefix_len == best_common_prefix_len
                            && highlight_name.len() < best_name_len);
                    if is_best_match {
                        best_index = Some(i);
                        best_name_len = highlight_name.len();
                        best_common_prefix_len = common_prefix_len;
                    }
                }
                best_index.map(Highlight)
            })
            .collect();

        let non_local_variable_patterns = (0..query.pattern_count())
            .map(|i| {
                query
                    .property_predicates(i)
                    .iter()
                    .any(|(prop, positive)| !*positive && prop.key.as_ref() == "local")
            })
            .collect();

        Ok(HighlightConfiguration {
            query,
            language,
            locals_pattern_index,
            highlights_pattern_index,
            highlight_indices,
            non_local_variable_patterns,
        })
    }

    pub fn highlight<'a>(
        &'a self,
        context: &'a mut HighlightContext,
        config: &'a HighlightConfiguration,
        source: &'a [u8],
        cancellation_flag: Option<&'a AtomicUsize>,
        injection_callback: impl Fn(&str) -> Option<&'a HighlightConfiguration> + 'a,
    ) -> Result<impl Iterator<Item = Result<HighlightEvent, Error>> + 'a, Error> {
        context
            .parser
            .set_language(config.language)
            .map_err(|_| Error::InvalidLanguage)?;
        unsafe { context.parser.set_cancellation_flag(cancellation_flag) };
        let tree = context.parser.parse(source, None).ok_or(Error::Cancelled)?;
        let capture_names = config.query.capture_names();

        let mut cursor = context.cursors.pop().unwrap_or(QueryCursor::new());

        // The `captures` iterator borrows the `Tree` and the `QueryCursor`, which
        // prevents them from being moved. But both of these values are really just
        // pointers, so it's actually ok to move them.
        let tree_ref = unsafe { mem::transmute::<_, &'static Tree>(&tree) };
        let cursor_ref = unsafe { mem::transmute::<_, &'static mut QueryCursor>(&mut cursor) };
        let captures = cursor_ref
            .captures(&config.query, tree_ref.root_node(), move |n| {
                &source[n.byte_range()]
            })
            .peekable();

        let mut local_scope_capture_index = None;
        let mut local_def_capture_index = None;
        let mut local_ref_capture_index = None;
        for (i, name) in capture_names.iter().enumerate() {
            let i = Some(i as u32);
            match name.as_str() {
                "local.scope" => local_scope_capture_index = i,
                "local.definition" => local_def_capture_index = i,
                "local.reference" => local_ref_capture_index = i,
                _ => {}
            }
        }

        Ok(HighlightIter {
            byte_offset: 0,
            iter_count: 0,
            next_event: None,
            highlight_end_stack: Vec::new(),
            scope_stack: vec![LocalScope {
                inherits: false,
                range: 0..usize::MAX,
                local_defs: Vec::new(),
            }],
            cursor: Some(cursor),
            _tree: tree,
            local_scope_capture_index,
            local_def_capture_index,
            local_ref_capture_index,
            captures,
            cancellation_flag,
            source,
            config,
            injection_callback,
            context,
        })
    }
}

impl<'a, F, C> HighlightIter<'a, F, C>
where
    F: Fn(&str) -> Option<&'a HighlightConfiguration> + 'a,
    C: Iterator<Item = (QueryMatch<'a>, usize)>,
{
    fn emit_event(
        &mut self,
        offset: usize,
        event: Option<HighlightEvent>,
    ) -> Option<Result<HighlightEvent, Error>> {
        if self.byte_offset < offset {
            let result = HighlightEvent::Source {
                start: self.byte_offset,
                end: offset,
            };
            self.byte_offset = offset;
            // eprintln!("EVENT {}, {:?}", self.byte_offset, event);
            self.next_event = event;
            Some(Ok(result))
        } else {
            // eprintln!("EVENT {}, {:?}", self.byte_offset, event);
            event.map(Ok)
        }
    }
}

impl<'a, F, C> Drop for HighlightIter<'a, F, C>
where
    F: Fn(&str) -> Option<&'a HighlightConfiguration> + 'a,
    C: Iterator<Item = (QueryMatch<'a>, usize)>,
{
    fn drop(&mut self) {
        if let Some(cursor) = self.cursor.take() {
            self.context.cursors.push(cursor);
        }
    }
}

impl<'a, F, C> Iterator for HighlightIter<'a, F, C>
where
    F: Fn(&str) -> Option<&'a HighlightConfiguration> + 'a,
    C: Iterator<Item = (QueryMatch<'a>, usize)>,
{
    type Item = Result<HighlightEvent, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(cancellation_flag) = self.cancellation_flag {
            self.iter_count += 1;
            if self.iter_count >= CANCELLATION_CHECK_INTERVAL {
                self.iter_count = 0;
                if cancellation_flag.load(Ordering::Relaxed) != 0 {
                    return Some(Err(Error::Cancelled));
                }
            }
        }

        if let Some(e) = self.next_event.take() {
            return Some(Ok(e));
        }

        // Consume captures until one provides a highlight.
        loop {
            // Get the next capture. If there are no more, then emit the rest of the
            // source code.
            let (query_match, capture_index) = if let Some(c) = self.captures.peek() {
                c.clone()
            } else {
                if let Some(end_byte) = self.highlight_end_stack.last().cloned() {
                    self.highlight_end_stack.pop();
                    return self.emit_event(end_byte, Some(HighlightEvent::HighlightEnd));
                }
                return self.emit_event(self.source.len(), None);
            };

            let mut capture = query_match.captures[capture_index];
            let mut pattern_index = query_match.pattern_index;

            // If any previous highlight ends before this node starts, then before
            // processing this capture, emit the source code up until the end of the
            // previous highlight, and an end event for that highlight.
            let range = capture.node.byte_range();
            if let Some(end_byte) = self.highlight_end_stack.last().cloned() {
                if end_byte <= range.start {
                    self.highlight_end_stack.pop();
                    return self.emit_event(end_byte, Some(HighlightEvent::HighlightEnd));
                }
            }
            self.captures.next();

            // Remove from the scope stack any local scopes that have already ended.
            while range.start > self.scope_stack.last().unwrap().range.end {
                self.scope_stack.pop();
            }

            // Process any local variable tracking patterns for this node.
            let mut reference_highlight = None;
            let mut definition_highlight = None;
            while pattern_index < self.config.highlights_pattern_index {
                // If the node represents a local scope, push a new local scope onto
                // the scope stack.
                if Some(capture.index) == self.local_scope_capture_index {
                    definition_highlight = None;
                    self.scope_stack.push(LocalScope {
                        inherits: true,
                        range: range.clone(),
                        local_defs: Vec::new(),
                    });
                }
                // If the node represents a definition, add a new definition to the
                // local scope at the top of the scope stack.
                else if Some(capture.index) == self.local_def_capture_index {
                    reference_highlight = None;
                    definition_highlight = None;
                    let scope = self.scope_stack.last_mut().unwrap();
                    if let Ok(name) = str::from_utf8(&self.source[range.clone()]) {
                        scope.local_defs.push((name, None));
                        definition_highlight = scope.local_defs.last_mut().map(|s| &mut s.1);
                    }
                }
                // If the node represents a reference, then try to find the corresponding
                // definition in the scope stack.
                else if Some(capture.index) == self.local_ref_capture_index {
                    if definition_highlight.is_none() {
                        definition_highlight = None;
                        if let Ok(name) = str::from_utf8(&self.source[range.clone()]) {
                            for scope in self.scope_stack.iter().rev() {
                                if let Some(highlight) =
                                    scope.local_defs.iter().rev().find_map(|i| {
                                        if i.0 == name {
                                            Some(i.1)
                                        } else {
                                            None
                                        }
                                    })
                                {
                                    reference_highlight = highlight;
                                    break;
                                }
                                if !scope.inherits {
                                    break;
                                }
                            }
                        }
                    }
                }

                // Continue processing any additional local-variable-tracking patterns
                // for the same node.
                if let Some((next_match, next_capture_index)) = self.captures.peek() {
                    let next_capture = next_match.captures[*next_capture_index];
                    if next_capture.node == capture.node {
                        pattern_index = next_match.pattern_index;
                        capture = next_capture.clone();
                        self.captures.next();
                        continue;
                    }
                }

                break;
            }

            // If the current node was found to be a local variable, then skip over any
            // highlighting patterns that are disabled for local variables.
            let mut has_highlight = true;
            while (definition_highlight.is_some() || reference_highlight.is_some())
                && self.config.non_local_variable_patterns[pattern_index]
            {
                has_highlight = false;
                if let Some((next_match, next_capture_index)) = self.captures.peek() {
                    let next_capture = next_match.captures[*next_capture_index];
                    if next_capture.node == capture.node {
                        pattern_index = next_match.pattern_index;
                        capture = next_capture.clone();
                        has_highlight = true;
                        self.captures.next();
                        continue;
                    }
                }
                break;
            }
            if !has_highlight {
                continue;
            }

            // Once a highlighting pattern is found for the current node, skip over
            // any later highlighting patterns that also match this node.
            while let Some((next_match, capture_index)) = self.captures.peek() {
                if next_match.captures[*capture_index].node == capture.node {
                    self.captures.next();
                } else {
                    break;
                }
            }

            let current_highlight = self.config.highlight_indices[capture.index as usize];

            if let Some(definition_highlight) = definition_highlight {
                *definition_highlight = current_highlight;
            }

            if let Some(highlight) = reference_highlight.or(current_highlight) {
                self.highlight_end_stack.push(range.end);
                return self
                    .emit_event(range.start, Some(HighlightEvent::HighlightStart(highlight)));
            }
        }
    }
}

pub struct HtmlRenderer {
    pub html: Vec<u8>,
    pub line_offsets: Vec<u32>,
}

impl HtmlRenderer {
    pub fn new() -> Self {
        HtmlRenderer {
            html: Vec::new(),
            line_offsets: vec![0],
        }
    }

    pub fn reset(&mut self) {
        self.html.clear();
        self.line_offsets.clear();
        self.line_offsets.push(0);
    }

    pub fn render<'a, F>(
        &mut self,
        highlighter: impl Iterator<Item = Result<HighlightEvent, Error>>,
        source: &'a [u8],
        attribute_callback: &F,
    ) -> Result<(), Error>
    where
        F: Fn(Highlight) -> &'a [u8],
    {
        let mut highlights = Vec::new();
        for event in highlighter {
            match event {
                Ok(HighlightEvent::HighlightStart(s)) => {
                    highlights.push(s);
                    self.start_highlight(s, attribute_callback);
                }
                Ok(HighlightEvent::HighlightEnd) => {
                    highlights.pop();
                    self.end_highlight();
                }
                Ok(HighlightEvent::Source { start, end }) => {
                    self.add_text(&source[start..end], &highlights, attribute_callback);
                }
                Err(a) => return Err(a),
            }
        }
        if self.html.last() != Some(&b'\n') {
            self.html.push(b'\n');
        }
        if self.line_offsets.last() == Some(&(self.html.len() as u32)) {
            self.line_offsets.pop();
        }
        Ok(())
    }

    pub fn lines(&self) -> impl Iterator<Item = &str> {
        self.line_offsets
            .iter()
            .enumerate()
            .map(move |(i, line_start)| {
                let line_start = *line_start as usize;
                let line_end = if i + 1 == self.line_offsets.len() {
                    self.html.len()
                } else {
                    self.line_offsets[i + 1] as usize
                };
                str::from_utf8(&self.html[line_start..line_end]).unwrap()
            })
    }

    fn start_highlight<'a, F>(&mut self, h: Highlight, attribute_callback: &F)
    where
        F: Fn(Highlight) -> &'a [u8],
    {
        let attribute_string = (attribute_callback)(h);
        self.html.extend(b"<span");
        if !attribute_string.is_empty() {
            self.html.extend(b" ");
            self.html.extend(attribute_string);
        }
        self.html.extend(b">");
    }

    fn end_highlight(&mut self) {
        self.html.extend(b"</span>");
    }

    fn add_text<'a, F>(&mut self, src: &[u8], highlights: &Vec<Highlight>, attribute_callback: &F)
    where
        F: Fn(Highlight) -> &'a [u8],
    {
        for c in util::LossyUtf8::new(src).flat_map(|p| p.bytes()) {
            if c == b'\n' {
                if self.html.ends_with(b"\r") {
                    self.html.pop();
                }
                highlights.iter().for_each(|_| self.end_highlight());
                self.html.push(c);
                self.line_offsets.push(self.html.len() as u32);
                highlights
                    .iter()
                    .for_each(|scope| self.start_highlight(*scope, attribute_callback));
            } else if let Some(escape) = util::html_escape(c) {
                self.html.extend_from_slice(escape);
            } else {
                self.html.push(c);
            }
        }
    }
}
