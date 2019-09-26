pub mod c_lib;
pub mod util;
pub use c_lib as c;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::{iter, mem, ops, str, usize};
use tree_sitter::{Language, Node, Parser, Query, QueryCaptures, QueryCursor, QueryError, Tree};

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
    pub language: Language,
    pub query: Query,
    locals_pattern_index: usize,
    highlights_pattern_index: usize,
    highlight_indices: Vec<Option<Highlight>>,
    non_local_variable_patterns: Vec<bool>,
    injection_site_capture_index: Option<u32>,
    injection_content_capture_index: Option<u32>,
    injection_language_capture_index: Option<u32>,
    local_scope_capture_index: Option<u32>,
    local_def_capture_index: Option<u32>,
    local_ref_capture_index: Option<u32>,
}

#[derive(Clone, Debug)]
pub struct Highlighter {
    pub highlight_names: Vec<String>,
}

pub struct HighlightContext {
    parser: Parser,
    cursors: Vec<QueryCursor>,
}

struct HighlightIter<'a, F>
where
    F: Fn(&str) -> Option<&'a HighlightConfiguration> + 'a,
{
    source: &'a [u8],
    byte_offset: usize,
    context: &'a mut HighlightContext,
    injection_callback: F,
    cancellation_flag: Option<&'a AtomicUsize>,
    layers: Vec<HighlightIterLayer<'a>>,
    iter_count: usize,
    next_event: Option<HighlightEvent>,
}

struct HighlightIterLayer<'a> {
    _tree: Tree,
    cursor: QueryCursor,
    captures: iter::Peekable<QueryCaptures<'a>>,
    config: &'a HighlightConfiguration,
    highlight_end_stack: Vec<usize>,
    scope_stack: Vec<LocalScope<'a>>,
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

        let mut injection_content_capture_index = None;
        let mut injection_language_capture_index = None;
        let mut injection_site_capture_index = None;
        let mut local_def_capture_index = None;
        let mut local_ref_capture_index = None;
        let mut local_scope_capture_index = None;
        for (i, name) in query.capture_names().iter().enumerate() {
            let i = Some(i as u32);
            match name.as_str() {
                "injection.content" => injection_content_capture_index = i,
                "injection.language" => injection_language_capture_index = i,
                "injection.site" => injection_site_capture_index = i,
                "local.definition" => local_def_capture_index = i,
                "local.reference" => local_ref_capture_index = i,
                "local.scope" => local_scope_capture_index = i,
                _ => {}
            }
        }

        Ok(HighlightConfiguration {
            query,
            language,
            locals_pattern_index,
            highlights_pattern_index,
            highlight_indices,
            non_local_variable_patterns,
            injection_content_capture_index,
            injection_language_capture_index,
            injection_site_capture_index,
            local_def_capture_index,
            local_ref_capture_index,
            local_scope_capture_index,
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
        let layer = HighlightIterLayer::new(config, source, context, cancellation_flag, None)?;
        Ok(HighlightIter {
            source,
            byte_offset: 0,
            injection_callback,
            cancellation_flag,
            context,
            iter_count: 0,
            layers: vec![layer],
            next_event: None,
        })
    }
}

impl<'a> HighlightIterLayer<'a> {
    fn new(
        config: &'a HighlightConfiguration,
        source: &'a [u8],
        context: &mut HighlightContext,
        cancellation_flag: Option<&'a AtomicUsize>,
        parent_nodes: Option<&[Node<'a>]>,
    ) -> Result<Self, Error> {
        context
            .parser
            .set_language(config.language)
            .map_err(|_| Error::InvalidLanguage)?;
        unsafe { context.parser.set_cancellation_flag(cancellation_flag) };

        if let Some(parent_nodes) = parent_nodes {
            let ranges = parent_nodes.iter().map(|n| n.range()).collect::<Vec<_>>();
            context.parser.set_included_ranges(&ranges);
        }

        let tree = context.parser.parse(source, None).ok_or(Error::Cancelled)?;
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

        Ok(HighlightIterLayer {
            highlight_end_stack: Vec::new(),
            scope_stack: vec![LocalScope {
                inherits: false,
                range: 0..usize::MAX,
                local_defs: Vec::new(),
            }],
            cursor,
            _tree: tree,
            captures,
            config,
        })
    }

    fn offset(&mut self) -> Option<usize> {
        let next_start = self
            .captures
            .peek()
            .map(|(m, i)| m.captures[*i].node.start_byte());
        let next_end = self.highlight_end_stack.last().cloned();
        match (next_start, next_end) {
            (Some(i), Some(j)) => Some(usize::min(i, j)),
            (Some(i), None) => Some(i),
            (None, Some(j)) => Some(j),
            _ => None,
        }
    }
}

impl<'a, F> HighlightIter<'a, F>
where
    F: Fn(&str) -> Option<&'a HighlightConfiguration> + 'a,
{
    fn emit_event(
        &mut self,
        offset: usize,
        event: Option<HighlightEvent>,
    ) -> Option<Result<HighlightEvent, Error>> {
        let result;
        if self.byte_offset < offset {
            result = Some(Ok(HighlightEvent::Source {
                start: self.byte_offset,
                end: offset,
            }));
            self.byte_offset = offset;
            self.next_event = event;
        } else {
            result = event.map(Ok);
        }
        self.sort_layers();
        result
    }

    fn sort_layers(&mut self) {
        if let Some(offset) = self.layers[0].offset() {
            let mut i = 0;
            while i + 1 < self.layers.len() {
                if let Some(next_offset) = self.layers[i + 1].offset() {
                    if next_offset < offset {
                        i += 1;
                        continue;
                    }
                }
                break;
            }
            if i > 0 {
                &self.layers[0..(i + 1)].rotate_left(i);
            }
        } else {
            let layer = self.layers.remove(0);
            self.context.cursors.push(layer.cursor);
        }
    }
}

impl<'a, F> Iterator for HighlightIter<'a, F>
where
    F: Fn(&str) -> Option<&'a HighlightConfiguration> + 'a,
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

        // Consume captures until one provides a highlight.
        'main_loop: loop {
            if let Some(e) = self.next_event.take() {
                return Some(Ok(e));
            }

            if self.layers.is_empty() {
                return None;
            }

            let layer = &mut self.layers[0];

            // Get the next capture. If there are no more, then emit the rest of the
            // source code.
            let (mut match_, capture_index) = if let Some(c) = layer.captures.peek() {
                c.clone()
            } else if let Some(end_byte) = layer.highlight_end_stack.last().cloned() {
                layer.highlight_end_stack.pop();
                return self.emit_event(end_byte, Some(HighlightEvent::HighlightEnd));
            } else {
                return self.emit_event(self.source.len(), None);
            };
            let mut capture = match_.captures[capture_index];

            // If any previous highlight ends before this node starts, then before
            // processing this capture, emit the source code up until the end of the
            // previous highlight, and an end event for that highlight.
            let range = capture.node.byte_range();
            if let Some(end_byte) = layer.highlight_end_stack.last().cloned() {
                if end_byte <= range.start {
                    layer.highlight_end_stack.pop();
                    return self.emit_event(end_byte, Some(HighlightEvent::HighlightEnd));
                }
            }
            layer.captures.next();

            // Remove from the scope stack any local scopes that have already ended.
            while range.start > layer.scope_stack.last().unwrap().range.end {
                layer.scope_stack.pop();
            }

            let content_capture_index = layer.config.injection_content_capture_index;
            let language_capture_index = layer.config.injection_language_capture_index;
            let site_capture_index = layer.config.injection_site_capture_index;

            // Process any injections for this node.
            if match_.pattern_index < layer.config.locals_pattern_index {
                let mut injection_site = None;
                let mut injection_language = None;
                let mut injection_contents = Vec::new();
                for capture in match_.captures {
                    let index = Some(capture.index);
                    if index == site_capture_index {
                        injection_site = Some(capture.node);
                    } else if index == language_capture_index {
                        injection_language = capture.node.utf8_text(self.source).ok();
                    } else if index == content_capture_index {
                        injection_contents.push(capture.node);
                    }
                }

                if injection_language.is_none() {
                    injection_language = layer
                        .config
                        .query
                        .property_settings(match_.pattern_index)
                        .iter()
                        .find_map(|prop| {
                            if prop.key.as_ref() == "injection.language" {
                                prop.value.as_ref().map(|s| s.as_ref())
                            } else {
                                None
                            }
                        });
                }

                let pattern_index = match_.pattern_index;
                match_.remove();
                if let Some(injection_site) = injection_site {
                    while let Some((next_match, _)) = layer.captures.peek() {
                        if next_match.pattern_index == pattern_index
                            && next_match.captures.iter().any(|c| {
                                Some(c.index) == site_capture_index && c.node == injection_site
                            })
                        {
                            injection_contents.extend(next_match.captures.iter().filter_map(|c| {
                                if Some(c.index) == content_capture_index {
                                    Some(c.node)
                                } else {
                                    None
                                }
                            }));
                            layer.captures.next().unwrap().0.remove();
                            continue;
                        }
                        break;
                    }
                }

                if let Some(config) = injection_language.and_then(&self.injection_callback) {
                    if !injection_contents.is_empty() {
                        match HighlightIterLayer::new(
                            config,
                            self.source,
                            self.context,
                            self.cancellation_flag,
                            Some(&injection_contents),
                        ) {
                            Ok(layer) => self.layers.push(layer),
                            Err(e) => return Some(Err(e)),
                        }
                    }
                }

                self.sort_layers();
                continue 'main_loop;
            }

            // Process any local variable tracking patterns for this node.
            let mut reference_highlight = None;
            let mut definition_highlight = None;
            while match_.pattern_index < layer.config.highlights_pattern_index {
                // If the node represents a local scope, push a new local scope onto
                // the scope stack.
                if Some(capture.index) == layer.config.local_scope_capture_index {
                    definition_highlight = None;
                    layer.scope_stack.push(LocalScope {
                        inherits: true,
                        range: range.clone(),
                        local_defs: Vec::new(),
                    });
                }
                // If the node represents a definition, add a new definition to the
                // local scope at the top of the scope stack.
                else if Some(capture.index) == layer.config.local_def_capture_index {
                    reference_highlight = None;
                    definition_highlight = None;
                    let scope = layer.scope_stack.last_mut().unwrap();
                    if let Ok(name) = str::from_utf8(&self.source[range.clone()]) {
                        scope.local_defs.push((name, None));
                        definition_highlight = scope.local_defs.last_mut().map(|s| &mut s.1);
                    }
                }
                // If the node represents a reference, then try to find the corresponding
                // definition in the scope stack.
                else if Some(capture.index) == layer.config.local_ref_capture_index {
                    if definition_highlight.is_none() {
                        definition_highlight = None;
                        if let Ok(name) = str::from_utf8(&self.source[range.clone()]) {
                            for scope in layer.scope_stack.iter().rev() {
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
                if let Some((next_match, next_capture_index)) = layer.captures.peek() {
                    let next_capture = next_match.captures[*next_capture_index];
                    if next_capture.node == capture.node {
                        match_ = next_match.clone();
                        capture = next_capture;
                        layer.captures.next();
                        continue;
                    }
                }

                break;
            }

            // If the current node was found to be a local variable, then skip over any
            // highlighting patterns that are disabled for local variables.
            let mut has_highlight = true;
            while (definition_highlight.is_some() || reference_highlight.is_some())
                && layer.config.non_local_variable_patterns[match_.pattern_index]
            {
                has_highlight = false;
                if let Some((next_match, next_capture_index)) = layer.captures.peek() {
                    let next_capture = next_match.captures[*next_capture_index];
                    if next_capture.node == capture.node {
                        match_ = next_match.clone();
                        capture = next_capture;
                        has_highlight = true;
                        layer.captures.next();
                        continue;
                    }
                }
                break;
            }

            if has_highlight {
                // Once a highlighting pattern is found for the current node, skip over
                // any later highlighting patterns that also match this node.
                while let Some((next_match, capture_index)) = layer.captures.peek() {
                    if next_match.captures[*capture_index].node == capture.node {
                        layer.captures.next();
                    } else {
                        break;
                    }
                }

                let current_highlight = layer.config.highlight_indices[capture.index as usize];

                if let Some(definition_highlight) = definition_highlight {
                    *definition_highlight = current_highlight;
                }

                if let Some(highlight) = reference_highlight.or(current_highlight) {
                    layer.highlight_end_stack.push(range.end);
                    return self
                        .emit_event(range.start, Some(HighlightEvent::HighlightStart(highlight)));
                }
            }

            self.sort_layers();
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
