#![allow(warnings)]
mod server;

use header::*;
use std::{collections::HashMap, ops::Deref};

pub mod header {
    use std::borrow::Borrow;
    use std::hash::{Hash, Hasher};

    /// Case-insensitive comparison.
    pub fn eq<A, B>(a: &A, b: &B) -> bool
    where
        A: AsRef<[u8]> + ?Sized,
        B: AsRef<[u8]> + ?Sized,
    {
        a.as_ref().eq_ignore_ascii_case(b.as_ref())
    }

    pub const CONTENT_LENGTH: &str = "Content-Length";
    pub const TRANSFER_ENCODING: &str = "Transfer-Encoding";
    pub const HOST: &str = "Host";

    /// Header name.
    /// This type has case-insensitive [PartialEq] and [Hash] implementations.
    pub struct Name(pub String);

    impl PartialEq for Name {
        fn eq(&self, other: &Self) -> bool {
            self.0.eq_ignore_ascii_case(&other.0)
        }
    }

    impl Eq for Name {}

    impl Hash for Name {
        fn hash<H: Hasher>(&self, state: &mut H) {
            for b in self.0.bytes() {
                state.write_u8(b.to_ascii_lowercase());
            }
        }
    }

    impl Borrow<str> for Name {
        fn borrow(&self) -> &str {
            &self.0
        }
    }

    /// Header value.
    pub struct Value(pub String);

    #[cfg(test)]
    mod tests {
        use super::Name;
        use std::collections::HashMap;

        #[test]
        fn equal_keys_with_different_case_match() {
            let mut map = HashMap::new();
            map.insert(Name("Content-Type".into()), "json");

            assert_eq!(map.get(&Name("content-type".into())), Some(&"json"));
            assert_eq!(map.get(&Name("CONTENT-TYPE".into())), Some(&"json"));
        }

        #[test]
        fn different_header_names_do_not_collide() {
            let mut map = HashMap::new();
            map.insert(Name("Host".into()), "example.com");
            map.insert(Name("Accept".into()), "text/html");

            assert_eq!(map.get(&Name("host".into())), Some(&"example.com"));
            assert_eq!(map.get(&Name("accept".into())), Some(&"text/html"));
        }

        #[test]
        fn overwriting_value_uses_case_insensitive_match() {
            let mut map = HashMap::new();
            map.insert(Name("Host".into()), "one");
            map.insert(Name("HOST".into()), "two");

            // Expected behavior, although the [Parser] will generally check for existing keys
            // and append the new value instead.
            assert_eq!(map.len(), 1);
            assert_eq!(map.get(&Name("host".into())), Some(&"two"));
        }
    }
}

/// HTTP method.
/// Parse one from a string with respect to RFC9112 by using
/// [FromStr].
#[derive(Debug)]
pub enum Method {
    GET,
    POST,
    PUT,
    PATCH,
    DELETE,
    HEAD,
    OPTIONS,
    CONNECT,
    TRACE,
}

#[derive(Debug)]
pub enum MethodError {
    UnsupportedMethod,
}

impl From<MethodError> for Error {
    fn from(value: MethodError) -> Self {
        match value {
            MethodError::UnsupportedMethod => Self::UnsupportedMethod,
        }
    }
}

impl TryFrom<&[u8]> for Method {
    type Error = MethodError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        match value {
            b"GET" => Ok(Method::GET),
            b"POST" => Ok(Method::POST),
            b"PUT" => Ok(Method::PUT),
            b"PATCH" => Ok(Method::PATCH),
            b"DELETE" => Ok(Method::DELETE),
            b"HEAD" => Ok(Method::HEAD),
            b"OPTIONS" => Ok(Method::OPTIONS),
            b"CONNECT" => Ok(Method::CONNECT),
            b"TRACE" => Ok(Method::TRACE),
            _ => Err(MethodError::UnsupportedMethod),
        }
    }
}

#[derive(Debug)]
pub enum Version {
    HTTP11,
}

pub enum VersionError {
    UnsupportedVersion,
}

impl TryFrom<&[u8]> for Version {
    type Error = VersionError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        match value {
            b"HTTP/1.1" => Ok(Self::HTTP11),
            _ => Err(VersionError::UnsupportedVersion),
        }
    }
}

impl From<VersionError> for Error {
    fn from(value: VersionError) -> Self {
        match value {
            VersionError::UnsupportedVersion => Self::UnsupportedVersion,
        }
    }
}

/// Builder state.
/// This describes how the builder will apply received bytes.
#[derive(Debug)]
pub enum State {
    /// Reading the request line.
    Line,
    /// Reading the request headers.
    Headers,
    /// No additional headers are expected.
    /// Additional data received while in this state will cause an error.
    Done,
}

/// Request line target.
/// Enforces no whitespace in the internal bytes.
///
/// "No whitespace is allowed in the request-target."
///
/// https://datatracker.ietf.org/doc/html/rfc9112#section-3.2-3
#[derive(Default, Debug)]
pub struct Target(String);

pub enum TargetError {
    TargetContainsWhitespace,
}

impl From<TargetError> for Error {
    fn from(value: TargetError) -> Self {
        match value {
            TargetError::TargetContainsWhitespace => Error::MalformedRequestLine,
        }
    }
}
pub enum TransferCodingError {
    UnrecognizedTransferCoding,
}

impl From<TransferCodingError> for Error {
    fn from(value: TransferCodingError) -> Self {
        match value {
            TransferCodingError::UnrecognizedTransferCoding => Error::UnsupportedTransferCoding,
        }
    }
}

pub struct RequestLine {
    /// Request line method.
    method: Method,
    /// Request line target URI.
    target: Target,
    /// Request line version.
    version: Version,
}

impl Default for RequestLine {
    fn default() -> Self {
        Self {
            method: Method::HEAD,
            target: Target(String::new()),
            version: Version::HTTP11,
        }
    }
}

/// Header storage.
/// Some well known headers have dedicated fields within this type.
/// All others are stored in [Headers::other].
#[derive(Default)]
pub struct Headers {
    /// Host header.
    ///
    /// https://developer.mozilla.org/en-US/docs/Web/HTTP/Reference/Headers/Host
    host: Option<String>,
    /// Transfer encoding.
    ///
    /// https://developer.mozilla.org/en-US/docs/Web/HTTP/Reference/Headers/Transfer-Encoding
    transfer_encoding: Vec<String>,
    /// Content length.
    ///
    /// https://developer.mozilla.org/en-US/docs/Web/HTTP/Reference/Headers/Content-Length
    content_length: Option<i64>,

    /// All other headers are stored here.
    /// TODO: Ensure all lookups are case-insensitive.
    pub other: HashMap<header::Name, Vec<header::Value>>,
}

/// A fully formed request header containing the request line and headers.
/// Provides additional methods to interact with the request body.
pub struct Request {
    request_line: RequestLine,
    headers: Headers,
}

impl TryFrom<Parser> for Request {
    type Error = ();

    fn try_from(value: Parser) -> Result<Self, Self::Error> {
        if !matches!(value.state, State::Done) {
            return Err(());
        }
        Ok(Self {
            request_line: value.request_line.unwrap(),
            headers: value.headers,
        })
    }
}

/// Represents the next expected action.
/// The parser will continue taking bytes until the request line
/// and all headers have been read,
/// at which point it will return [Next::Done], which may contain a portion of the request body.
/// The caller may want to produce some object that contains this data,
/// and then expose additional methods to continue reading the request body.
#[derive(Debug)]
pub enum Next {
    /// The parser expects to receive more data.
    Receive,
    /// The request line and headers have been read.
    /// The [Vec<u8>] contains any portion of the body that was read into the parser.
    Done(Vec<u8>),
}

/// Fatal errors.
/// The [Parser] cannot be recovered after it has returned an error.
#[derive(Debug, Clone)]
pub enum Error {
    ReceivedNonAsciiBytes,
    RequestContainsBareCR,
    MalformedRequestLine,
    FoundWhitespaceBeforeFirstHeader,
    UnsupportedMethod,
    UnsupportedVersion,
    MalformedHeader,
    MissingHost,
    MultipleHostHeaders,
    UnsupportedTransferCoding,
    /// Returned when the parser has finished parsing headers,
    /// but more data has been received.
    ///
    /// You should observe the [Next::Done] action,
    /// take the overflow bytes contained within,
    /// and proceed to read the request body yourself.
    Done,
}

pub struct Parser {
    /// Request bytes.
    /// All data received by [Parser::read_bytes] is stored here
    data: Vec<u8>,
    /// Position of the next unparsed byte in [Parser::data].
    /// if a caller uses [Parser::read_data] with a line that does not end
    /// in "\r\n", the data is not immediately parsed.
    pos: usize,
    /// Current state of the parser.
    state: State,
    request_line: Option<RequestLine>,
    headers: Headers,
    /// If the [Parser] returns an error,
    /// all further calls to parser methods return that same error.
    error: Option<Error>,
}

impl Default for Parser {
    fn default() -> Self {
        Self {
            data: Vec::new(),
            pos: 0,
            state: State::Line,
            error: None,
            request_line: None,
            headers: Headers::default(),
        }
    }
}

// TODO: A server that receives a request-target longer than any URI it wishes to
// parse MUST respond with a 414 (URI Too Long) status code

// GET /path/to/resource HTTP/1.1\r\n
// Host: example.com\r\n
// User-Agent: curl/8.0\r\n
// \r\n
// <body...>

impl Parser {
    /// Read data into this request.
    /// Returns the number of bytes consumed from `data` and the new builder state.
    pub fn read_data(&mut self, data: &[u8]) -> Result<Next, Error> {
        // If the system previously returned an error,
        // the state of the connection cannot be advanced further.
        // Continue to return the error.
        if let Some(error) = &self.error {
            return Err(error.clone());
        }

        match self.state {
            State::Done => return Err(Error::Done),
            _ => {}
        }

        // "A recipient MUST parse an HTTP message ... in an encoding that is a superset
        // of US-ASCII. Parsing an HTTP message as a stream of Unicode characters ...
        // creates security vulnerabilities."
        //
        // https://datatracker.ietf.org/doc/html/rfc9112#section-2.2-2
        if !data.is_ascii() {
            return Err(Error::ReceivedNonAsciiBytes);
        }

        self.data.extend_from_slice(data);
        let mut lines = Lines(&self.data[self.pos..]);

        // Destructure state.
        // ------------------------------------------------------------------------->>
        let mut request_line = std::mem::take(&mut self.request_line).unwrap_or_default();
        let mut headers = std::mem::take(&mut self.headers);
        // --------------------------------------------------------------------|

        while let Some(line) = lines.next() {
            let line = line?;
            self.pos += line.len();
            let result = match self.state {
                State::Line => self.parse_request_line(line, &mut request_line),
                State::Headers => self.parse_header(line, &mut headers),
                _ => unreachable!(), // Checked above.
            };
            match result {
                Ok(state) => {
                    self.state = state;
                }
                Err(error) => {
                    self.error = Some(error.clone());
                    return Err(error);
                }
            }
        }

        // Restructure state.
        // ------------------------------------------------------------------------<<^
        self.request_line = Some(request_line);
        self.headers = headers;
        // ------------------------------------|

        match self.state {
            // Parser is now finished.
            // The user will be delivered any "overflow" bytes so the request body can be
            // read lazily.
            State::Done => {
                let remaining = self.data[self.pos..].to_vec();
                Ok(Next::Done(remaining))
            }
            _ => Ok(Next::Receive),
        }
    }

    /// Parse the request line.
    /// This function assumes that line is an entire line. It does not handle partial lines.
    /// The caller should store bytes until a full line is available to parse all at once.
    #[rustfmt::skip]
    fn parse_request_line(&self, line: Line, state: &mut RequestLine) -> Result<State, Error> {
        // "In the interest of robustness,
        // a server that is expecting to receive and parse a request-line SHOULD ignore
        // at least one empty line (CRLF) received prior to the request-line."
        //
        // https://datatracker.ietf.org/doc/html/rfc9112#section-2.2-6
        if line.is_empty() {
            // TODO: Limit to one skip only?
            return Ok(State::Line);
        }

        // Parse the line.
        // Do not use `split_whitespace` or similar because that splits on
        // "any amount" of whitespace, which is allowed by the spec but can be a security vulnerability.
        // See test `strict_request_line_whitespace` for details.
        let line_parts: [Range; 3] = split_request_line(&line)?;

        state.method = line[line_parts[0].start..line_parts[0].end].try_into()?;
        state.target = Target(unsafe { std::str::from_utf8_unchecked(&self.data[line_parts[1].start..line_parts[1].end]) }.to_string());
        state.version = line[line_parts[2].start..line_parts[2].end].try_into()?;
        Ok(State::Headers)
    }

    /// Parse a header line.
    /// This function assumes that line is an entire line. It does not handle partial lines.
    /// The caller should store bytes until a full line is available to parse all at once.
    fn parse_header(&self, line: Line, state: &mut Headers) -> Result<State, Error> {
        if line.is_empty() {
            // This line signals the end of the headers.
            // It is a good time to enforce certain requirements, such as:
            //
            // 1. "A client MUST send a Host header field in all HTTP/1.1 request messages."
            //    https://datatracker.ietf.org/doc/html/rfc9112#section-3.2-5
            if state.get(header::HOST).is_none() {
                return Err(Error::MissingHost);
            }
            // TODO: Authority of request line target (if any) must match Host ^.
            // https://datatracker.ietf.org/doc/html/rfc9112#section-3.2-5
            // https://datatracker.ietf.org/doc/html/rfc9112#section-3.2-6
            return Ok(State::Done);
        }

        // A recipient that receives whitespace between the start-line and the first header
        // field MUST either reject the message ...
        //
        // https://datatracker.ietf.org/doc/html/rfc9112#section-2.2-8
        //
        // The spec describes a way to handle this,
        // but lets just reject it for now.
        let line_len_with_cr = line.len_with_rn();
        if state.other.is_empty() && line.trim_ascii_start().len() != line_len_with_cr {
            return Err(Error::FoundWhitespaceBeforeFirstHeader);
        }

        let split = split_field_line(&line.0)?;
        let split_name = &line[split[0].start..split[0].end];
        let split_value = &line[split[1].start..split[1].end];

        // Check for significant headers.
        let s_unchecked =
            |bytes: &[u8]| unsafe { std::str::from_utf8_unchecked(bytes) }.to_string();
        let mut store_header = true;
        if header::eq(HOST, split_name) {
            // A server MUST respond with a 400 (Bad Request) status code to any HTTP/1.1 request
            // message that lacks a Host header field and to any request message that contains more
            // than one Host header field line or a Host header field with an invalid field value.
            //
            // https://www.rfc-editor.org/rfc/rfc9112.html#section-3.2-6
            if state.host.is_some() {
                return Err(Error::MultipleHostHeaders);
            }
            state.host = Some(s_unchecked(split_name));
            store_header = false;
        } else if header::eq(CONTENT_LENGTH, split_name) {
            let content_length: i64 = unsafe { std::str::from_utf8_unchecked(split_value) }
                .parse()
                .map_err(|_| Error::MalformedHeader)?;
            state.content_length = Some(content_length);
            store_header = false;
        } else if header::eq(TRANSFER_ENCODING, split_name) {
            state
                .transfer_encoding
                .push(unsafe { std::str::from_utf8_unchecked(split_value) }.to_string());
            store_header = false;
        }

        // All data is checked with is_ascii in read_data.
        if store_header {
            let name_str = unsafe { std::str::from_utf8_unchecked(split_name) };
            let value_str = unsafe { std::str::from_utf8_unchecked(split_value) };
            let name_owned = name_str.to_string();
            let value_owned = value_str.to_string();
            let name = header::Name(name_owned);
            let value = header::Value(value_owned);
            match state.other.entry(name) {
                std::collections::hash_map::Entry::Occupied(mut oe) => oe.get_mut().push(value),
                std::collections::hash_map::Entry::Vacant(ve) => {
                    ve.insert(vec![value]);
                }
            }
        }

        Ok(State::Headers)
    }
}

/// Returns true if `c` is a valid HTTP header field character (RFC 7230 tchar).
/// https://datatracker.ietf.org/doc/html/rfc9110#name-tokens
fn is_valid_header_field_byte(c: u8) -> bool {
    match c {
        b'0'..=b'9'
        | b'a'..=b'z'
        | b'A'..=b'Z'
        | b'!'
        | b'#'
        | b'$'
        | b'%'
        | b'&'
        | b'\''
        | b'*'
        | b'+'
        | b'-'
        | b'.'
        | b'^'
        | b'_'
        | b'`'
        | b'|'
        | b'~' => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::is_valid_header_field_byte;

    #[test]
    fn allowed_byte() {
        for &c in b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!#$%&'*+-.^_`|~" {
            assert!(
                is_valid_header_field_byte(c),
                "expected allowed: {}",
                c as char
            );
        }
    }

    #[test]
    fn disallowed_byte() {
        for &c in b" :()\r\n\t=," {
            assert!(
                !is_valid_header_field_byte(c),
                "expected disallowed: {}",
                c as char
            );
        }
        assert!(!is_valid_header_field_byte(200));
    }
}

#[cfg(test)]
mod request_line_parsing {
    use super::*;

    #[test]
    fn multi_chunk_request_line() {
        let mut request_builder = Parser::default();

        let chunks = ["GET ", "/s", "omewhere ", "HTTP/1.1"];
        for (i, chunk) in chunks.iter().enumerate() {
            request_builder
                .read_data(chunk.as_bytes())
                .expect(&format!("Failed at chunk {}", i));
        }

        if !matches!(request_builder.state, State::Line) {
            panic!("unexpected state: {:?}", request_builder.state);
        }

        if let Err(error) = request_builder.read_data(b"\r\n") {
            panic!("unexpect error: {:?}", error);
        }
        //assert!(request_builder.read_data(b"\r\n").is_ok());
        //assert!(matches!(request_builder.state, State::Headers));
    }
}

#[cfg(test)]
mod header_parsing {
    use super::*;

    // TODO: Test rejection of whitespace after header name but before :
    // TODO: Add tests for well known header handling

    #[test]
    fn parse_headers() {
        let mut parser = Parser::default();
        parser.state = State::Headers;

        let chunks_1 = ["Content-Type:", "text/html\r\n"];
        for (i, chunk) in chunks_1.iter().enumerate() {
            parser.read_data(chunk.as_bytes()).unwrap();
        }
        if !matches!(parser.state, State::Headers) {
            panic!("unexpected state: {:?}", parser.state);
        }
        assert!(parser.headers.other.len() == 1);

        let chunks_2 = [header::TRANSFER_ENCODING, ":"];
        for (i, chunk) in chunks_2.iter().enumerate() {
            parser.read_data(chunk.as_bytes()).unwrap();
        }
        parser.read_data("chunked\r\n".as_bytes()).unwrap();
        // Should still be 1 because TRANSFER_ENCODING is a "well known" header and does not go in the header map.
        assert!(parser.headers.other.len() == 1);
    }

    #[test]
    fn reject_whitespace_between_request_line_and_first_header() {
        let chunks = [
            "POST / HTTP/1.1\r\n",
            "    Content-Type: application/json\r\n",
        ];

        // Read request line.
        let mut parser = Parser::default();
        let chunk_zero = chunks.get(0).unwrap();
        assert!(parser.read_data(chunk_zero.as_bytes()).is_ok());
        assert!(matches!(parser.state, State::Headers));

        // Read first header.
        // This should error due to the whitespace before the header name.
        let error = parser
            .read_data(chunks.get(1).unwrap().as_bytes())
            .unwrap_err();
        if !matches!(error, Error::FoundWhitespaceBeforeFirstHeader) {
            panic!("unexpected error: {:?}", error);
        }
    }

    #[test]
    fn strict_request_line_whitespace() {
        // "Although the request-line grammar rule requires that each of the
        // component elements be separated by a single SP octet,
        // recipients MAY instead parse on whitespace-delimited word boundaries and,
        // aside from the CRLF terminator,
        // treat any form of whitespace as the SP separator ..."
        // "... However, lenient parsing can result in request smuggling security vulnerabilities"
        //
        // https://datatracker.ietf.org/doc/html/rfc9112#section-3-3
        let chunks = ["PATCH    /             HTTP/1.1\r\n"];
        let mut parser = Parser::default();
        let result = parser.read_data(chunks.get(0).unwrap().as_bytes());
        assert!(result.is_err_and(|err| matches!(err, Error::MalformedRequestLine)));
    }

    #[test]
    fn reject_non_ascii_bytes() {
        let chunks = ["GET /abc/🤡/def HTTP/1.1"];
        let mut parser = Parser::default();
        assert!(
            parser
                .read_data(chunks.get(0).unwrap().as_bytes())
                .is_err_and(|err| matches!(err, Error::ReceivedNonAsciiBytes))
        );
    }

    #[test]
    fn reject_unsupported_method() {
        // "A server that receives a method longer than any that it implements
        // SHOULD respond with a 501 (Not Implemented) status code"
        // https://datatracker.ietf.org/doc/html/rfc9112#section-3-4
        let mut parser = Parser::default();
        let error = parser
            .read_data("POKE / HTTP/1.1\r\n".as_bytes())
            .unwrap_err();
        if !matches!(error, Error::UnsupportedMethod) {
            panic!("unexpected error: {:?}", error);
        }
    }

    #[test]
    fn reject_request_without_host_header() {
        let mut parser = Parser::default();
        let error = parser
            .read_data("GET / HTTP/1.1\r\n\r\n".as_bytes())
            .unwrap_err();
        if !matches!(error, Error::MissingHost) {
            panic!("unexpected error: {:?}", error);
        }
    }

    #[test]
    fn parse_content_length() {
        let mut parser = Parser::default();
        parser.state = State::Headers;
        let h1 = format!("{}: 300\r\n", header::CONTENT_LENGTH);
        if let Err(error) = parser.read_data(h1.as_bytes()) {
            panic!("unexpected error: {:?}", error);
        }
        let Headers { content_length, .. } = parser.headers;
        assert_eq!(content_length, Some(300));
    }

    #[test]
    fn parse_transfer_encoding() {
        let mut parser = Parser::default();
        parser.state = State::Headers;
        let h1 = format!("{}: chunked\r\n", header::TRANSFER_ENCODING);
        assert!(parser.read_data(h1.as_bytes()).is_ok());
        assert!(
            parser
                .headers
                .transfer_encoding
                .iter()
                .any(|v| v == "chunked")
        );
    }
}

struct Lines<'data>(&'data [u8]);

impl<'data> Iterator for Lines<'data> {
    type Item = Result<Line<'data>, LineError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0.is_empty() {
            return None;
        }
        while let Some(pos) = self.0.iter().position(|&b| b == b'\r') {
            if pos + 1 < self.0.len() && self.0[pos + 1] == b'\n' {
                let line = &self.0[..pos];
                debug_assert!(!line.ends_with(b"\r\n"));
                self.0 = &self.0[pos + 2..];
                return Some(Ok(line.into()));
            } else {
                // "A sender MUST NOT generate a bare CR (a CR character not immediately followed by LF)
                // within any protocol elements other than the content."
                //
                // https://datatracker.ietf.org/doc/html/rfc9112#section-2.2-4
                return Some(Err(LineError::LineContainsBareCR));
            }
        }

        self.0 = &[];
        None
    }
}

/// This contains a slice of bytes representing a fully formed HTTP/1.1 line,
/// with the trailing \r\n NOT included.
#[derive(PartialEq, Debug)]
struct Line<'data>(&'data [u8]);

impl<'data> Line<'data> {
    /// Return the length of the line, including the \r\n.
    pub fn len_with_rn(&self) -> usize {
        return self.0.len();
    }

    /// Return the length of the line, not including \r\n.
    /// See [Line::len_with_rn].
    pub fn len(&self) -> usize {
        return self.0.len() + 2;
    }

    /// Return the line as &str.
    pub fn as_str(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(self.0) }
    }
}

impl<'data> Deref for Line<'data> {
    type Target = &'data [u8];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'data> From<&'data [u8]> for Line<'data> {
    fn from(value: &'data [u8]) -> Self {
        Line(value)
    }
}

impl<'data, const N: usize> From<&'data [u8; N]> for Line<'data> {
    fn from(value: &'data [u8; N]) -> Self {
        Line(&value[..])
    }
}

#[derive(PartialEq, Debug)]
pub enum LineError {
    LineContainsBareCR,
}

impl From<LineError> for Error {
    fn from(value: LineError) -> Self {
        match value {
            LineError::LineContainsBareCR => Error::RequestContainsBareCR,
        }
    }
}

#[cfg(test)]
mod lines_iterator_tests {
    use super::*;

    #[test]
    fn trailing_newline() {
        let data = b"foo\r\nbar\r\n";
        let mut lines = Lines(data);
        assert_eq!(lines.next(), Some(Ok(b"foo".into())));
        assert_eq!(lines.next(), Some(Ok(b"bar".into())));
        assert_eq!(lines.next(), None);
        assert_eq!(lines.next(), None);
    }

    #[test]
    fn no_trailing_newline() {
        let data = b"foo\r\nbar\r\nbaz";
        let mut lines = Lines(data);
        assert_eq!(lines.next(), Some(Ok(b"foo".into())));
        assert_eq!(lines.next(), Some(Ok(b"bar".into())));

        // "baz" doesn't count as a line yet.
        assert_eq!(lines.next(), None);
        assert_eq!(lines.next(), None);
    }

    #[test]
    fn empty_input() {
        let data = b"";
        let mut lines = Lines(data);
        assert_eq!(lines.next(), None);
        assert_eq!(lines.next(), None);
    }

    #[test]
    fn consecutive_crlf() {
        let data = b"foo\r\n\r\nbar";
        let mut lines = Lines(data);
        assert_eq!(lines.next(), Some(Ok(b"foo".into())));
        assert_eq!(lines.next(), Some(Ok(b"".into())));
        assert_eq!(lines.next(), None);
        assert_eq!(lines.next(), None);
    }

    #[test]
    fn lone_crs_should_error() {
        let data = b"foo\rbar\r\n";
        let mut lines = Lines(data);
        assert_eq!(lines.next(), Some(Err(LineError::LineContainsBareCR)));
        assert_eq!(lines.next(), Some(Err(LineError::LineContainsBareCR)));
    }

    #[test]
    fn starts_with_crlf() {
        let data = b"\r\nfoo\r\nbar";
        let mut lines = Lines(data);
        assert_eq!(lines.next(), Some(Ok(b"".into())));
        assert_eq!(lines.next(), Some(Ok(b"foo".into())));
        assert_eq!(lines.next(), None);
        assert_eq!(lines.next(), None);
    }

    #[test]
    fn multiple_trailing_crlf() {
        let data = b"foo\r\nbar\r\n\r\n";
        let mut lines = Lines(data);
        assert_eq!(lines.next(), Some(Ok(b"foo".into())));
        assert_eq!(lines.next(), Some(Ok(b"bar".into())));
        assert_eq!(lines.next(), Some(Ok(b"".into())));
        assert_eq!(lines.next(), None);
        assert_eq!(lines.next(), None);
    }

    #[test]
    fn only_crlf() {
        let data = b"\r\n";
        let mut lines = Lines(data);
        assert_eq!(lines.next(), Some(Ok(b"".into())));
        assert_eq!(lines.next(), None);
        assert_eq!(lines.next(), None);
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
struct Range {
    start: usize,
    end: usize,
}

impl Range {
    /// Return the length of the [Range],
    /// which is the difference of end-start.
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// The closure is applied to the start and end indexes.
    fn map<F: Fn(usize) -> usize>(self, f: F) -> Range {
        Range {
            start: f(self.start),
            end: f(self.end),
        }
    }
}

impl From<std::ops::Range<usize>> for Range {
    fn from(value: std::ops::Range<usize>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}

fn split_request_line(data: &[u8]) -> Result<[Range; 3], Error> {
    let mut start = 0;
    let mut num = 0;
    let mut result: [Range; 3] = std::array::from_fn(|_| (0..0).into());

    // GET / HTTP/1.1
    for (index, byte) in data.iter().enumerate() {
        if byte.is_ascii_whitespace() {
            if num == 3 {
                return Err(Error::MalformedRequestLine);
            }
            result[num] = (start..index).into();
            start = index + 1;
            num += 1;
        }
    }
    if num == 2 {
        result[num] = (start..data.len()).into();
    }

    Ok(result)
}

#[derive(Debug)]
enum FieldLineError {
    /// The field line contains whitespace in an invalid position.
    HasInvalidWhitespace,
    /// The provided byte slice does not contain a ':' byte.
    /// This error is also returned when data is empty (zero-length).
    HasNoSplitByte,
}

impl From<FieldLineError> for Error {
    fn from(value: FieldLineError) -> Self {
        match value {
            _ => Error::MalformedHeader,
        }
    }
}

/// field-line = field-name ":" OWS field-value OWS
fn split_field_line(data: &[u8]) -> Result<[Range; 2], FieldLineError> {
    let split_at_index = data
        .iter()
        .position(|&b| b == b':')
        .ok_or(FieldLineError::HasNoSplitByte)?;

    if data.get(0).unwrap().is_ascii_whitespace()
        || data.get(split_at_index - 1).unwrap().is_ascii_whitespace()
    {
        return Err(FieldLineError::HasInvalidWhitespace);
    }

    let mut result: [Range; 2] = std::array::from_fn(|_| (0..0).into());

    let name_start = 0;
    let name_end = split_at_index;

    // Find true value length (not including leading/trailing whitespace)
    let mut value_start = split_at_index + 1;
    let mut value_end = data.len();
    let value = &data[value_start..value_end];
    let value_len = value.len();
    if value.trim_ascii().len() > 0 {
        // If the value has non-whitespace characters,
        // ignore the whitespace on either side.
        value_start += value_len - value.trim_ascii_start().len();
        value_end -= value_len - value.trim_ascii_end().len();
    } else {
        // If the value is only whitespace,
        // ignore all of it.
        value_end = value_start;
    }

    result[0].start = name_start;
    result[0].end = name_end;
    result[1].start = value_start;
    result[1].end = value_end;

    Ok(result)
}

#[cfg(test)]
mod split_tests {
    use super::*;

    #[test]
    fn split_request_line_basic() -> () {
        let bytes = "GET /index.html HTTP/1.1".as_bytes();
        let result = split_request_line(bytes);
        if let Err(error) = result {
            panic!("unexpected error: {:?}", error);
        }
        let result = result.unwrap();

        let method = result[0];
        let target = result[1];
        let version = result[2];
        assert_eq!(method, Range { start: 0, end: 3 });
        assert_eq!(target, Range { start: 4, end: 15 });
        assert_eq!(version, Range { start: 16, end: 24 });
    }

    #[test]
    fn split_field_line_no_whitespace() -> () {
        let bytes = "Content-Length: 100".as_bytes();
        let result = split_field_line(bytes);

        if let Err(error) = result {
            panic!("unexpected error: {:?}", error);
        }

        let result = result.unwrap();
        assert_eq!(result[0], Range { start: 0, end: 14 });
        assert_eq!(result[1], Range { start: 16, end: 19 });
        #[rustfmt::skip]
        assert_eq!(&bytes[result[0].start..result[0].end], "Content-Length".as_bytes());
        assert_eq!(&bytes[result[1].start..result[1].end], "100".as_bytes());
    }

    #[test]
    fn split_field_empty_value() -> () {
        let bytes = "Blah:".as_bytes();
        let result = split_field_line(bytes);

        if let Err(error) = result {
            panic!("unexpected error: {:?}", error);
        }

        let result = result.unwrap();
        assert_eq!(result[0], Range { start: 0, end: 4 });
        assert_eq!(result[1], Range { start: 5, end: 5 });
        #[rustfmt::skip]
        assert_eq!(&bytes[result[0].start..result[0].end], "Blah".as_bytes());
        assert_eq!(&bytes[result[1].start..result[1].end], "".as_bytes());
    }

    #[test]
    fn split_field_empty_value_whitespace() -> () {
        let bytes = "Blah:\r\n".as_bytes();
        let result = split_field_line(bytes);

        if let Err(error) = result {
            panic!("unexpected error: {:?}", error);
        }

        let result = result.unwrap();

        assert_eq!(result[0], Range { start: 0, end: 4 });
        assert_eq!(result[1], Range { start: 5, end: 5 });
        #[rustfmt::skip]
        assert_eq!(&bytes[result[0].start..result[0].end], "Blah".as_bytes());
        assert_eq!(&bytes[result[1].start..result[1].end], "".as_bytes());
    }

    #[test]
    fn split_field_line_whitespace_before_name() -> () {
        let bytes = "   Content-Length: 100".as_bytes();
        let result = split_field_line(bytes);
        assert!(result.is_err());
    }

    #[test]
    fn split_field_line_whitespace_after_name() -> () {
        let bytes = "Content-Length\n: 100".as_bytes();
        let result = split_field_line(bytes);
        assert!(result.is_err());
    }
}
