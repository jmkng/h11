#![allow(warnings)]

use std::collections::HashMap;
use std::str::FromStr;

const CONTENT_LENGTH: &str = "Content-Length";
const TRANSFER_ENCODING: &str = "Transfer-Encoding";

/// HTTP method.
/// Parse one from a string with respect to RFC9112 by using
/// [FromStr].
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

pub enum MethodError {
    UnsupportedMethod,
}

impl From<MethodError> for ReadError {
    fn from(value: MethodError) -> Self {
        match value {
            MethodError::UnsupportedMethod => Self::RequestLineUnsupportedMethod,
        }
    }
}

impl FromStr for Method {
    type Err = MethodError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "GET" => Ok(Method::GET),
            "POST" => Ok(Method::POST),
            "PUT" => Ok(Method::PUT),
            "PATCH" => Ok(Method::PATCH),
            "DELETE" => Ok(Method::DELETE),
            "HEAD" => Ok(Method::HEAD),
            "OPTIONS" => Ok(Method::OPTIONS),
            "CONNECT" => Ok(Method::CONNECT),
            "TRACE" => Ok(Method::TRACE),
            _ => Err(MethodError::UnsupportedMethod),
        }
    }
}

pub struct Request {
    pub method: Method,
    pub path: String,
    pub version: String,
    pub body: Option<String>,
}

#[derive(Debug)]
enum RequestState {
    Line,
    /// Builder is reading the request headers.
    /// Contains the length of the headers so far.
    Headers(usize),
    /// Builder is reading the request body.
    /// Contains the length of the body so far.
    Body(usize),
    Done,
}

/// Request line target.
/// Enforces no whitespace in the internal string.
pub struct Target(String);

pub enum TargetError {
    TargetContainsWhitespace,
}

impl Target {
    pub fn new(target: String) -> Result<Self, TargetError> {
        // "No whitespace is allowed in the request-target."
        //
        // https://datatracker.ietf.org/doc/html/rfc9112#section-3.2-3
        if target.contains(|p: char| p.is_whitespace()) {
            return Err(TargetError::TargetContainsWhitespace);
        }
        Ok(Self(target))
    }
}

impl From<TargetError> for ReadError {
    fn from(value: TargetError) -> Self {
        match value {
            TargetError::TargetContainsWhitespace => ReadError::MalformedRequestLine,
        }
    }
}

enum TransferCoding {
    Chunked,
}

impl FromStr for TransferCoding {
    type Err = ReadError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // "All transfer-coding names are case-insensitive"
        //
        // https://datatracker.ietf.org/doc/html/rfc9112#section-7-2
        if s.eq_ignore_ascii_case("chunked") {
            return Ok(TransferCoding::Chunked);
        }
        Err(ReadError::UnsupportedTransferCoding)
    }
}

enum BodyState {
    ContentLength(usize),
    TransferEncoding(TransferCoding),
    None,
}

pub struct RequestBuilder {
    /* State */
    /// Buffer to store bytes until at least one full line
    /// is available to be processed.
    buffer: Vec<u8>,
    /// Internal state.
    /// Decides what to do with bytes in buffer.
    request_state: RequestState,
    /// Determines how the request body, if any, will be handled.
    /// Set while parsing headers.
    body_state: BodyState,
    /// True if the "Host" header has been seen.
    has_host_header: bool,
    /// Prescribed buffer size for the reader.
    /// You may override this after creating the initial builder to set
    /// a default size,
    /// and then choose to resize the read buffer as this value is changed
    /// by calls to [RequestBuilder::read_data].
    pub read_buffer_size: usize,
    /// Request line HTTP method.
    method: Option<Method>,
    /// Request line target.
    target: Option<Target>,
    /// Request line HTTP version.
    version: Option<String>,
    /// Parsed HTTP headers.
    headers: HashMap<String, String>,

    /* Maximums */
    /// Maximum length of a single line in bytes.
    /// Default: 8 KiB
    max_line_len_bytes: usize,
    /// Maximum length of the request headers in bytes.
    /// Default: 64 KiB
    max_headers_len_bytes: usize,
    /// Maximum length of the request body in bytes.
    /// Default: 2 MiB
    max_body_len_bytes: usize,
}

impl Default for RequestBuilder {
    fn default() -> Self {
        Self {
            request_state: RequestState::Line,
            buffer: Default::default(),
            body_state: BodyState::None,
            has_host_header: false,
            max_line_len_bytes: 8 * 1024,
            max_headers_len_bytes: 64 * 1024,
            max_body_len_bytes: 2 * 1024 * 1024,
            read_buffer_size: 1024,
            method: None,
            target: None,
            version: None,
            headers: Default::default(),
        }
    }
}

// GET /path/to/resource HTTP/1.1\r\n
// Host: example.com\r\n
// User-Agent: curl/8.0\r\n
// \r\n
// <body...>

#[derive(Debug)]
pub enum ReadResult {
    NeedMoreData,
    Done,
}

#[derive(Debug)]
pub enum ReadError {
    MalformedRequestLine,
    MalformedHeader,
    ReceivedNonAsciiBytes,
    FoundWhitespaceBetweenRequestLineAndFirstHeader,
    RequestLineUnsupportedMethod,
    MissingHostHeader,
    ExceededMaxLineLen,
    ExceededMaxHeadersLen,
    ExceededMaxBodyLen,
    RequestContainsBareCR,
    UnsupportedTransferCoding,
    /// Returned when the [RequestBuilder] has completed the request,
    /// yet more bytes are being fed in.
    Done,
}

// TODO: A server that receives a request-target longer than any URI it wishes to
// parse MUST respond with a 414 (URI Too Long) status code

impl RequestBuilder {
    pub fn read_buffer_size(&self) -> usize {
        // TODO: This can change when we know the length of the body.
        self.read_buffer_size
    }

    pub fn read_data(&mut self, data: &[u8]) -> Result<ReadResult, ReadError> {
        if matches!(self.request_state, RequestState::Done) {
            return Err(ReadError::Done);
        }

        // "A recipient MUST parse an HTTP message ... in an encoding that is a superset
        // of US-ASCII. Parsing an HTTP message as a stream of Unicode characters ...
        // creates security vulnerabilities."
        //
        // https://datatracker.ietf.org/doc/html/rfc9112#section-2.2-2
        if !data.is_ascii() {
            return Err(ReadError::ReceivedNonAsciiBytes);
        }

        // Length checks.
        if self.buffer.len() + data.len() > self.max_line_len_bytes {
            return Err(ReadError::ExceededMaxLineLen);
        }
        #[rustfmt::skip]
        let state_limit = match self.request_state {
            RequestState::Headers(current_headers_len) => Some((current_headers_len, self.max_headers_len_bytes, ReadError::ExceededMaxHeadersLen)),
            RequestState::Body(current_body_len) => Some((current_body_len, self.max_body_len_bytes, ReadError::ExceededMaxBodyLen)),
            _ => None,
        };
        if let Some((current_len, max_len, err)) = state_limit {
            if current_len + data.len() > max_len {
                return Err(err);
            }
        }

        self.buffer.reserve(data.len());

        // Extend buffer.
        // Watch for bare CR.
        //
        // "A sender MUST NOT generate a bare CR (a CR character not immediately followed by LF)
        // within any protocol elements other than the content."
        //
        // https://datatracker.ietf.org/doc/html/rfc9112#section-2.2-4
        for (i, &byte) in data.iter().enumerate() {
            if byte == b'\r' {
                match data.get(i + 1) {
                    Some(&b'\n') => {} // Ok -— CRLF.
                    _ => return Err(ReadError::RequestContainsBareCR),
                }
            }
            self.buffer.push(byte);
        }

        // Process all available buffer lines.
        while let Some(index_pos_of_next_cr) = self.has_line() {
            let line = self.take_line_from_index(index_pos_of_next_cr);
            debug_assert!(!line.as_str().starts_with("\r\n"));

            self.request_state = match self.request_state {
                RequestState::Line => self.parse_request_line(line)?,
                RequestState::Headers(headers_len) => self.read_header(line, headers_len)?,
                RequestState::Body(body_len) => self.try_read_body()?,
                RequestState::Done => unreachable!(), // Handled at start of `read_data` above.
            }
        }

        Ok(ReadResult::NeedMoreData)
    }

    fn parse_request_line(&mut self, line: String) -> Result<RequestState, ReadError> {
        // "In the interest of robustness,
        // a server that is expecting to receive and parse a request-line SHOULD ignore
        // at least one empty line (CRLF) received prior to the request-line."
        //
        // https://datatracker.ietf.org/doc/html/rfc9112#section-2.2-6
        //
        if line.is_empty() {
            // TODO: Limit to one skip only?
            return Ok(RequestState::Line);
        }

        // Parse the line.
        // Do not use `split_whitespace` or similar because that splits on
        // "any amount" of whitespace, which is allowed by the spec but can be a security vulnerability.
        // See test `strict_request_line_whitespace` for details.
        let parts: Vec<&str> = line.split(|p: char| p.is_ascii_whitespace()).collect();
        if parts.len() == 3 {
            // TODO: Validate these parts.
            self.method = Some(FromStr::from_str(parts[0])?);
            self.target = Some(Target::new(parts[1].to_string())?); // TODO: Arena
            self.version = Some(parts[2].to_string());
            Ok(RequestState::Headers(0))
        } else {
            Err(ReadError::MalformedRequestLine)
        }
    }

    #[rustfmt::skip]
    fn read_header(&mut self, line: String, current_headers_len: usize) -> Result<RequestState, ReadError> {
        if line.is_empty() {
            // At this point, no more headers will be read.
            // This is a good time to enforce certain requirements, such as:
            //
            // 1. "A client MUST send a Host header field in all HTTP/1.1 request messages."
            //
            //    https://datatracker.ietf.org/doc/html/rfc9112#section-3.2-5
            if !self.has_host_header {
                return Err(ReadError::MissingHostHeader);
            }

            // TODO: Authority of request line target (if any) must match Host ^.
            //
            // https://datatracker.ietf.org/doc/html/rfc9112#section-3.2-5
            // https://datatracker.ietf.org/doc/html/rfc9112#section-3.2-6

            // TODO: Set read buffer size according to Content-Length.
            return match self.body_state {
                BodyState::None => Ok(RequestState::Done),
                _ => Ok(RequestState::Body(0)),
            };
        }

        // A recipient that receives whitespace between the start-line and the first header
        // field MUST either reject the message ...
        //
        // https://datatracker.ietf.org/doc/html/rfc9112#section-2.2-8
        //
        // The spec describes a way to handle this,
        // but lets just reject it for now.
        if self.headers.is_empty() && line.trim_ascii_start().len() != line.len() {
            return Err(ReadError::FoundWhitespaceBetweenRequestLineAndFirstHeader);
        }

        let mut split_iter = line.split(|p| p == ':');
        let name = split_iter.next();
        let value = split_iter.next();
        if split_iter.next().is_some() || name.is_none() || value.is_none() {
            return Err(ReadError::MalformedHeader);
        }
        let name = name.unwrap().trim(); // Trim whitespace for name/value here.
        let value = value.unwrap().trim();


        // Check for significant headers.
        if name.eq_ignore_ascii_case(CONTENT_LENGTH) {
            let content_length: usize = value.parse().map_err(|err| ReadError::MalformedHeader)?;
            self.body_state = BodyState::ContentLength(content_length)
        } else if name.eq_ignore_ascii_case(TRANSFER_ENCODING) {
            self.body_state = BodyState::TransferEncoding(FromStr::from_str(value)?)
        }
        if name.eq_ignore_ascii_case("host") {
            self.has_host_header = true;
        }

        // Insert the header.
        if self
            .headers
            .insert(name.to_string(), value.to_string())
            .is_some()
        {
            // TODO
            todo!("handle duplicate headers");
        }

        Ok(RequestState::Headers(current_headers_len + line.len()))
    }

    fn try_read_body(&mut self) -> Result<RequestState, ReadError> {
        todo!();
    }

    /// Return the index of the first occurance of "\r\n" in buffer, if any.
    /// Does not take the line -- to take it, use [RequestBuilder::take_line] instead.
    fn has_line(&self) -> Option<usize> {
        if let Some(index_pos_of_next_cr) = self.buffer.windows(2).position(|w| w == b"\r\n") {
            return Some(index_pos_of_next_cr);
        }
        None
    }

    fn take_line_from_index(&mut self, index_pos_of_next_cr: usize) -> String {
        // TODO: "Although the line terminator for the start-line and fields is the sequence CRLF,
        // a recipient MAY recognize a single LF as a line terminator and ignore any preceding CR."
        // https://datatracker.ietf.org/doc/html/rfc9112#section-2.2-3
        let line_bytes: Vec<u8> = self.buffer.drain(..index_pos_of_next_cr).collect();
        self.buffer.drain(..2); // Drain that CR too.

        // SAFETY: Method [RequestBuilder::read_data] will reject non-ascii bytes.
        let line = unsafe { std::str::from_utf8_unchecked(&line_bytes) }.to_string();
        line
    }

    /// Shortcut for [RequestBuilder::has_line] + [RequestBuilder::take_line_from_index].
    fn take_line(&mut self) -> Option<String> {
        if let Some(index_pos_of_next_cr) = self.has_line() {
            Some(self.take_line_from_index(index_pos_of_next_cr))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn buffer_take_line_behavior() {
        let mut request_builder = RequestBuilder::default();

        assert!(request_builder.has_line().is_none());
        request_builder.buffer = "\r\n".as_bytes().to_vec();
        let index = request_builder.has_line();
        assert!(index.is_some());
        assert!(
            request_builder
                .take_line_from_index(index.unwrap())
                .is_empty()
        );

        request_builder.buffer = concat!("Host: someone.somewhere.com", "\r\n")
            .as_bytes()
            .to_vec();
        assert!(
            request_builder
                .take_line()
                .is_some_and(|line| line.as_str() == "Host: someone.somewhere.com")
        );
        assert!(request_builder.buffer.is_empty());
    }

    #[test]
    fn parse_request_line() {
        let mut request_builder = RequestBuilder::default();

        let chunks = ["GET ", "/s", "omewhere ", "HTTP/1.1"];
        for (i, chunk) in chunks.iter().enumerate() {
            request_builder
                .read_data(chunk.as_bytes())
                .expect(&format!("Failed at chunk {}", i));
        }

        if !matches!(request_builder.request_state, RequestState::Line) {
            panic!("unexpected state: {:?}", request_builder.request_state);
        }

        assert!(request_builder.read_data(b"\r\n").is_ok());
        assert!(matches!(
            request_builder.request_state,
            RequestState::Headers(0)
        ));
    }

    #[test]
    fn parse_headers() {
        let mut request_builder = RequestBuilder::default();
        request_builder.request_state = RequestState::Headers(0);

        let chunks_1 = ["Content-Type", ":", "text/html\r\n"];
        let mut chunks_len = 0;
        for (i, chunk) in chunks_1.iter().enumerate() {
            chunks_len += chunk.len();
            request_builder
                .read_data(chunk.as_bytes())
                .expect(&format!("Failed at chunk {}", i));
        }

        if !matches!(
            request_builder.request_state,
            RequestState::Headers(chunks_len)
        ) {
            panic!("unexpected state: {:?}", request_builder.request_state);
        }

        assert!(request_builder.headers.len() == 1);
        assert!(
            request_builder
                .headers
                .get("Content-Type")
                .is_some_and(|value| value == "text/html")
        );

        /// Parser should ignore case.
        let chunks_2 = ["transfer-encoding", ":"];
        for (i, chunk) in chunks_2.iter().enumerate() {
            request_builder
                .read_data(chunk.as_bytes())
                .expect(&format!("Failed at chunk {}", i));
        }

        assert!(request_builder.headers.len() == 1);
        request_builder.read_data("chunked\r\n".as_bytes());
        assert!(request_builder.headers.len() == 2);
        assert!(
            request_builder
                .headers
                .get("transfer-encoding")
                .is_some_and(|value| value == "chunked")
        );
        assert!(request_builder.buffer.is_empty())
    }

    #[test]
    fn reject_whitespace_between_request_line_and_first_header() {
        let chunks = ["POST / HTTP/1.1\r\n", " Content-Type: application/json\r\n"];

        // Read request line.
        let mut request_builder = RequestBuilder::default();
        let chunk_zero = chunks.get(0).unwrap();
        let chunks_len = chunk_zero.len();
        assert!(request_builder.read_data(chunk_zero.as_bytes()).is_ok());
        assert!(matches!(
            request_builder.request_state,
            RequestState::Headers(chunks_len)
        ));

        // Read first header.
        // This should error due to the whitespace before the header name.
        let error = request_builder
            .read_data(chunks.get(1).unwrap().as_bytes())
            .unwrap_err();
        if !matches!(
            error,
            ReadError::FoundWhitespaceBetweenRequestLineAndFirstHeader
        ) {
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
        let mut request_builder = RequestBuilder::default();
        let should_be_err = request_builder.read_data(chunks.get(0).unwrap().as_bytes());
        assert!(should_be_err.is_err_and(|err| matches!(err, ReadError::MalformedRequestLine)));
    }

    #[test]
    fn reject_non_ascii_bytes() {
        let chunks = ["GET /abc/🤡/def HTTP/1.1"];
        let mut request_builder = RequestBuilder::default();
        assert!(
            request_builder
                .read_data(chunks.get(0).unwrap().as_bytes())
                .is_err_and(|err| matches!(err, ReadError::ReceivedNonAsciiBytes))
        );
    }

    #[test]
    fn reject_unsupported_method() {
        // "A server that receives a method longer than any that it implements
        // SHOULD respond with a 501 (Not Implemented) status code"
        // https://datatracker.ietf.org/doc/html/rfc9112#section-3-4
        let mut request_builder = RequestBuilder::default();
        let error = request_builder
            .read_data("POKE / HTTP/1.1\r\n".as_bytes())
            .unwrap_err();
        if !matches!(error, ReadError::RequestLineUnsupportedMethod) {
            panic!("unexpected error: {:?}", error);
        }
    }

    //#[test]
    //fn request_builder_trims_header_parts() {
    //    let mut request_builder = RequestBuilder::default();
    //    // TODO: Allowed by spec?
    //    request_builder.read_data("GET / HTTP/1.1\r\nA: B\r\nC : D  ".as_bytes())
    //}

    #[test]
    fn reject_request_without_host_header() {
        let mut request_builder = RequestBuilder::default();
        let error = request_builder
            .read_data("GET / HTTP/1.1\r\n\r\n".as_bytes())
            .unwrap_err();
        if !matches!(error, ReadError::MissingHostHeader) {
            panic!("unexpected error: {:?}", error);
        }
    }

    #[test]
    fn parse_content_length() {
        let mut request_builder = RequestBuilder::default();
        request_builder.request_state = RequestState::Headers(0);

        if let Err(error) = request_builder.read_data(format!("{}: 300\r\n", CONTENT_LENGTH).as_bytes())
        {
            panic!("unexpected error: {:?}", error);
        }
        assert!(matches!(
            request_builder.body_state,
            BodyState::ContentLength(300)
        ));
    }

    #[test]
    fn parse_transfer_encoding() {
        let mut request_builder = RequestBuilder::default();
        request_builder.request_state = RequestState::Headers(0);
        assert!(
            request_builder
                .read_data(format!("{}: chunked\r\n", TRANSFER_ENCODING).as_bytes())
                .is_ok()
        );
        assert!(matches!(
            request_builder.body_state,
            BodyState::TransferEncoding(TransferCoding::Chunked)
        ));
    }
}
