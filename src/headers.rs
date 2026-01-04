use std::borrow::Borrow;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::sync::LazyLock;

macro_rules! well_known {
    ($( $ident:ident => $value:expr ),* $(,)?) => {
        $(pub const $ident: &'static str = $value;)*
        static WELL_KNOWN_SET: LazyLock<HashSet<&'static str>> = LazyLock::new(|| {
            let mut set = HashSet::new();
            $(set.insert($ident);)*
            set
        });
    };
}

well_known! {
    ACCEPT => "Accept",
    ACCEPT_ENCODING => "Accept-Encoding",
    ACCEPT_LANGUAGE => "Accept-Language",
    ACCEPT_RANGES => "Accept-Ranges",
    ACCESS_CONTROL_ALLOW_CREDENTIALS => "Access-Control-Allow-Credentials",
    ACCESS_CONTROL_ALLOW_HEADERS => "Access-Control-Allow-Headers",
    ACCESS_CONTROL_ALLOW_METHODS => "Access-Control-Allow-Methods",
    ACCESS_CONTROL_ALLOW_ORIGIN => "Access-Control-Allow-Origin",
    ACCESS_CONTROL_EXPOSE_HEADERS => "Access-Control-Expose-Headers",
    ACCESS_CONTROL_MAX_AGE => "Access-Control-Max-Age",
    ACCESS_CONTROL_REQUEST_HEADERS => "Access-Control-Request-Headers",
    ACCESS_CONTROL_REQUEST_METHOD => "Access-Control-Request-Method",
    AGE => "Age",
    ALLOW => "Allow",
    AUTHORIZATION => "Authorization",
    CACHE_CONTROL => "Cache-Control",
    CONNECTION => "Connection",
    CONTENT_ENCODING => "Content-Encoding",
    CONTENT_LANGUAGE => "Content-Language",
    CONTENT_LENGTH => "Content-Length",
    CONTENT_LOCATION => "Content-Location",
    CONTENT_RANGE => "Content-Range",
    CONTENT_SECURITY_POLICY => "Content-Security-Policy",
    CONTENT_SECURITY_POLICY_REPORT_ONLY => "Content-Security-Policy-Report-Only",
    CONTENT_TYPE => "Content-Type",
    COOKIE => "Cookie",
    DATE => "Date",
    ETAG => "ETag",
    EXPIRES => "Expires",
    FORWARDED => "Forwarded",
    FROM => "From",
    HOST => "Host",
    IF_MATCH => "If-Match",
    IF_MODIFIED_SINCE => "If-Modified-Since",
    IF_NONE_MATCH => "If-None-Match",
    IF_UNMODIFIED_SINCE => "If-Unmodified-Since",
    LAST_MODIFIED => "Last-Modified",
    LINK => "Link",
    LOCATION => "Location",
    ORIGIN => "Origin",
    PERMISSIONS_POLICY => "Permissions-Policy",
    PROXY_AUTHENTICATE => "Proxy-Authenticate",
    PROXY_AUTHORIZATION => "Proxy-Authorization",
    RANGE => "Range",
    REFERER => "Referer",
    REFERRER_POLICY => "Referrer-Policy",
    RETRY_AFTER => "Retry-After",
    SERVER => "Server",
    SERVER_TIMING => "Server-Timing",
    SET_COOKIE => "Set-Cookie",
    STRICT_TRANSPORT_SECURITY => "Strict-Transport-Security",
    TRANSFER_ENCODING => "Transfer-Encoding",
    UPGRADE => "Upgrade",
    USER_AGENT => "User-Agent",
    VARY => "Vary",
    VIA => "Via",
    WWW_AUTHENTICATE => "WWW-Authenticate",
    X_CONTENT_TYPE_OPTIONS => "X-Content-Type-Options",
    X_FORWARDED_FOR => "X-Forwarded-For",
    X_FORWARDED_HOST => "X-Forwarded-Host",
    X_FORWARDED_PROTO => "X-Forwarded-Proto",
    X_FRAME_OPTIONS => "X-Frame-Options",
}

pub fn lookup_well_known_header(value: &str) -> Option<&'static str> {
    WELL_KNOWN_SET.get(value).copied()
}

/// Header name.
/// This type has case-insensitive [PartialEq] and [Hash] implementation
#[derive(Debug)]
pub enum Name {
    Static(&'static str),
    Owned(String),
}

impl AsRef<[u8]> for Name {
    fn as_ref(&self) -> &[u8] {
        match self {
            Name::Static(s) => s.as_bytes(),
            Name::Owned(s) => s.as_bytes(),
        }
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        match self {
            Name::Static(ss) => ss,
            Name::Owned(os) => os.as_str(),
        }
    }
}

impl PartialEq for Name {
    fn eq(&self, other: &Self) -> bool {
        let self_ref: &str = self.as_ref();
        let other_ref: &str = other.as_ref();
        self_ref.eq_ignore_ascii_case(other_ref)
    }
}

impl Eq for Name {}

impl Hash for Name {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let bytes: &[u8] = self.as_ref();
        for b in bytes {
            state.write_u8(b.to_ascii_lowercase());
        }
    }
}

/// Header value.
#[derive(Debug)]
pub struct Value(pub String);
