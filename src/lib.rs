//! This crate provides a zero-allocation, slice-based parser for [HTTP Media
//! Types](https://tools.ietf.org/html/rfc7231#section-3.1.1) as they appear in
//! `Content-Type` and `Accept` headers.
//!
//! ## Example
//!
//! ```rust
//! use uhttp_media_type::{MediaType, MediaParams, ParamValue};
//!
//! let mt = MediaType::new("application/json; charset=utf-8; param=\"a value\"").unwrap();
//! assert_eq!(mt.mimetype, "application/json");
//! assert_eq!(mt.parts().unwrap(), ("application", "json"));
//! assert_eq!(mt.params, " charset=utf-8; param=\"a value\"");
//!
//! let mut params = MediaParams::new(mt.params);
//!
//! let (key, val) = params.next().unwrap().unwrap();
//! assert_eq!(key, "charset");
//! assert_eq!(val, ParamValue::Unquoted("utf-8"));
//! assert_eq!(val.inner(), "utf-8");
//!
//! let (key, val) = params.next().unwrap().unwrap();
//! assert_eq!(key, "param");
//! assert_eq!(val, ParamValue::Quoted("a value"));
//! assert_eq!(val.inner(), "a value");
//!
//! assert!(params.next().is_none());
//! ```

#![feature(field_init_shorthand)]

extern crate memchr;

use memchr::memchr;

/// Parses a media type field into its MIME type and parameter components.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub struct MediaType<'a> {
    /// The MIME type should have form `type/subtype` for some media type and subtype.
    ///
    /// This is guaranteed to be nonempty and free of surrounding whitespace but is not
    /// guaranteed to be in the correct syntax. It requires case-insensitive comparison to
    /// other strings [RFC7231§3.1.1.1].
    pub mimetype: &'a str,

    /// Parameter string for the MIME type.
    pub params: &'a str,
}

impl<'a> MediaType<'a> {
    /// Try to parse a `MediaType` from the given string.
    pub fn new(s: &'a str) -> Result<Self, ()> {
        // Split on the ';' that begins parameters, or use the whole string.
        let (mimetype, params) = match memchr(b';', s.as_bytes()) {
            Some(idx) => {
                let (l, r) = s.split_at(idx);
                (l, &r[1..])
            },
            None => (s, &""[..]),
        };

        // Mimetype may have surrounding whitespace [RFC7231§3.1.1.1].
        let mimetype = mimetype.trim();

        // Mimetype should be nonempty [RFC7231§3.1.1.1].
        if mimetype.is_empty() {
            return Err(());
        }

        Ok(MediaType { mimetype, params })
    }

    /// Try to retrieve the type and subtype, in that order, of the current MIME type.
    ///
    /// Each part may be empty or contain whitespace and requires case-insensitive
    /// comparison to other strings.
    pub fn parts(&self) -> Result<(&'a str, &'a str), ()> {
        let mut parts = self.mimetype.split('/');

        let main = parts.next().ok_or(())?;
        let sub = parts.next().ok_or(())?;

        if parts.next().is_none() {
            Ok((main, sub))
        } else {
            Err(())
        }
    }
}

/// Iterator over key/value pairs in a media type parameter string.
///
/// Each iteration yields a `(key, value)` for the key and value of a parameter. The key
/// is guaranteed to be free of surrounding whitespace but is not guaranteed to be free of
/// internal whitespace. It requires case-insensitive comparison to other strings. The
/// value has the guarantees of `ParamValue` and doesn't necessarily require
/// case-insensitive comparison.
#[derive(Copy, Clone, Debug, Hash)]
pub struct MediaParams<'a>(&'a str);

impl<'a> MediaParams<'a> {
    /// Create a new `MediaParams` iterator over the given parameters string.
    pub fn new(s: &'a str) -> Self {
        MediaParams(s)
    }
}

impl<'a> Iterator for MediaParams<'a> {
    type Item = Result<(&'a str, ParamValue<'a>), ()>;

    fn next(&mut self) -> Option<Self::Item> {
        let (key, rest) = match memchr(b'=', self.0.as_bytes()) {
            Some(idx) => self.0.split_at(idx),
            None => return None,
        };

        // Key may have leading whitespace [RFC7231§3.1.1.1]. This may violate the syntax
        // requirement of no whitespace around the '=' separator, but the requirement
        // doesn't seem necessary to the rest of the grammar, isn't given any rationale,
        // and doesn't seem worth the complexity to check it.
        let key = key.trim();

        let (val, rest) = match ParamValue::new(&rest[1..]) {
            Ok(v) => v,
            Err(()) => return Some(Err(())),
        };

        self.0 = rest;

        Some(Ok((key, val)))
    }
}

/// A value for a media type parameter.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum ParamValue<'a> {
    /// Value is in simple, unquoted form.
    ///
    /// The inner string is guaranteed to be nonempty and free of surrounding whitespace
    /// but may contain internal whitespace.
    Unquoted(&'a str),
    /// Value is in quoted form.
    ///
    /// The inner string contains the text inside the quotes, which may empty, may contain
    /// internal and surrounding whitespace, or may contain backslash-escaped characters
    /// that require further processing.
    Quoted(&'a str),
}

impl<'a> ParamValue<'a> {
    fn new(s: &'a str) -> Result<(Self, &'a str), ()> {
        if s.is_empty() {
            return Err(());
        }

        if s.starts_with('"') {
            let len = find_end_quote(s.as_bytes()).ok_or(())?;

            // Skip over beginning quote and extract value.
            let (val, rest) = (&s[1..]).split_at(len);
            // Skip over ending quote.
            let rest = &rest[1..];

            // Extract any text between ending quote and semicolon.
            let (leftover, rest) = match memchr(b';', rest.as_bytes()) {
                Some(idx) => {
                    let (l, r) = rest.split_at(idx);
                    (l, &r[1..])
                },
                None => (rest, &""[..]),
            };

            // Verify that text between ending quote and semicolon contains only
            // whitespace.
            if !leftover.trim().is_empty() {
                return Err(());
            }

            Ok((ParamValue::Quoted(val), rest))
        } else {
            let (val, rest) = match memchr(b';', s.as_bytes()) {
                Some(idx) => {
                    let (l, r) = s.split_at(idx);
                    (l, &r[1..])
                },
                None => (s, &""[..]),
            };

            // Value may have surrounding whitespace [RFC7231§3.1.1.1].
            let val = val.trim();

            // Unquoted value must be nonempty [RFC7231§3.1.1.1].
            if val.is_empty() {
                return Err(());
            }

            Ok((ParamValue::Unquoted(val), rest))
        }
    }

    /// Retrieve the inner text value of the parameter.
    pub fn inner(&self) -> &'a str {
        match *self {
            ParamValue::Unquoted(s) => s,
            ParamValue::Quoted(s) => s,
        }
    }
}

/// Find the terminating quote in the given string, skipping backslash-escaped quotes, and
/// return the number of bytes within the quotes.
fn find_end_quote(s: &[u8]) -> Option<usize> {
    debug_assert!(s[0] == b'"');

    // Start after the beginning quote.
    let start = match s.get(1..) {
        Some(x) => x,
        None => return None,
    };

    // Current slice being searched for quotes.
    let mut cur = start;
    // Current length of text (bytes) within quotes.
    let mut len = 0;

    loop {
        // Find the next quote.
        let idx = match memchr(b'"', cur) {
            Some(idx) => idx,
            None => return None,
        };

        // Include everything up to the quote.
        len += idx;

        let (text, rest) = cur.split_at(idx);

        if text.is_empty() || escape_count(text) % 2 == 0 {
            break;
        }

        // Include the escaped quote.
        len += 1;

        // Try to move past the quote.
        cur = match rest.get(1..) {
            Some(x) => x,
            None => return None,
        };
    }

    Some(len)
}

/// Count the number of contiguous escape characters (backslashes) that exist at the end
/// of the given slice.
fn escape_count(s: &[u8]) -> usize {
    s.iter().rev().take_while(|&&b| b == b'\\').fold(0, |s, _| s + 1)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_media_type() {
        let m = MediaType::new("text/html;charset=utf-8").unwrap();
        assert_eq!(m.mimetype, "text/html");
        assert_eq!(m.params, "charset=utf-8");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "text");
        assert_eq!(sub, "html");

        let m = MediaType::new("text/*;charset=utf-8").unwrap();
        assert_eq!(m.mimetype, "text/*");
        assert_eq!(m.params, "charset=utf-8");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "text");
        assert_eq!(sub, "*");

        let m = MediaType::new("image/*").unwrap();
        assert_eq!(m.mimetype, "image/*");
        assert_eq!(m.params, "");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "image");
        assert_eq!(sub, "*");

        let m = MediaType::new("text/json").unwrap();
        assert_eq!(m.mimetype, "text/json");
        assert_eq!(m.params, "");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "text");
        assert_eq!(sub, "json");

        let m = MediaType::new("text/json ;").unwrap();
        assert_eq!(m.mimetype, "text/json");
        assert_eq!(m.params, "");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "text");
        assert_eq!(sub, "json");

        let m = MediaType::new("text/json ;    ").unwrap();
        assert_eq!(m.mimetype, "text/json");
        assert_eq!(m.params, "    ");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "text");
        assert_eq!(sub, "json");

        let m = MediaType::new("text/html; charset=\"utf-8\"").unwrap();
        assert_eq!(m.mimetype, "text/html");
        assert_eq!(m.params, " charset=\"utf-8\"");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "text");
        assert_eq!(sub, "html");

        let m = MediaType::new("\t\t    text/html  \t; charset=utf-8    \t\t").unwrap();
        assert_eq!(m.mimetype, "text/html");
        assert_eq!(m.params, " charset=utf-8    \t\t");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "text");
        assert_eq!(sub, "html");

        let m = MediaType::new(" text  /\t*  \t; charset=utf-8").unwrap();
        assert_eq!(m.mimetype, "text  /\t*");
        assert_eq!(m.params, " charset=utf-8");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "text  ");
        assert_eq!(sub, "\t*");

        let m = MediaType::new("\t\t    text/html  \t; charset=utf-8    \t\t").unwrap();
        assert_eq!(m.mimetype, "text/html");
        assert_eq!(m.params, " charset=utf-8    \t\t");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "text");
        assert_eq!(sub, "html");

        let m = MediaType::new("text/hello space").unwrap();
        assert_eq!(m.mimetype, "text/hello space");
        assert_eq!(m.params, "");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "text");
        assert_eq!(sub, "hello space");

        let m = MediaType::new("image/").unwrap();
        assert_eq!(m.mimetype, "image/");
        assert_eq!(m.params, "");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "image");
        assert_eq!(sub, "");

        let m = MediaType::new("image/    ").unwrap();
        assert_eq!(m.mimetype, "image/");
        assert_eq!(m.params, "");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "image");
        assert_eq!(sub, "");

        let m = MediaType::new("/json").unwrap();
        assert_eq!(m.mimetype, "/json");
        assert_eq!(m.params, "");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "");
        assert_eq!(sub, "json");

        let m = MediaType::new("   /json").unwrap();
        assert_eq!(m.mimetype, "/json");
        assert_eq!(m.params, "");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "");
        assert_eq!(sub, "json");

        let m = MediaType::new("/").unwrap();
        assert_eq!(m.mimetype, "/");
        assert_eq!(m.params, "");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "");
        assert_eq!(sub, "");

        let m = MediaType::new("\t\t /   ").unwrap();
        assert_eq!(m.mimetype, "/");
        assert_eq!(m.params, "");
        let (main, sub) = m.parts().unwrap();
        assert_eq!(main, "");
        assert_eq!(sub, "");

        assert!(MediaType::new("").is_err());
        assert!(MediaType::new("   \t").is_err());
        assert!(MediaType::new("   \t; charet=utf8").is_err());

        let m = MediaType::new("text ; charset=utf8").unwrap();
        assert_eq!(m.mimetype, "text");
        assert_eq!(m.params, " charset=utf8");
        assert!(m.parts().is_err());
    }

    #[test]
    fn test_escape_count() {
        assert_eq!(escape_count(br"\"), 1);
        assert_eq!(escape_count(br"\\"), 2);
        assert_eq!(escape_count(br"\\\"), 3);
        assert_eq!(escape_count(br"\\\\"), 4);
        assert_eq!(escape_count(br"42 \\\\"), 4);
        assert_eq!(escape_count(br"\\ 42 \\\\"), 4);
        assert_eq!(escape_count(br"\\ \\\\"), 4);
        assert_eq!(escape_count(br"\\a\\\\"), 4);
    }

    #[test]
    fn test_find_end_quote() {
        assert_eq!(find_end_quote(b"\""), None);
        assert_eq!(find_end_quote(b"\"\""), Some(b"".len()));
        assert_eq!(find_end_quote(b"\"utf-8\""), Some(b"utf-8".len()));
        assert_eq!(find_end_quote(b"\"'utf-8'\""), Some(b"'utf-8'".len()));
        assert_eq!(find_end_quote(b"\"utf-8\"; key=value"), Some(b"utf-8".len()));

        assert_eq!(find_end_quote(b"\"hello \\\"world\\\" 1337\""),
            Some(b"hello \\\"world\\\" 1337".len()));

        assert_eq!(find_end_quote(b"\"abcd fghi\\\" jklm \"; nopq"),
            Some(b"abcd fghi\\\" jklm ".len()));

        assert_eq!(find_end_quote(b"\"utf-8; key=value"), None);
        assert_eq!(find_end_quote(b"\"utf-8\\\"; key=value"), None);
    }

    #[test]
    fn test_param_value() {
        assert_eq!(ParamValue::new(""), Err(()));
        assert_eq!(ParamValue::new("  \t"), Err(()));
        assert_eq!(ParamValue::new("  \t;charset=utf8"), Err(()));
        assert_eq!(ParamValue::new("\""), Err(()));

        assert_eq!(ParamValue::new("\"\""), Ok((
            ParamValue::Quoted(&""[..]),
            &""[..],
        )));

        assert_eq!(ParamValue::new("\"\""), Ok((
            ParamValue::Quoted(&""[..]),
            &""[..],
        )));

        assert_eq!(ParamValue::new("\"utf-8\""), Ok((
            ParamValue::Quoted(&"utf-8"[..]),
            &""[..],
        )));

        assert_eq!(ParamValue::new("\"utf-8, \\\" wat\"; key=value"), Ok((
            ParamValue::Quoted(&"utf-8, \\\" wat"[..]),
            &" key=value"[..],
        )));

        assert_eq!(ParamValue::new("\"utf-8; other\"; key=value"), Ok((
            ParamValue::Quoted(&"utf-8; other"[..]),
            &" key=value"[..],
        )));

        assert_eq!(ParamValue::new("\"utf-8\\\"\"; key=value"), Ok((
            ParamValue::Quoted(&"utf-8\\\""[..]),
            &" key=value"[..],
        )));

        assert_eq!(ParamValue::new("\"utf-8\\\"\" \t\t ; key=value"), Ok((
            ParamValue::Quoted(&"utf-8\\\""[..]),
            &" key=value"[..],
        )));

        assert_eq!(ParamValue::new("\"utf-8\\\"\" wrong; key=value"), Err(()));

        assert_eq!(ParamValue::new("utf-8; key=value"), Ok((
            ParamValue::Unquoted(&"utf-8"[..]),
            &" key=value"[..],
        )));

        assert_eq!(ParamValue::new("some-value   "), Ok((
            ParamValue::Unquoted(&"some-value"[..]),
            &""[..],
        )));

        assert_eq!(ParamValue::new("utf-8 abc; key=value"), Ok((
            ParamValue::Unquoted(&"utf-8 abc"[..]),
            &" key=value"[..],
        )));
    }

    #[test]
    fn test_media_params() {
        let mut p = MediaParams::new("charset=utf-8");

        let (k, v) = p.next().unwrap().unwrap();
        assert_eq!(k, "charset");
        assert_eq!(v, ParamValue::Unquoted("utf-8"));

        assert!(p.next().is_none());

        let mut p = MediaParams::new(" charset=\"utf-8\"");

        let (k, v) = p.next().unwrap().unwrap();
        assert_eq!(k, "charset");
        assert_eq!(v, ParamValue::Quoted("utf-8"));

        assert!(p.next().is_none());

        let mut p = MediaParams::new(
            "  \tcharset=utf-8; chars=\"utf-42; wat\";key=\"some \\\"value\\\"\";   k=v  \t\t"
        );

        let (k, v) = p.next().unwrap().unwrap();
        assert_eq!(k, "charset");
        assert_eq!(v, ParamValue::Unquoted("utf-8"));

        let (k, v) = p.next().unwrap().unwrap();
        assert_eq!(k, "chars");
        assert_eq!(v, ParamValue::Quoted("utf-42; wat"));

        let (k, v) = p.next().unwrap().unwrap();
        assert_eq!(k, "key");
        assert_eq!(v, ParamValue::Quoted("some \\\"value\\\""));

        let (k, v) = p.next().unwrap().unwrap();
        assert_eq!(k, "k");
        assert_eq!(v, ParamValue::Unquoted("v"));

        assert!(p.next().is_none());
    }

    #[test]
    fn test_media_type_params() {
        let m = MediaType::new("text/html;charset=utf-8").unwrap();
        assert_eq!(m.mimetype, "text/html");
        let mut p = MediaParams::new(m.params);
        let (k, v) = p.next().unwrap().unwrap();
        assert_eq!(k, "charset");
        assert_eq!(v, ParamValue::Unquoted("utf-8"));
        assert!(p.next().is_none());

        let m = MediaType::new("text/*;charset=utf-8").unwrap();
        assert_eq!(m.mimetype, "text/*");
        let mut p = MediaParams::new(m.params);
        let (k, v) = p.next().unwrap().unwrap();
        assert_eq!(k, "charset");
        assert_eq!(v, ParamValue::Unquoted("utf-8"));
        assert!(p.next().is_none());

        let m = MediaType::new("text/html; charset=\"utf-8\"").unwrap();
        assert_eq!(m.mimetype, "text/html");
        let mut p = MediaParams::new(m.params);
        let (k, v) = p.next().unwrap().unwrap();
        assert_eq!(k, "charset");
        assert_eq!(v, ParamValue::Quoted("utf-8"));
        assert!(p.next().is_none());

        let m = MediaType::new("text/json; charset=\"utf-8\"; key=val  \t").unwrap();
        assert_eq!(m.mimetype, "text/json");
        let mut p = MediaParams::new(m.params);
        let (k, v) = p.next().unwrap().unwrap();
        assert_eq!(k, "charset");
        assert_eq!(v, ParamValue::Quoted("utf-8"));
        let (k, v) = p.next().unwrap().unwrap();
        assert_eq!(k, "key");
        assert_eq!(v, ParamValue::Unquoted("val"));
        assert!(p.next().is_none());

        let m = MediaType::new("text/json").unwrap();
        assert_eq!(m.mimetype, "text/json");
        let mut p = MediaParams::new(m.params);
        assert!(p.next().is_none());

        let m = MediaType::new("text/json ;").unwrap();
        assert_eq!(m.mimetype, "text/json");
        let mut p = MediaParams::new(m.params);
        assert!(p.next().is_none());
    }
}
