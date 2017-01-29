# uhttp_media_type -- HTTP MIME/media type parser

[Documentation](https://docs.rs/uhttp_media_type)

This crate provides a zero-allocation, slice-based parser for [HTTP Media
Types](https://tools.ietf.org/html/rfc7231#section-3.1.1) as they appear in
`Content-Type` and `Accept` headers.

## Example

```rust
use uhttp_media_type::{MediaType, MediaParams, ParamValue};

let mt = MediaType::new("application/json; charset=utf-8; param=\"a value\"").unwrap();
assert_eq!(mt.mimetype, "application/json");
assert_eq!(mt.parts().unwrap(), ("application", "json"));
assert_eq!(mt.params, " charset=utf-8; param=\"a value\"");

let mut params = MediaParams::new(mt.params);

let (key, val) = params.next().unwrap().unwrap();
assert_eq!(key, "charset");
assert_eq!(val, ParamValue::Unquoted("utf-8"));
assert_eq!(val.inner(), "utf-8");

let (key, val) = params.next().unwrap().unwrap();
assert_eq!(key, "param");
assert_eq!(val, ParamValue::Quoted("a value"));
assert_eq!(val.inner(), "a value");

assert!(params.next().is_none());
```

## Usage

This [crate](https://crates.io/crates/uhttp_media_type) can be used through cargo by
adding it as a dependency in `Cargo.toml`:

```toml
[dependencies]
uhttp_media_type = "0.5.0"
```
and importing it in the crate root:

```rust
extern crate uhttp_media_type;
```
