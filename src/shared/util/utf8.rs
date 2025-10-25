/// Decodes the next UTF-8 encoded codepoint from the given byte slice.
///
/// If no valid encoding of a codepoint exists at the beginning of the
/// given byte slice, then a 1-3 byte slice is returned (which is guarnateed
/// to be a prefix of `bytes`). That byte slice corresponds either to a single
/// invalid byte, or to a prefix of a valid UTF-8 encoding of a Unicode scalar
/// value (but which ultimately did not lead to a valid encoding).
///
/// This returns `None` if and only if `bytes` is empty.
///
/// This never panics.
///
/// *WARNING*: This is not designed for performance. If you're looking for
/// a fast UTF-8 decoder, this is not it. If you feel like you need one in
/// this crate, then please file an issue and discuss your use case.
pub(crate) fn decode(bytes: &[u8]) -> Option<Result<char, &[u8]>> {
    if bytes.is_empty() {
        return None;
    }
    let string = match core::str::from_utf8(&bytes[..bytes.len().min(4)]) {
        Ok(s) => s,
        Err(ref err) if err.valid_up_to() > 0 => {
            core::str::from_utf8(&bytes[..err.valid_up_to()]).unwrap()
        }
        // In this case, we want to return 1-3 bytes that make up a prefix of
        // a potentially valid codepoint.
        Err(err) => {
            return Some(Err(
                &bytes[..err.error_len().unwrap_or_else(|| bytes.len())]
            ))
        }
    };
    // OK because we guaranteed above that `string`
    // must be non-empty. And thus, `str::chars` must
    // yield at least one Unicode scalar value.
    Some(Ok(string.chars().next().unwrap()))
}
