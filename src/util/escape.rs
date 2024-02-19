/*!
Provides convenience routines for escaping raw bytes.

This was copied from `regex-automata` with a few light edits.
*/

/// Provides a convenient `Debug` implementation for a `u8`.
///
/// The `Debug` impl treats the byte as an ASCII, and emits a human readable
/// representation of it. If the byte isn't ASCII, then it's emitted as a hex
/// escape sequence.
#[derive(Clone, Copy)]
pub struct Byte(pub u8);

impl core::fmt::Display for Byte {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        if self.0 == b' ' {
            return write!(f, " ");
        }
        // 10 bytes is enough to cover any output from ascii::escape_default.
        let mut bytes = [0u8; 10];
        let mut len = 0;
        for (i, mut b) in core::ascii::escape_default(self.0).enumerate() {
            // capitalize \xab to \xAB
            if i >= 2 && b'a' <= b && b <= b'f' {
                b -= 32;
            }
            bytes[len] = b;
            len += 1;
        }
        write!(f, "{}", core::str::from_utf8(&bytes[..len]).unwrap())
    }
}

impl core::fmt::Debug for Byte {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "\"")?;
        core::fmt::Display::fmt(self, f)?;
        write!(f, "\"")?;
        Ok(())
    }
}

/// Provides a convenient `Debug` implementation for `&[u8]`.
///
/// This generally works best when the bytes are presumed to be mostly UTF-8,
/// but will work for anything. For any bytes that aren't UTF-8, they are
/// emitted as hex escape sequences.
pub struct Bytes<'a>(pub &'a [u8]);

impl<'a> core::fmt::Display for Bytes<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        // This is a sad re-implementation of a similar impl found in bstr.
        let mut bytes = self.0;
        while let Some(result) = utf8_decode(bytes) {
            let ch = match result {
                Ok(ch) => ch,
                Err(byte) => {
                    write!(f, r"\x{:02x}", byte)?;
                    bytes = &bytes[1..];
                    continue;
                }
            };
            bytes = &bytes[ch.len_utf8()..];
            match ch {
                '\0' => write!(f, "\\0")?,
                // ASCII control characters except \0, \n, \r, \t
                '\x01'..='\x08'
                | '\x0b'
                | '\x0c'
                | '\x0e'..='\x19'
                | '\x7f' => {
                    write!(f, "\\x{:02x}", u32::from(ch))?;
                }
                '\n' | '\r' | '\t' | _ => {
                    write!(f, "{}", ch.escape_debug())?;
                }
            }
        }
        Ok(())
    }
}

impl<'a> core::fmt::Debug for Bytes<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "\"")?;
        core::fmt::Display::fmt(self, f)?;
        write!(f, "\"")?;
        Ok(())
    }
}

/// Decodes the next UTF-8 encoded codepoint from the given byte slice.
///
/// If no valid encoding of a codepoint exists at the beginning of the given
/// byte slice, then the first byte is returned instead.
///
/// This returns `None` if and only if `bytes` is empty.
///
/// This never panics.
///
/// *WARNING*: This is not designed for performance. If you're looking for a
/// fast UTF-8 decoder, this is not it. If you feel like you need one in this
/// crate, then please file an issue and discuss your use case.
fn utf8_decode(bytes: &[u8]) -> Option<Result<char, u8>> {
    if bytes.is_empty() {
        return None;
    }
    let len = match utf8_len(bytes[0]) {
        None => return Some(Err(bytes[0])),
        Some(len) if len > bytes.len() => return Some(Err(bytes[0])),
        Some(1) => return Some(Ok(char::from(bytes[0]))),
        Some(len) => len,
    };
    match core::str::from_utf8(&bytes[..len]) {
        Ok(s) => Some(Ok(s.chars().next().unwrap())),
        Err(_) => Some(Err(bytes[0])),
    }
}

/// Given a UTF-8 leading byte, this returns the total number of code units
/// in the following encoded codepoint.
///
/// If the given byte is not a valid UTF-8 leading byte, then this returns
/// `None`.
fn utf8_len(byte: u8) -> Option<usize> {
    if byte <= 0x7F {
        return Some(1);
    } else if byte & 0b1100_0000 == 0b1000_0000 {
        return None;
    } else if byte <= 0b1101_1111 {
        Some(2)
    } else if byte <= 0b1110_1111 {
        Some(3)
    } else if byte <= 0b1111_0111 {
        Some(4)
    } else {
        None
    }
}
