#![cfg_attr(fuzz, no_main)]
mod shim;

use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};
use libfuzzer_sys::{arbitrary, fuzz_target};
use std::borrow::Cow;

use jiff::fmt::strtime::parse;

#[derive(Debug)]
struct Input<'a> {
    format: &'a str,
    input: &'a str,
}

impl<'a> Arbitrary<'a> for Input<'a> {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let fmt_len: u8 = u.arbitrary()?;
        let in_len: u16 = u.arbitrary()?;
        let format = u.bytes(fmt_len as usize)?;
        let format = core::str::from_utf8(format)
            .map_err(|_| arbitrary::Error::IncorrectFormat)?;
        // TODO this is marked as "currently unsupported", but may be better in the future
        if !format.is_ascii() {
            return Err(arbitrary::Error::IncorrectFormat);
        }
        let input = u.bytes(in_len as usize)?;
        let input = core::str::from_utf8(input)
            .map_err(|_| arbitrary::Error::IncorrectFormat)?;
        Ok(Input { format, input })
    }

    fn arbitrary_take_rest(
        mut u: Unstructured<'a>,
    ) -> arbitrary::Result<Self> {
        let len: u8 = u.arbitrary()?;
        let _in_len: u16 = u.arbitrary()?; // ignored in take rest, but keep it consistent
        let format = u.bytes(len as usize)?;
        let format = core::str::from_utf8(format)
            .map_err(|_| arbitrary::Error::IncorrectFormat)?;
        let input = u.take_rest();
        let input = core::str::from_utf8(input)
            .map_err(|_| arbitrary::Error::IncorrectFormat)?;
        Ok(Input { format, input })
    }
}

fn do_fuzz(src: Input) {
    if let Ok(first) = parse(src.format, src.input) {
        let mut unparsed = Vec::with_capacity(src.input.len());
        first
            .format(src.format, &mut unparsed)
            .expect("We parsed it, so we should be able to print it");
        if let Ok(second) = parse(src.format, &unparsed) {
            // there's not a direct equality here
            // to get around this, we compare unparsed with doubly-unparsed

            let mut unparsed_again = Vec::with_capacity(unparsed.len());
            second.format(src.format, &mut unparsed_again).expect(
                "We parsed it (twice!), so we should be able to print it",
            );

            assert_eq!(unparsed, unparsed_again, "Expected the initially parsed value to be equal to the value after printing and re-parsing.");
        } else if cfg!(not(feature = "relaxed")) {
            let unparsed_str = String::from_utf8_lossy(&unparsed);
            panic!(
                "Should be able to parse a printed value; failed at: `{}'{}",
                unparsed_str,
                if matches!(unparsed_str, Cow::Owned(_)) {
                    Cow::from(format!(" (lossy; actual bytes: {unparsed:?})"))
                } else {
                    Cow::from("")
                }
            );
        }
    }
}

fuzz_target!(|data: Input<'_>| do_fuzz(data));

maybe_define_main!();
