#![cfg_attr(fuzzing, no_main)]

use std::borrow::Cow;

use libfuzzer_sys::{
    arbitrary,
    arbitrary::{Arbitrary, Unstructured},
    fuzz_target,
};

use jiff::fmt::strtime::parse;

mod shim;

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
        let input = u.bytes(in_len as usize)?;
        let input = core::str::from_utf8(input)
            .map_err(|_| arbitrary::Error::IncorrectFormat)?;
        Ok(Input { format, input })
    }

    fn arbitrary_take_rest(
        mut u: Unstructured<'a>,
    ) -> arbitrary::Result<Self> {
        let len: u8 = u.arbitrary()?;
        // ignored in take rest, but keep it consistent
        let _in_len: u16 = u.arbitrary()?;
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
        if first.format(src.format, &mut unparsed).is_err() {
            // There are a number of reasons why this may fail. the formatter
            // is simply not as strong as the parser, so we accept failure
            // here.
            return;
        }

        match parse(src.format, &unparsed) {
            Ok(second) => {
                // There's not a direct equality here. To get around this, we
                // compare unparsed with doubly-unparsed.

                let mut unparsed_again = Vec::with_capacity(unparsed.len());
                second.format(src.format, &mut unparsed_again).expect(
                    "We parsed it (twice!), so we should be able to print it",
                );

                assert_eq!(
                    unparsed,
                    unparsed_again,
                    "expected the initially parsed value \
                     to be equal to the value after \
                     printing and re-parsing; \
                     found `{}', expected `{}'",
                    String::from_utf8_lossy(&unparsed_again),
                    String::from_utf8_lossy(&unparsed),
                );
            }
            Err(e) if cfg!(not(feature = "relaxed")) => {
                let unparsed_str = String::from_utf8_lossy(&unparsed);
                panic!(
                    "should be able to parse a printed value; \
                     failed with `{e}` at: `{unparsed_str}`{}, \
                     corresponding to {first:?}",
                    if matches!(unparsed_str, Cow::Owned(_)) {
                        Cow::from(format!(
                            " (lossy; actual bytes: {unparsed:?})"
                        ))
                    } else {
                        Cow::from("")
                    }
                );
            }
            Err(_) => {}
        }
    }
}

fuzz_target!(|data: Input<'_>| do_fuzz(data));

maybe_define_main!();
