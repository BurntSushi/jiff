#![cfg_attr(fuzzing, no_main)]

use std::borrow::Cow;

use libfuzzer_sys::fuzz_target;

use jiff::fmt::rfc2822;

mod shim;

fn do_fuzz(data: &[u8]) {
    const RFC2822_PARSER: rfc2822::DateTimeParser =
        rfc2822::DateTimeParser::new();
    const RFC2822_PRINTER: rfc2822::DateTimePrinter =
        rfc2822::DateTimePrinter::new();

    let Ok(first) = RFC2822_PARSER.parse_zoned(data) else { return };
    let mut unparsed = Vec::with_capacity(data.len());
    RFC2822_PRINTER
        .print_zoned(&first, &mut unparsed)
        .expect("We parsed it, so we should be able to print it");

    match RFC2822_PARSER.parse_zoned(&unparsed) {
        Ok(second) => {
            assert_eq!(
                first, second,
                "expected the initially parsed value \
                 to be equal to the value after printing and re-parsing",
            );
        }
        Err(e) if cfg!(not(feature = "relaxed")) => {
            let unparsed_str = String::from_utf8_lossy(&unparsed);
            panic!(
                "should be able to parse a printed value; \
                 failed with `{e}` at: `{unparsed_str}`{}, \
                 corresponding to {first:?}",
                if matches!(unparsed_str, Cow::Owned(_)) {
                    Cow::from(format!(" (lossy; actual bytes: {unparsed:?})"))
                } else {
                    Cow::from("")
                }
            );
        }
        Err(_) => {}
    }
}

fuzz_target!(|data: &[u8]| do_fuzz(data));

maybe_define_main!();
