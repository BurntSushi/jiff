#![cfg_attr(fuzzing, no_main)]
mod shim;

use jiff::fmt::temporal;
use libfuzzer_sys::fuzz_target;
use std::borrow::Cow;

fn do_fuzz(data: &[u8]) {
    const TEMPORAL_PARSER: temporal::SpanParser = temporal::SpanParser::new();
    const TEMPORAL_PRINTER: temporal::SpanPrinter =
        temporal::SpanPrinter::new();
    if let Ok(first) = TEMPORAL_PARSER.parse_span(data) {
        let mut unparsed = Vec::with_capacity(data.len()); // get a good start at least
        TEMPORAL_PRINTER
            .print_span(&first, &mut unparsed)
            .expect("We parsed it, so we should be able to print it.");

        match TEMPORAL_PARSER.parse_span(&unparsed) {
            Ok(second) => {
                assert_eq!(first, second, "Expected the initially parsed value to be equal to the value after printing and re-parsing");
            }
            Err(e) if cfg!(not(feature = "relaxed")) => {
                let unparsed_str = String::from_utf8_lossy(&unparsed);
                panic!(
                    "Should be able to parse a printed value; failed with `{e}' at: `{unparsed_str}'{}, corresponding to {first:?}",
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
}

fuzz_target!(|data: &[u8]| do_fuzz(data));

maybe_define_main!();
