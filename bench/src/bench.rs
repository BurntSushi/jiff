use criterion::{Bencher, Criterion};

mod convert;
mod date;
mod datetime;
mod parse;
mod print;
mod timestamp;
mod tz;
mod zoned;

fn main() {
    // I find the Criterion macros to be unwieldy and opaque.
    // So I just write them out instead. It's really not that
    // much more to type...
    let mut c = Criterion::default()
        .configure_from_args()
        .sample_size(100)
        // default is 3s
        .warm_up_time(std::time::Duration::from_secs(1))
        // default is 5s
        .measurement_time(std::time::Duration::from_secs(3))
        .nresamples(100_000)
        .noise_threshold(0.01)
        .confidence_level(0.95)
        .significance_level(0.05)
        .plotting_backend(criterion::PlottingBackend::None);
    date::define(&mut c);
    datetime::define(&mut c);
    parse::define(&mut c);
    print::define(&mut c);
    timestamp::define(&mut c);
    tz::define(&mut c);
    zoned::define(&mut c);
    // This is an undocument API. Woohoo.
    c.final_summary();
}

/// Defines a Criterion benchmark for the given function.
///
/// We centralize our interaction with Criterion here so that we can tweak
/// some settings that apply to all benchmarks.
fn benchmark(
    c: &mut Criterion,
    id: impl Into<String>,
    f: impl FnMut(&mut Bencher<'_>),
) {
    c.bench_function(&id.into(), f);
}
