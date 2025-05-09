use std::time::{Duration, Instant};

use jiff::Zoned;

/// This test is meant to be run on its own as the only thing in a CI job.
///
/// It's supposed to test how long it takes for the first call to
/// `Zoned::now()` to run. The specific problem is that, when this test was
/// written, Jiff would walk `/usr/share/zoneinfo` and catalog all time zones
/// in that directory. While this is generally not much of a problem, it can be
/// on a very slow file system. In particular, this can evolve a few syscalls
/// per file, and there might be a couple thousand files inside the directory.
/// Moreover, Jiff was doing a 4-byte read of each file to check if it was TZif
/// or not.
///
/// Ref: https://github.com/BurntSushi/jiff/issues/366
#[cfg(feature = "std")]
#[test]
fn zoned_now() {
    let start = Instant::now();
    println!("{}", Zoned::now());
    let first = Instant::now().duration_since(start);
    println!("first-run-elapsed-microseconds:{}", first.as_micros());

    let start = Instant::now();
    println!("{}", Zoned::now());
    let second = Instant::now().duration_since(start);
    println!("second-run-elapsed-microseconds:{}", second.as_micros());

    // These are somewhat arbitrary, but if `Zoned::now()` starts
    // going above 100ms (even in slow CI), then it probably makes
    // sense to investigate. At time of writing (2025-05-09), the
    // biggest time observed here was ~33ms.
    assert!(
        first < Duration::from_millis(100),
        "first `Zoned::now()` call should complete in less than 100ms",
    );
    // The second call should run soon enough that the cached
    // directory traversal results are still valid. So this should
    // be extremely fast. Ideally even less than 1µs, but we give
    // CI wide latitude.
    assert!(
        second < Duration::from_millis(1),
        "second `Zoned::now()` call should complete in less than 1ms",
    );
}
