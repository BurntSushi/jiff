use jiff::tz::TimeZone;
use std::thread::sleep;
use std::time::Duration;

fn main() {
    // The time zone is updated by async thread each 20 seconds.
    // And we get the default time zone continuously,
    // so we can see the log: `cache is still using, so update the tz.`
    for i in 1..=50 {
        sleep(Duration::from_secs(1));
        TimeZone::system();
        println!("round 1------{i}");
    }

    // Stop the get the default time zone for a while, so we can see the log :
    // `cache is not used so far, so stop this thread.`
    for i in 1..=35 {
        sleep(Duration::from_secs(1));
        println!("round 2------{i}");
    }

    // Get the default time zone again, we can see
    // `try_update_time_zone` log to start the thread again.
    // And see the `cache is still using, so update the tz.` log later.
    for i in 1..=50 {
        sleep(Duration::from_secs(1));
        TimeZone::system();
        println!("round 3------{i}");
    }

    // See the `cache is not used so far, so stop this thread.` log later.
    for i in 1..=50 {
        sleep(Duration::from_secs(1));
        println!("round 4------{i}");
    }
}
