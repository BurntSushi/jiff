Links:

* [ISO 8601](https://www.iso.org/iso-8601-date-and-time-format.html)
* [RFC 3339](https://datatracker.ietf.org/doc/html/rfc3339)
    * [Syntax extensions to RFC 3339](https://ryzokuken.dev/draft-ryzokuken-datetime-extended/documents/rfc-3339.html)
* [RFC 8536](https://datatracker.ietf.org/doc/html/rfc8536)
* [New RFC 8536](https://datatracker.ietf.org/doc/draft-murchison-rfc8536bis/)
* [RFC 9557](https://www.rfc-editor.org/rfc/rfc9557.html)
* [RFC 2822 datetimes](https://datatracker.ietf.org/doc/html/rfc2822#section-3.3)
* [FreeDesktop.org on localtime](https://www.freedesktop.org/software/systemd/man/latest/localtime.html)
* [About the IANA Time Zone Database](https://data.iana.org/time-zones/tz-link.html)
* [Lisp code for *Calendrical calculations*](https://github.com/EdReingold/calendar-code2)
* [SOFA](https://www.iausofa.org/)
* [MUSL `tzset`](https://git.musl-libc.org/cgit/musl/tree/src/time/__tz.c#n127)
* [Talk about leap seconds](https://www.youtube.com/watch?v=meK8dY9l_gE&t=9s)
* [Toward a Standard C++ ’Date’ Class](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2012/n3344.pdf)
* [2023-02 - Calendrical C++: std::chrono, History, Mathematics and the Computus - Ben Deane](https://www.youtube.com/watch?v=fIWDQclgUEE)
* [Local Time Disambiguation (PEP 495)](https://peps.python.org/pep-0495/)
* [Temporal tests](https://github.com/tc39/test262/tree/main/test/built-ins/Temporal)
* [Modeling Time - Eric Evans (Joda Time?)](https://www.youtube.com/watch?v=T29WzvaPNc8&t=657s)
* [Fixing JavaScript Date – Getting Started](https://maggiepint.com/2017/04/09/fixing-javascript-date-getting-started/)
* [PEP-4095](https://peps.python.org/pep-0495/)
* [Temporal API blog](https://2ality.com/2021/06/temporal-api.html)


Other Rust crates:

* [chrono](https://github.com/chronotope/chrono)
* [chrono-tz](https://github.com/chronotope/chrono-tz)
* [time](https://github.com/time-rs/time)
* [icu_calendar](https://docs.rs/icu_calendar/latest/icu_calendar/)
* [hifitime](https://docs.rs/hifitime/latest/hifitime/index.html)
    * [hifitime model checking](https://model-checking.github.io/kani-verifier-blog/2023/03/31/how-kani-helped-find-bugs-in-hifitime.html)
* [kine](https://crates.io/crates/kine)
* [Flexible datetime parsing](https://crates.io/crates/parse_datetime)
* [eos](https://github.com/Rapptz/eos) (unfinished/unpublished)
* [temporal_rs](https://github.com/boa-dev/temporal)
* [tz-rs](https://github.com/x-hgg-x/tz-rs)
* [iana-time-zone](https://github.com/strawlab/iana-time-zone)
* [parse-zoneinfo](https://github.com/chronotope/parse-zoneinfo)
* [tzfile](https://github.com/kennytm/tzfile)

Other datetime libraries:

* [ThreeTen](https://www.threeten.org/threeten-extra/). Seems to have good
support for leap seconds. See https://github.com/robinst/java-threeten-test.

Read/perused:

* [Time Standards Reference](https://geometrian.com/programming/reference/timestds/index.php)
* [Actual leap seconds](https://hpiers.obspm.fr/iers/bul/bulc/ntp/leap-seconds.list)
  * [Even more leap seconds](https://maia.usno.navy.mil/ser7/tai-utc.dat)
* [ISO 8601 summary](https://www.cl.cam.ac.uk/~mgk25/iso-time.html)
* [POSIX `TZ` environment variable](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap08.html)
* [Joda Time User Guide](https://www.joda.org/joda-time/userguide.html)
* [JSR 310](https://jcp.org/aboutJava/communityprocess/pfd/jsr310/JSR-310-guide.html)
* [`java.time` API](https://docs.oracle.com/javase/8/docs/api/java/time/package-summary.html)
* [Leap seconds](https://en.wikipedia.org/wiki/Leap_second)
* [Koka's standard `time` library](https://koka-lang.github.io/koka/doc/std_time.html)
* ["Seconds Since the Epoch"](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap04.html#tag_04_16)
* [Storing UTC is not a silver bullet](https://codeblog.jonskeet.uk/2019/03/27/storing-utc-is-not-a-silver-bullet/)
* [Unix time and leap seconds](https://en.wikipedia.org/wiki/Unix_time#Leap_seconds)
* [UTC-SLS](https://www.cl.cam.ac.uk/~mgk25/time/utc-sls/)
* [`time` crate's issue on `localtime_r` unsoundness](https://github.com/time-rs/time/issues/293)
* [Pure Rust implementation of `localtime_r`](https://github.com/x-hgg-x/tz-rs)
* [Interesting issue about TAI support in Chrono](https://github.com/chronotope/chrono/issues/21)
* [NIST leap seconds via FTP](ftp://ftp.boulder.nist.gov/pub/time/leap-seconds.list)
* [Interesting use case from dtolnay for `Date` type](https://github.com/chronotope/chrono/issues/820)
* [Desirable characteristics of time systems](https://www.ucolick.org/~sla/leapsecs/picktwo.html)
* [TC39 rejecting leap second handling](https://github.com/tc39/proposal-temporal/issues/54)
* [cctz philosophy](https://github.com/google/cctz#fundamental-concepts)
* [Russ Cox on "absolute" vs "civil" time](https://github.com/golang/go/issues/19700#issuecomment-559250634)
* [Javascript code for converting between TAI and Unix](https://github.com/qntm/t-a-i)
* [TC39 "Temporal"](https://tc39.es/proposal-temporal/docs/)
* [TC39 Polyfill](https://github.com/js-temporal/temporal-polyfill)
* [TC39 on non-standard IANA time zone suffix](https://tc39.es/proposal-temporal/docs/strings.html#iana-time-zone-names)
    * [Java's description of the same thing](https://docs.oracle.com/javase/8/docs/api/java/time/format/DateTimeFormatter.html#ISO_ZONED_DATE_TIME)
    * [Proposed RFC3339 Update](https://datatracker.ietf.org/wg/sedate/about/)
* [RFC 5545 (iCalendar) on date arithmetic](https://datatracker.ietf.org/doc/html/rfc5545#section-3.3.6)
    * [Previous section on datetime](https://datatracker.ietf.org/doc/html/rfc5545#section-3.3.5)
* [C++ Chrono Extension](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2018/p0355r7.html)
* [How gcc's libstdc++'s chrono library deals with leap seconds](https://github.com/gcc-mirror/gcc/blob/c1d1571329b4e0923a104b6139cd7db2f0aa1c1d/libstdc%2B%2B-v3/include/std/chrono#L3207)
    * [Some nice insight into C++ chrono's handling of leap seconds](https://stackoverflow.com/a/56620657)
* [Proleptic Gregorian Calendar](https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar)
* ["A Brief History of Leap Seconds"](https://www.youtube.com/watch?v=meK8dY9l_gE&t=9s)
* ["The Long, Painful History of Time"](https://naggum.no/lugm-time.html)
    * This has an interesting idea to use 2000-03-01 as the epoch.
* [TC39 "Temporal"](https://tc39.es/proposal-temporal/docs/)
* [Time zones](https://en.wikipedia.org/wiki/Time_zone)
* [TAI timezone with TC39 for leap seconds](https://github.com/ryzokuken/temporal-tai)
* [On missing leap second support in Luxon](https://github.com/moment/luxon/issues/1176)
* [JSR-310 and leap seconds](https://docs.oracle.com/javase/8/docs/api/java/time/Instant.html)
    * [`Clock` explicitly says leap seconds are usually ignored](https://docs.oracle.com/javase/8/docs/api/java/time/Clock.html)
    * [More on JDK not supporting leap seconds](https://stackoverflow.com/questions/30984599/how-does-the-oracle-java-jvm-know-a-leap-second-is-occurring)
    * [Time4J apparently handles leap seconds](https://github.com/MenoData/Time4J)
* [`time` Rust crate and leap seconds](https://github.com/time-rs/time/discussions/413)
* [ICU timezone detection](https://github.com/nodejs/node/blob/5d0a770c129c00e3942263b429f8efa4c42efba9/deps/icu-small/source/common/putil.cpp#L1065)
* [Low level date algorithms](http://howardhinnant.github.io/date_algorithms.html)
* [Howard Hinnat's C++ `date` library](https://github.com/howardhinnant/date)
* [CppCon 2015: Howard Hinnant “A C++14 approach to dates and times"](https://www.youtube.com/watch?v=tzyGjOm8AKo)
* ["Date Algorithms" by Peter Baum](https://www.researchgate.net/publication/316558298_Date_Algorithms)
* [A discussion about ranged integers in Rust](https://github.com/rust-lang/rfcs/issues/671)
* [A possibly simpler implementation of Temporal's rounding](https://github.com/fullcalendar/temporal-polyfill/blob/main/packages/temporal-polyfill/src/internal/round.ts)
* [On the naming of types in Temporal](https://github.com/unicode-org/icu4x/issues/2583#issuecomment-1251846194)
* [On time zone abbreviations](https://github.com/tc39/proposal-temporal/issues/1694)
* [Commit adding `chrono` to `libstdc++ in `gcc`](https://gcc.gnu.org/git/?p=gcc.git;a=commit;h=9fc61d45fa15fdd3b084d30998ecda164af33e95)
    * This also explains why only `tzdata.zi` is used.
* [Interesting case of (I think?) UB for a simple use of C++/Chrono](https://old.reddit.com/r/cpp/comments/l755me/stdchrono_question_of_the_day_whats_the_result_of/)
    * [See also Howard Hinnant's response about Chrono's ability to use different representations for different units.](https://old.reddit.com/r/cpp/comments/l755me/stdchrono_question_of_the_day_whats_the_result_of/hul90k4/)
    * Interestingly Hinnant does not seem to comment on the UB...
    * Oh, he does comment [here](https://old.reddit.com/r/cpp/comments/l755me/stdchrono_question_of_the_day_whats_the_result_of/gl6y9cg/).
    * And [here](https://old.reddit.com/r/cpp/comments/l755me/stdchrono_question_of_the_day_whats_the_result_of/gl8hmph/).
    * Yes yes, "henny penny" and chicken little, har har har. But I thought
    modern C++ was getting safer? LOL. Like I get what Howard is saying. It's
    hard to do any better given what C++ is today. But man, the self reflection
    (for C++ as a whole) is just missing from a lot (not all) discourse.
* [A Foundation to Sleep On](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2008/n2661.htm)
* [StackOverflow info on `timezone` tag](https://stackoverflow.com/tags/timezone/info)
    * This is (to me) surprisingly practical and useful.
* [Nice description of `TZ` env var](https://www.gnu.org/software/libc/manual/2.25/html_node/TZ-Variable.html)
* [Tricky handling of `GetDynamicTimeZoneInformation` on Windows](https://github.com/unicode-org/icu/blob/943b0ca31b38f5c7ba8d58c5f3d88d34c4ebff8d/icu4c/source/common/wintz.cpp#L63-L88)
* [SPICE on UTC/TAI/etc](https://naif.jpl.nasa.gov/pub/naif/toolkit_docs/FORTRAN/req/time.html#SPICE%20Time%20Representations)
* [Getting TAI time on Linux requires configuration](https://www.bortzmeyer.org/tai-on-debian.html)
* [Ten Python datetime pitfalls, and what libraries are (not) doing about it](https://dev.arie.bovenberg.net/blog/python-datetime-pitfalls/#1-incompatible-concepts-are-squeezed-into-one-class)
* ["Time, Clock, and Calendar Programming In C"](http://www.catb.org/esr/time-programming/)

Links with specific targeted info that might be useful:

* [`TZ` can be ambiguous](https://github.com/chronotope/chrono/issues/1153)
* [OpenWRT support in Chrono](https://github.com/chronotope/chrono/issues/1129)
* [Support for Android in Hinnant's C++ `date` library](https://github.com/HowardHinnant/date/pull/628)
* [`TZ` can be ambiguous](https://github.com/chronotope/chrono/issues/1153)
* [`tzdb` git repo](https://github.com/eggert/tz)
* [Interesting case for datetime difference with timezone](https://github.com/tc39/proposal-temporal/pull/2760#issuecomment-1965355111)
* [Finding 25-hour leap days. Do this with `jiff`!](https://typesandtimes.net/2024/02/kazakhstan-25-hour-leap-years)
* [Curious rounding bug.](https://github.com/tc39/proposal-temporal/issues/2790#issuecomment-1971250440)
* [Nice date arithmetic/rounding test cases](https://github.com/tc39/proposal-temporal/issues/998#issuecomment-716764012)
* [Specific use cases for duration rounding](https://github.com/tc39/proposal-temporal/issues/856)
* [Good test case for subtracting zoned times](https://github.com/tc39/proposal-temporal/pull/2760#issue-2103137194)
* Rounding:
    * [Proposal: Rounding method (and rounding for difference and toString) for non-Duration types](https://github.com/tc39/proposal-temporal/issues/827)
    * [Proposal: rounding and balancing for Duration type (replaces #789)](https://github.com/tc39/proposal-temporal/issues/856)
    * [Interesting case of rounding to months](https://github.com/tc39/proposal-temporal/issues/2535)
    * [difference should always return a "top-heavy balanced" duration with largest-first order of operations](https://github.com/tc39/proposal-temporal/issues/993#issuecomment-709711892)
    * [Inconsistent results in DifferenceISODate?](https://github.com/tc39/proposal-temporal/issues/2535)
    * [Discussion thread for resolution of weeks rounding bug](https://github.com/tc39/proposal-temporal/issues/2728)
* [Android's support for time zones appears weak](https://github.com/chronotope/chrono/pull/1018#issuecomment-1536311725)
* [Detecting system time zone (Rust/Chrono)](https://github.com/chronotope/chrono-tz/issues/13)
* [timestamp() doesn't match Display (Rust/Chrono)](https://github.com/chronotope/chrono/issues/318)
* [add/sub days (Rust/Chrono)](https://github.com/chronotope/chrono/pull/784)
* [Provide docs that do an audit of calendrical fallacies](https://yourcalendricalfallacyis.com/)
* [Relative duration rounding](https://github.com/tc39/proposal-temporal/issues/2792#issuecomment-2058186806)

Commentary on Rust datetime libraries
-------------------------------------
* [A comment thread on Chrono's API being complex.](https://old.reddit.com/r/rust/comments/18i8y39/learning_rust_my_experience_so_far_has_been_mixed/)
* [Chrono and locales](https://old.reddit.com/r/rust/comments/19cup9v/how_to_parse_datetime_in_locale_other_than_english/)

How to deal with the environment
--------------------------------
It seems there are at least 3 relevant environment variables? `TZ`, defined by
POSIX. Then there's [`TZDIR`](https://github.com/chronotope/chrono/issues/1265)
which is used by glibc. And then I think `ZONEINFO` is used by Go.

`TZ` is fine. I know how to deal with that. But what happens if both `TZDIR`
and `ZONEINFO` are defined?

It seems like [`TZDIR` is more broadly supported](https://man7.org/linux/man-pages/man8/tzselect.8.html).

I'm unsure of the origins of the `ZONEINFO` environment variable. Is this just
Go being a special snowflake?

It seems like we should ignore `ZONEINFO` but respect `TZDIR`. If users demand
it, we could fallback to `ZONEINFO`, but only if `TZDIR` is unset/empty.

How weeks are handled in rounding
---------------------------------
From: https://github.com/tc39/proposal-temporal/issues/827

Specifically: if largestUnit is 'month' or 'year' and smallestUnit is 'day' or
smaller, then weeks will always be zero and only days and/or months will be
included in the result. Edge cases that are NOT ambiguous are noted below.

7.7.1 If smallestUnit is 'week', then there is no ambiguity and any remainder
      will go into week.
7.7.2 If largestUnit is 'day', then there is no ambiguity because weeks are
      excluded and week will be zero.
7.7.3 In the degenerate case of { largestUnit: 'week', smallestUnit: 'day' }
      then there is also no ambiguity so both fields will be populated.

Names
-----

* `wheel`
* `gigawatt`
* `pend`
* `planck`
* `jiff`, `jiffy`


2024-02-28
----------
* I really don't like the name `jiff::Time`. I don't mind the name
`jiff::ZonedTime` (not yet defined), but `jiff::Time` and `jiff::civil::Time`
having the same type name is just super annoying. At first I thought it would
be fine since a `civil::Time` is basically never used, so who cares what it's
called since it's stuffed away in its own module. But a `civil::DateTime` will
very likely be used occasionally, and if we renamed `civil::Time` to, say,
`civil::Clock`, then the `civil::DateTime` name would no longer make much
sense. `civil::DateTime` is pretty much the canonical name for what it is,
so... we should leave it. And that means `civil::Time` stays. Which in turn
means we probably need a different name for `jiff::Time`. The most obvious
alternative is `jiff::Instant`, but this would be too confusing of a conflict
with `std::time::Instant`. *sigh* Other ideas: `TimePoint`, `AbsoluteTime`,
`TimeInstant`, `Point`, `Moment`. Bah. I want one word. And that word should
combine nicely with a `Zoned` prefix. UPDATE(2024-03-16): I ended up going with
`jiff::Instant` and `jiff::Zoned`. I'm still not 100% solid on those names,
but I haven't found an alternative that I like better. UPDATE(2024-06-26): I
ended up switching `Instant` to `Timestamp`. I think I would have stuck with
`Instant`, but the name conflict with `std::time::Instant` is just too
unfortunate. And having monotonicity being the main difference between them
is too subtle. I also still have `Zoned`. I like it immensely because it is
short, clear and one word. But... there's still something I don't like about
it. Not sure.

* We should probably balance `Span` values before returning them. See what the
`civil::Time` type currently returns for example. Just sticking to nanoseconds
and requiring users to explicitly round/balance is very likely to confuse them.
UPDATE(2024-03-16): Unfortunately, balancing by default means that sometimes
the ops won't be commutative, particularly for dates. We can balance times, but
nothing above the unit of "day."

* Add a cutesy API for easily building `Span` values. For example, perhaps
via a `ToSpan` trait, `2.hours() + 10.minutes()`. UPDATE(2024-03-16): Done, but
I'm still not 100% happy with it.

* We still need to figure out rounding in `Span` and how to deal with the
`relative-to` nonsense. I want to store it on the `Span`, but this could be
confusing at points. The alternative is to do what Temporal does and ask for
`relative-to` whenever rounding occurs. But this just... seems like overkill?
Temporal also allows one to pass the rounding options to most/all of the
date arithmetic methods, which is also something I really don't want to do.
UPDATE(2024-03-16): `relative-to` is only needed when rounding durations, so
we'll just allow users to provide it at that point. We also will not do any
rounding as part of computing spans in the first place, so we side-step needing
to deal with duration rounding complexity everywhere. This does mean users will
need to do duration rounding explicitly if they want it though, so this case
will be a bit more verbose/annoying than Temporal proper.

* We are otherwise getting pretty close to a point where we have most of the
fundamental pieces built. And now we just need to kind of put everything
together and start layering the timezone, parsing and formatting bullshit on
top of it. I had expected the base layers to require more code. Am I missing
anything? The rounding is potentially one big one, but it doesn't seem awful.
UPDATE(2024-03-16): No, rounding is awful. Saving that for when timezone stuff
is implemented.

* What about things like, "find the 4th Thursday in March 2024?" I think this
is just a matter of knowing what day a year began with. UPDATE(2024-03-16):
This is done. Along with "find the next Nth weekday."

* Do we need explicit millisecond and microsecond fields on `Span`? The
icky part is that they will be two additional `i64` values, which seems
very non-ideal. But if we don't have them, then do we still support
rounding/balancing them? I don't think we can, because then, e.g, milliseconds
and microseconds can't be "more." We have no real way to distinguish them
from one another. Sigh... UPDATE(2024-03-16): Yeah I just bit the bullet and
added them. If size of `Span` truly ends up being an issue, we could consider
limiting some fields to `i32` instead of `i64`, but ultimately it will be
pretty marginal. I generally don't think we can do much about `Span` being a
big type. Probably the work-around for this if it is a problem is to provide
alternative lower level APIs that operate on smaller types but aren't as
ergonomic.

* Add panicking variants of arithmetic via Add/Sub. UPDATE(2024-03-16): Done.

* Flush out the error types a bit more? UPDATE(2024-03-16): I've made
incremental progress here, but still not totally happy. The main issue at
present is that probably a lot of error messages aren't directly connected
to values given by callers. I'm not sure if we can do much better here
unfortunately.

* Settle on a TimeZone design. I've been thinking of having a TimeZoneDatabase
trait that `ZonedTime` is generic over (with a default type). The trait would
let you add timezones to it, and query it, and you would get `Copy` handles
back. The main complication is avoiding the need for time values to hold the
database itself. I want to keep times `Copy`. But this really constrains
the design of the time zone database and likely means every database has to
be a global that can never be freed. e.g., What happens when a `ZonedTime`
looks up a timezone handle that no longer exists? So we might just need to
accept that a `ZonedTime` is not `Copy`. We could make the timezone itself
a type parameter, and some timezones will be `Copy`, but this is a big
complication IMO and makes the API harder to understand. But note also that if
a `ZonedTime` is not `Copy`, and a `Span` will potentially hold a `ZonedTime`
via `relative_to`, then `Span` won't implement `Copy` either. No, `Span` will
not hold a `ZonedTime`, so the non-`Copy`ness of `Zoned` won't infect `Span`.

2024-03-16
----------
I'm thinking mostly about the timezone database design. At present, I think
making all timezones `Copy` is not in the cards. Specifically, a real timezone
has potentially lots of data associated with corresponding to DST transitions
(among potentially other kinds of transitions, but DST transitions are the
common case). That data is variable sized and cannot be `Copy`. Therefore, the
only real way to make it `Copy` is to stuff the data into a global database (or
one that is passed around) and put a handle in `Zoned` where the handle is just
an index into the database. But there are significant problems to this
approach:

* There's no real way to invalidate handles if the user wants to drop the
time zone database. So this design effectively requires that any time zone
database is global and can never be dropped.
* While we can likely button things up for the default case, this design also
means that if users use custom time zone databases, then they'll likely be
required to make sure they're passing in the right database when the handle
needs to be resolved. We could potentially work around this by pushing the
database into a type parameter on `Zoned`.
* In order to get information about a timezone for a handle, one has to go
to the database. We could potentially cache things like offsets in the high
bits of a handle, but whenever one needs to consult the timezone transitions
(which I think is needed for pretty much everything), we'd have to go to the
database. This is likely to be a problem because the database probably wants to
be mutable, so that we can update timezone data. This in turn means there could
be some gnarly synchronization involved here.

I overall felt like this was too much complication, particularly without
more user feedback. In theory, we could still make *some* values of `Zoned`
implement `Copy` by making it generic over a `TimeZone` trait. Then *some*
implementations of that trait (say, timezones that are just offsets) could
be `Copy`. The problem with this approach IMO is that it pushes folks toward
doing the wrong thing because using just the offset is likely to lead to
incorrect results because it doesn't deal with DST transitions. So then you
wind up in a situation where you have a "fast"-probably-wrong approach and a
"slow"-but-correct approach. This is especially quarrelsome because it can
impact code architecture where the former is more flexible given its `Copy`
impl while the latter is not.

So I think ultimately what we should do is define a concrete `TimeZone` type,
and a `Zoned` has an `Timestamp` and a `TimeZone`. And that's it. A `TimeZone`
type will be reference counted internally so that at least cloning is cheap.
The other possible advantage compared to the handle approach is that once a
`TimeZone` is constructed, it will never be mutated. Where as with the handle
approach, subsequent reads of the database could return different results if
the tzdata has changed on disk. The bummer here is using an `Arc` in the first
place, since cloning it could become a bottleneck when the `TimeZone` is shared
across multiple threads. But I'm not sure I really see a better approach here
that doesn't leak memory.

So if `TimeZone` is just an immutable reference counted type, that means more
of the interesting bits are off-loaded to the `TimeZoneDatabase`. Here's what
I'm thinking, with the docs here being more of an implementation sketch than
user-facing public docs.

```rust
/// Upon construction, the database may do some up-front work.
///
/// In the case of the binary IANA database commonly found in Unix
/// environments, this will traverse the directory structure to load
/// all available names of timezones. This is necessary in order to support
/// case insensitive timezone lookups. For example, in Go, time.LoadLocation
/// for `america/new_york` fails while `America/New_York` succeeds. Internally,
/// this will have a `RwLock<Map<Name, Result<TimeZone, Error>>>`.
///
/// In the case of a plain text IANA database, then the entire set of data
/// (hopefully one file via `tzdata.zi`) are loaded into memory since it
/// doesn't appear straight-forward to load timezones in an incremental
/// fashion. So in this case, we'd use a `Map<Name, TimeZone>`.
///
/// I think Android also uses a slightly different format here, so we might
/// need a third type of IANA, although I think it still ultimately uses the
/// same binary format but just compacted into one file.
///
/// We might implement a third option which uses Windows time zone data, but
/// from what I can tell, it's bunk. So I think we'll skip this one initially.
///
/// And I think this should also be "unavailable" with perhaps a message
/// indicating why.
pub struct TimeZoneDatabse;

impl TimeZoneDatabase {
    /// This tries to load a time zone database from the environmnet in a way
    /// that is likely to be correct. Here is what I'm thinking:
    ///
    /// 1. Respect `ZONEINFO` environment variable.
    /// 2. Use platform to look for binary iana database.
    /// ~~3. Use platform to look for plain text database.~~
    /// 4. Fall back to bundled tzdb if available.
    fn from_env() -> TimeZoneDatabase {
        todo!()
    }

    /// Creates a time zone database that reads a directory of binary IANA
    /// time zone files.
    fn from_iana_binary_path(
        dir: impl AsRef<Path>,
    ) -> Result<TimeZoneDatabase, Error> {
        todo!()
    }

    /// Creates a time zone database that reads from a single file containing
    /// the plain text IANA database. (e.g., `tzdata.zi`.)
    ///
    /// NOTE: I've scratched the text database support from initial release.
    fn from_iana_text_path(
        file: impl AsRef<Path>,
    ) -> Result<TimeZoneDatabase, Error> {
        todo!()
    }

    /// Creates a time zone database that reads from zero or more files
    /// containing the plain text IANA database. (e.g., `[northamerica,
    /// southamerica]`.)
    ///
    /// NOTE: I've scratched the text database support from initial release.
    fn from_iana_text_paths(
        files: impl IntoIterator<Item = impl AsRef<Path>>,
    ) -> Result<TimeZoneDatabase, Error> {
        todo!()
    }

    /// Creates a time zone database that reads from a single stream containing
    /// the plain text IANA database. (e.g., `tzdata.zi`.)
    ///
    /// NOTE: I've scratched the text database support from initial release.
    fn from_iana_text_reader(
        rdr: impl std::io::Read,
    ) -> Result<TimeZoneDatabase, Error> {
        todo!()
    }

    /// Returns a timezone corresponding to the given name. If one doesn't
    /// exist or if there was a problem loading it, then an error is returned.
    ///
    /// Depending on cache settings, this may reuse a previously loaded
    /// timezone for the given name. If caching is disabled or the previously
    /// loaded timezone has expired, then the timezone will be re-loaded.
    fn timezone(&self, name: &str) -> Result<TimeZone, Error> {
        todo!()
    }

    /// Sets the cache behavior of this timezone database.
    ///
    /// When the duration is zero, then no caching will be performed. Timezone
    /// lookups will always reload data from the underlying source.
    ///
    /// For the IANA binary database, "no caching" is straight-forward: we just
    /// always reload from disk.
    ///
    /// But for the plain text database, does this mean we read and parse the
    /// entire textual data every time? And when the cache is busted, is that
    /// what we do? There are pretty extreme differences here, which is why we
    /// have options to ensure one kind of database or the other.
    ///
    /// I think we should set a long default (1 day?) here since timezone data
    /// rarely changes. I'm thinking like one day? I suppose the problem is
    /// that when you update the timezone data, you'd ideally like for it to
    /// refreshed somewhat immediately. I suppose we can support that with
    /// `clear_cache`, although I could imagine that being annyoing. Maybe a
    /// shorter default TTL like 1 hour would be better?
    fn time_to_live(&self, duration: Span) {
        todo!()
    }

    /// This clears any cached timezones in this database.
    ///
    /// This guarantees that any subsequent lookups for a timezone will reload
    /// the data.
    fn clear_cache(&self) {
        todo!()
    }
}
```

tzdb bundling
-------------
Bundling tzdb within Jiff isn't a good idea because the database changes. And
it would be best if such changes didn't require re-compiling the library.

But, Windows doesn't have a system copy of tzdb. So it's worth bundling in
that case.

We'd therefore like to express a default feature of "bundle tzdb, but only on
platforms that probably need it." And also, "you shouldn't need to pay for
downloading or compiling this bundled copy if you don't need it." I believe
this requires the following setup:

```toml
[features]
default = ["tzdb-bundle-platform"]
tzdb-bundle-platform = ["dep:jiff-tzdb-platform"]
tzdb-bundle-always = ["dep:jiff-tzdb"]

[dependencies]
jiff-tzdb = { version = "0.1", path = "jiff-tzdb", optional = true }

[target.'cfg(windows)'.dependencies]
jiff-tzdb-platform = { version = "0.1", path = "jiff-tzdb-platform", optional = true }
```

And then make `jiff-tzdb-platform` a crate that literally just re-exports
`jiff-tzdb`. This is a bit odd, but I don't think I can accomplish the above
setup with just `jiff-tzdb`. The issue is that we need a platform-only
dependency to be enabled when `tzdb-bundle-platform` is enabled. That way, for
platforms that don't need it, enabling `tzdb-bundle-platform` is a no-op.

TAI support
-----------
I think I should add a `Tai` implementation of the `TimeScale` trait. I think
that it shouldn't be a simple "marker" type like `Unix` and should instead
carry the leap-second table with it. We can provide different ways of
constructing the leap-second table, e.g., from a `TimeZoneDatabase` or perhaps
a built-in copy or perhaps even from the text-file source itself. Once we have
the table and the `Tai` scale, then conversions can be done between `Unix` and
`Tai`. Once we have that, differences can be computed between `Timestamp`s that
are accurate.

Note though that the conversion is necessarily non-lossy. That is, some Unix
times can map to two distinct TAI times, and some Unix times might not even
exist for a given TAI time. (Although that latter case can only happen when a
negative leap second occurs, which has never happened yet.) So we'll need to
figure out how to handle those cases. I especially want to make them infallible
because these conversions happen in APIs that I otherwise want to be infallible
(like `Timestamp::to_datetime`). We could expose special fallible conversion
routines and otherwise do infallible conversions everywhere else. It's probably
fine?

In the case of a fold (positive leap second), we should pick the first, since
that's what things like RFC 5545 require and what Temporal does by clamping
`23:59:60` to `23:59:59`.

In the case of a gap (negative leap second), I think there is an unambiguous
mapping. That is, the straight-forward thing should just work? Either way, we
should be able to pretty easily write a test for it.

One other complication here is that we probably need to provide a way to build
an `Timestamp` straight from a `TAI` timestamp value. For example, from a
`clock_gettime(CLOCK_TAI, ...)` call.

Feedback from tweets
--------------------
See: https://twitter.com/burntsushi5/status/1763284928970572112
See: https://bsky.app/profile/burntsushi.net/post/3kmld45nj722o

> 1. want to be able to get a list of timestamps while specifying 3 out of 4 of
> these:
> - initial timestamp
> - final timestamp
> - dt
> - number of timestamps
>
> 2. want different options for "rounding" timestamps to different levels of
> precision (e.g. ceil/floor/round to month/year/etc)
>
> I am not a js user but I do a lot of time data processing in python. wrote
> this tooltime for the functionality I mention
> https://github.com/sslivkoff/tooltime?tab=readme-ov-file#create-standardized-timeperiods
>
> the get_standard_timeperiod() and get_standard_intervals() are the two
> functions that I havent been able to easily find in other libs
> (impl here
> https://github.com/sslivkoff/tooltime/blob/main/tooltime/timeperiod_utils/timeperiod_standard.py)
>
> basically making it easy to 1) put messy realworld timestamps into regular
> intervals, and 2) being able to easily generate regular intervals under
> different parameterizations
>
> oh thats awesome!!!
>
> love the modes. probably more than I would ever need with all those half-X
> roudingMode's. and not sure the use of largestUnit
>
> roundingIncrement would be very nice

> Mostly just easy integration. My biggest pain point was trying to get them to
> work with Serde. It's been a while, but it ended up being easier to just make
> my own Date type rather than dealing with the errors. Having one DateTime
> across crates (Serde, Polars etc.) would be nice.

> Don't panic. Use rust's error handling. We've fought chrono panics for a
> while on @nu_shell, mostly because of cross-platform oddball file system or
> file corruption but also things like Windows named pipe dates of 1/1/1601,
> IIRC.
>
> Here's another one while I'm dreaming. :) Precise datetime math that includes
> leap calculations but take it a step further and allow the result to be
> expressed in a human readable duration that includes decades, years, months,
> weeks, days, hours, minutes, seconds, etc.

> Here's a real answer that I had a professional need for a few years ago: a
> natural language-agnostic syntax tree for complicated date/time expressions,
> e.g. "the day after next Friday" => DayDelta(NextWeekday(Now, Friday), 1)

> Clear documentation which representation is used for what. datetime libraries
> naturally have to deal with different representations of similar things, that
> is just essential complexity. 1/2
>
> If you add a ton of similar things that are are either just marginally useful
> or legacy you end up in chaos. I'm looking at you Java.
>
> Yes, java.time is good and I realize that what I want is kind of a xkcd/927
> problem that cannot be solved by a library alone. What I wish for a library
> is that it does not pretend to be the only datetime library in existence, but
> acknowledges the fact that there are others.
>
> To stay with the Java example: Clearly say in the documentation, why
> http://java.date.Instance is always better than http://java.util.Date and
> what to do if you have to deal with http://java.util.Date for legacy reasons.
>
> (In my opinion http://java.util.Date should be deprecated completely, but it
> isn't. That would send a clear message and prevent a lot of confusion. With
> java.time being part of the standard we could have done it. Not in the power
> of a new library, though.)
>
> Also, java.time can keep its API surface minimal by strictly committing to
> immutable and thread-safe while completely disregarding performance. Not sure
> if we could get away with this in Rust.

> Consistent use of enums for weekdays / months without needing to use u8

> Date, DateTime, DateTimeMs to represent different resolutions. I wrote my
> own code for this (internal to a project) to keep the complexity down and
> make the API coder friendly. I only needed UNIX GMT time. A date-time crate
> doesn't have to be hard, but they seem to make it hard
>
> Yes, UNIX time in seconds, plus milliseconds. Really I'm just improvising
> these types as I need them. I needed "round up" and "round down" calls
> for N years, quarters, months, weeks, days, hours etc. I found chrono
> overcomplicated, overengineered and awkward. Life is short

> Doing the simple things seems unreasonably hard with Chrono. I shouldn't have
> to constantly look up the syntax for getting the current timestamp

> Strict definition of the output of the Display trait and it being trivial
> to parse.

> Julian/ordinal dates and easy conversion from SAS date, time, and datetime
> types, please

> Configurable precision to reduce on memory consumption in no_std/embedded
> devices. Chrono's Duration is i64 + u32. Cc @thibautvandv

> I would say TC39 Temporal but in Rust. But it seems you are already aware of
> it.

> Currently, calculating the difference in days between two
> dates (e.g., implementing the std::ops::Sub trait for
> chrono::NaiveDate) requires borrowing the special date calculation
> algorithm from the C++20 extension to the std::chrono library
> (https://howardhinnant.github.io/date_algorithms.html#days_from_civil).

> Easier formatting and parsing. It always takes google to solve.

> I think something such as thread time recorder, meaning that can record the
> execution time of a thread and maybe only of that thread, so that we may not
> need to use threadlocal types directly.
>
> I believe that would be a great addition, but just said that felt maybe
> relevant here.
>
> The reason I said that here is because recording time atomically from a time
> object itself can be highly convenient wrapper if given.

> I don't have a use case, but I watched a talk related to Joda time that made
> me excited about the challenge of domain modelling durations and periods with
> variable resolution as to work well for fuzzy human time like "in about 5
> minutes" is encoded as specific date with error

> Not be terribly over-engineered and make common use-cases available in
> <1 minute of reading doc. Reuse std::time::Duration instead of rolling a
> separate type. Make working with unix-timestamps comfy: they are everywhere
> and expecting to change that is unrealistic.
