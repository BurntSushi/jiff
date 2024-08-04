/*!
A bespoke but easy to read format for [`Span`](crate::Span) and
[`SignedDuration`](crate::SignedDuration).

# Motivation

This format was devised, in part, because the standard duration interchange
format specified by [Temporal's ISO 8601 definition](super::temporal) is
sub-optimal in two important respects:

1. It doesn't support individual sub-second components.
2. It is difficult to read.

In the first case, ISO 8601 durations do support sub-second components, but are
only expressible as fractional seconds. For example:

```text
PT1.100S
```

This is problematic in some cases because it doesn't permit distinguishing
between some spans. For example, `1.second().milliseconds(100)` and
`1100.milliseconds()` both serialize to the same ISO 8601 duration as shown
above. At deserialization time, it's impossible to know what the span originally
looked like. Thus, using the ISO 8601 format means the serialization and
deserialization of [`Span`](crate::Span) values is lossy.

In the second case, ISO 8601 durations appear somewhat difficult to quickly
read. For example:

```text
P1Y2M3DT4H59M1.1S
P1y2m3dT4h59m1.1S
```

When all of the unit designators are capital letters in particular, everything
runs together and it's hard for the eye to distinguish where digits stop and
letters begin. Using lowercase letters for unit designators helps somewhat,
but this is an extension to ISO 8601 that isn't broadly supported.

The "friendly" format resolves both of these problems by permitting sub-second
components and allowing the use of whitespace and longer unit designator labels
to improve readability. For example, all of the following are equivalent and
will parse to the same `Span`:

```text
1y 2mo 3d 4h 59m 1100ms
1 year 2 months 3 days 4h59m1100ms
1 year, 2 months, 3 days, 4h59m1100ms
1 year, 2 months, 3 days, 4 hours 59 minutes 1100 milliseconds
```

At the same time, the friendly format continues to support fractional
time components since they may be desirable in some cases. For example, both
of the following are equivalent:

```text
1h 1m 1.5s
01:01:01.5
```

The idea with the friendly format is that end users who know how to write
English durations are happy to both read and write durations in this format.
And moreover, the format is flexible enough that end users generally don't need
to stare at a grammar to figure out how to write a valid duration. Most of the
intuitive things you'd expect to work will work.

# Grammar

This section gives a more precise description of the "friendly" duration format
in the form of a grammar.

```text
format =
    format-signed-hms
    | format-signed-designator

format-signed-hms =
    sign? format-hms

format-hms =
    [0-9]+ ':' [0-9]+ ':' [0-9]+ fractional?

format-signed-designator =
    sign? format-designator-units
    | format-designator-units direction?
format-designator-units =
    years
    | months
    | weeks
    | days
    | hours
    | minutes
    | seconds
    | milliseconds
    | microseconds
    | nanoseconds

# This dance below is basically to ensure a few things:
# First, that at least one unit appears. That is, that
# we don't accept the empty string. Secondly, when a
# fractional component appears in a time value, we don't
# allow any subsequent units to appear. Thirdly, that
# `HH:MM:SS[.f{1,9}]?` is allowed after years, months,
# weeks or days.
years =
    unit-value unit-years comma? ws* format-hms
    | unit-value unit-years comma? ws* months
    | unit-value unit-years comma? ws* weeks
    | unit-value unit-years comma? ws* days
    | unit-value unit-years comma? ws* hours
    | unit-value unit-years comma? ws* minutes
    | unit-value unit-years comma? ws* seconds
    | unit-value unit-years comma? ws* milliseconds
    | unit-value unit-years comma? ws* microseconds
    | unit-value unit-years comma? ws* nanoseconds
    | unit-value unit-years
months =
    unit-value unit-months comma? ws* format-hms
    | unit-value unit-months comma? ws* weeks
    | unit-value unit-months comma? ws* days
    | unit-value unit-months comma? ws* hours
    | unit-value unit-months comma? ws* minutes
    | unit-value unit-months comma? ws* seconds
    | unit-value unit-months comma? ws* milliseconds
    | unit-value unit-months comma? ws* microseconds
    | unit-value unit-months comma? ws* nanoseconds
    | unit-value unit-months
weeks =
    unit-value unit-weeks comma? ws* format-hms
    | unit-value unit-weeks comma? ws* days
    | unit-value unit-weeks comma? ws* hours
    | unit-value unit-weeks comma? ws* minutes
    | unit-value unit-weeks comma? ws* seconds
    | unit-value unit-weeks comma? ws* milliseconds
    | unit-value unit-weeks comma? ws* microseconds
    | unit-value unit-weeks comma? ws* nanoseconds
    | unit-value unit-weeks
days =
    unit-value unit-days comma? ws* format-hms
    | unit-value unit-days comma? ws* hours
    | unit-value unit-days comma? ws* minutes
    | unit-value unit-days comma? ws* seconds
    | unit-value unit-days comma? ws* milliseconds
    | unit-value unit-days comma? ws* microseconds
    | unit-value unit-days comma? ws* nanoseconds
    | unit-value unit-days
hours =
    unit-value unit-hours comma? ws* minutes
    | unit-value unit-hours comma? ws* seconds
    | unit-value unit-hours comma? ws* milliseconds
    | unit-value unit-hours comma? ws* microseconds
    | unit-value unit-hours comma? ws* nanoseconds
    | unit-value fractional? ws* unit-hours
minutes =
    unit-value unit-minutes comma? ws* seconds
    | unit-value unit-minutes comma? ws* milliseconds
    | unit-value unit-minutes comma? ws* microseconds
    | unit-value unit-minutes comma? ws* nanoseconds
    | unit-value fractional? ws* unit-minutes
seconds =
    unit-value unit-seconds comma? ws* milliseconds
    | unit-value unit-seconds comma? ws* microseconds
    | unit-value unit-seconds comma? ws* nanoseconds
    | unit-value fractional? ws* unit-seconds
milliseconds =
    unit-value unit-milliseconds comma? ws* microseconds
    | unit-value unit-milliseconds comma? ws* nanoseconds
    | unit-value fractional? ws* unit-milliseconds
microseconds =
    unit-value unit-microseconds comma? ws* nanoseconds
    | unit-value fractional? ws* unit-microseconds
nanoseconds =
    unit-value fractional? ws* unit-nanoseconds

unit-value = [0-9]+ [ws*]
unit-years = 'years' | 'year' | 'yrs' | 'yr' | 'y'
unit-months = 'months' | 'month' | 'mos' | 'mo'
unit-weeks = 'weeks' | 'week' | 'wks' | 'wk' | 'w'
unit-days = 'days' | 'day' | 'd'
unit-hours = 'hours' | 'hour' | 'hrs' | 'hr' | 'h'
unit-minutes = 'minutes' | 'minute' | 'mins' | 'min' | 'm'
unit-seconds = 'seconds' | 'second' | 'secs' | 'sec' | 's'
unit-milliseconds =
    'milliseconds'
    | 'millisecond'
    | 'millis'
    | 'milli'
    | 'msecs'
    | 'msec'
    | 'ms'
unit-microseconds =
    'microseconds'
    | 'microsecond'
    | 'micros'
    | 'micro'
    | 'usecs'
    | 'usec'
    | 'µ' (U+00B5 MICRO SIGN) 'secs'
    | 'µ' (U+00B5 MICRO SIGN) 'sec'
    | 'us'
    | 'µ' (U+00B5 MICRO SIGN) 's'
unit-nanoseconds =
    'nanoseconds' | 'nanosecond' | 'nanos' | 'nano' | 'nsecs' | 'nsec' | 'ns'

fractional = decimal-separator decimal-fraction
decimal-separator = '.' | ','
decimal-fraction = [0-9]{1,9}

sign = '+' | '-'
direction = ws 'ago'
comma = ',' ws
ws =
    U+0020 SPACE
    | U+0009 HORIZONTAL TAB
    | U+000A LINE FEED
    | U+000C FORM FEED
    | U+000D CARRIAGE RETURN
```

One thing not specified by the grammar above are maximum values. Namely,
there are no specific maximum values imposed for each individual unit, nor
a maximum value for the entire duration (say, when converted to nanoseconds).
Instead, implementations are expected to impose their own limitations.

For Jiff, a `Span` is more limited than a `SignedDuration`. For example, a the
year component of a `Span` is limited to `[-19,999, 19,999]`. In contrast,
a `SignedDuration` is a 96-bit signed integer number of nanoseconds with no
particular limits on the individual units. They just can't combine to something
that overflows a 96-bit signed integer number of nanoseconds. (And parsing into
a `SignedDuration` directly only supports units of hours or smaller, since
bigger units do not have an invariant length.) In general, implementations
should support a "reasonable" range of values.
*/

pub use self::{
    parser::SpanParser,
    printer::{Designator, Direction, FractionalUnit, Spacing, SpanPrinter},
};

/// The default span/duration parser that we use.
pub(crate) static DEFAULT_SPAN_PARSER: SpanParser = SpanParser::new();

/// The default span/duration printer that we use.
pub(crate) static DEFAULT_SPAN_PRINTER: SpanPrinter = SpanPrinter::new();

mod parser;
mod printer;
