/*!
TODO

# Precise details of format

Here is a grammar of the supported format for "friendly" time durations.

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
direction = 'ago'
comma = ',' ws
ws =
    U+0020 SPACE
    | U+0009 HORIZONTAL TAB
    | U+000A LINE FEED
    | U+000C FORM FEED
    | U+000D CARRIAGE RETURN
```
*/

pub use self::{
    parser::SpanParser,
    printer::{Designator, Direction, FractionalUnit, Spacing, SpanPrinter},
};

mod parser;
mod printer;
