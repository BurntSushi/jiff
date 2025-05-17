This tests that Jiff falls back to the special `Etc/Unknown` time zone when the
`TZ` environment variable is set to a non-empty and invalid value. This also
checks that a set but empty `TZ` environment variable is indistinguishable from
`TZ=UTC` (which follows existing convention for GNU and BSD implementations of
POSIX `date`).

See [#364](https://github.com/BurntSushi/jiff/issues/364) for discussion about
this behavior.
