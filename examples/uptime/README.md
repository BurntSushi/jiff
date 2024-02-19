This example shows how to parse the output of `uptime` on Unix and determine
when the system booted. This demonstrates regex parsing, fallible construction
of spans, zone aware arithmetic and rounding.

To run this program, use:

```
$ uptime | cargo run -qp uptime
2024-06-28T08:08:00-04:00[America/New_York]
```

If you don't have `uptime`, then you can pipe in data that looks like it came
from `uptime`:

```
$ echo '14:00:47 up 12 days,  5:53' | cargo run -qp uptime
2024-06-28T08:08:00-04:00[America/New_York]
```
