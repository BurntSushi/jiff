use jiff::{
    Error, civil,
    fmt::{
        Write,
        strtime::{BrokenDownTime, Config, Custom, Extension},
    },
};

#[cfg(feature = "alloc")]
#[test]
fn custom_trait_object() {
    struct CustomDate<'a>(&'a str);

    impl Custom for CustomDate<'_> {
        fn format_date(
            &self,
            _config: &Config<dyn Custom + '_>,
            _ext: &Extension,
            _tm: &BrokenDownTime<'_>,
            wtr: &mut dyn Write,
        ) -> Result<(), Error> {
            wtr.write_str(self.0)
        }
    }

    let formatted = String::from("a dynamically formatted date");
    let config = Config::new().custom(CustomDate(&formatted));
    let config: &Config<dyn Custom + '_> = &config;
    let tm = BrokenDownTime::from(civil::date(2025, 7, 1));
    assert_eq!(tm.to_string_with_config(config, "%x").unwrap(), formatted);
}

#[cfg(feature = "alloc")]
#[test]
fn broken_down_time_into_owned() {
    if jiff::tz::db().is_definitively_empty() {
        return;
    }

    let tm: BrokenDownTime<'static> = {
        let zdt = civil::date(2024, 7, 15)
            .at(16, 24, 59, 0)
            .in_tz("America/New_York")
            .unwrap();
        let tm = BrokenDownTime::from(&zdt);
        assert_eq!(tm.to_string("%Q %Z").unwrap(), "America/New_York EDT");
        tm.into_owned()
    };
    assert_eq!(tm.to_string("%Q %Z").unwrap(), "America/New_York EDT");
}
