//! FFI bindings to the Windows function and types used to acquire timezone information

pub const TIME_ZONE_ID_INVALID: u32 = 4294967295;

#[repr(C)]
struct SYSTEMTIME {
    year: u16,
    month: u16,
    day_of_week: u16,
    day: u16,
    hour: u16,
    minute: u16,
    seconds: u16,
    milliseconds: u16,
}

#[repr(C)]
pub(super) struct DYNAMIC_TIME_ZONE_INFORMATION {
    bias: i32,
    standard_name: [u16; 32],
    standard_date: SYSTEMTIME,
    standard_bias: i32,
    daylight_name: [u16; 32],
    daylight_date: SYSTEMTIME,
    daylight_bias: i32,
    /// This is the only field actually read by jiff
    pub(super) timezone_key_name: [u16; 128],
    dynamic_daylight_time_disabled: u8,
}

#[link(name = "kernel32", kind = "raw-dylib")]
unsafe extern "system" {
    /// Retrieves the current time zone and dynamic daylight saving time settings.
    ///
    /// These settings control the translations between Coordinated Universal Time (UTC) and local time.
    ///
    /// <https://learn.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-getdynamictimezoneinformation>
    pub(super) unsafe fn GetDynamicTimeZoneInformation(
        info: *mut DYNAMIC_TIME_ZONE_INFORMATION,
    ) -> u32;
}
