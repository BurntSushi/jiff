use wasm_bindgen_test::*;

macro_rules! eprintln {
    ($($tt:tt)*) => {{
        let s = std::format!($($tt)*);
        web_sys::console::log_1(&s.into());
    }}
}

#[wasm_bindgen_test]
fn zoned_now_no_panic() {
    let zdt = jiff::Zoned::now();
    eprintln!("{zdt}");
}

// Not sure if this is needed? ---AG
pub fn set_panic_hook() {
    // When the `console_error_panic_hook` feature is enabled, we can call the
    // `set_panic_hook` function at least once during initialization, and then
    // we will get better error messages if our code ever panics.
    //
    // For more details see
    // https://github.com/rustwasm/console_error_panic_hook#readme
    console_error_panic_hook::set_once();
}
