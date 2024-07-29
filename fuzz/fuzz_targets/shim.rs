use std::{
    error::Error,
    ffi::c_int,
    {env, fs, ptr},
};

extern "C" {
    // Initializer provided by libfuzzer-sys for creating an
    // appropriate panic hook.
    fn LLVMFuzzerInitialize(
        argc: *const isize,
        argv: *const *const *const u8,
    ) -> c_int;

    // This is a magic function defined by libfuzzer-sys; use for replay.
    #[allow(improper_ctypes)]
    fn rust_fuzzer_test_input(input: &[u8]) -> i32;
}

#[allow(unused)]
pub fn main() -> Result<(), Box<dyn Error>> {
    let mut count = 0usize;
    unsafe {
        let _ = LLVMFuzzerInitialize(ptr::null(), ptr::null());
    }
    for testcase in env::args_os().skip(1) {
        let content = fs::read(testcase)?;
        unsafe {
            let _ = rust_fuzzer_test_input(&content);
        }
        count += 1;
    }
    println!("Executed {count} testcases successfully!");
    if count == 0 {
        println!("Did you mean to specify a testcase?");
    }
    Ok(())
}

#[macro_export]
macro_rules! maybe_define_main {
    () => {
        #[cfg(not(fuzzing))]
        fn main() {
            let _ = $crate::shim::main();
        }
    };
}
