/*!
This crate provides macros for defining `static` data structures for Jiff.

The macros in this crate are re-exported in the [`jiff::tz`] sub-module.
Users should _not_ depend on this crate directly or import from it. Instead,
enable the `static` or `static-tz` features of Jiff and use the re-exports in
`jiff::tz`.

At present, the macros in this crate are limited to creating `TimeZone`
in a `const` context. This works by reading TZif data (e.g., from
`/usr/share/zoneinfo/America/New_York` or from [`jiff-tzdb`]) at compile
time and generating Rust source code that builds a `TimeZone`.

# Documentation

The macros defined in this crate are documented on their corresponding
re-exports in Jiff:

* `get` is documented at [`jiff::tz::get`].
* `include` is documented at [`jiff::tz::include`].

# Compatibility

The APIs required to build a `TimeZone` in a `const` context are exposed by
Jiff but not part of Jiff's public API for the purposes of semver (and do not
appear in `rustdoc`). The only guarantee provided by `jiff` and `jiff-static`
is that there is exactly one version of `jiff` that `jiff-static` works with.
Conventionally, this is indicated by the exact same version string. That is,
`jiff-static 0.2.2` is only guaranteed to work with `jiff 0.2.2`.

This compatibility constraint is managed by Jiff, so that you should never
need to worry about it. In particular, users should never directly depend on
this crate. Everything should be managed through the `jiff` crate.

[`jiff-tzdb`]: https://docs.rs/jiff-tzdb
[`jiff::tz`]: https://docs.rs/jiff/0.2/jiff/tz/index.html
[`jiff::tz::get`]: https://docs.rs/jiff/0.2/jiff/tz/macro.get.html
[`jiff::tz::include`]: https://docs.rs/jiff/0.2/jiff/tz/macro.include.html
*/

extern crate alloc;
extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;

use self::shared::{
    PosixDay, PosixDayTime, PosixDst, PosixRule, PosixTimeZone, TzifFixed,
    TzifIndicator, TzifLocalTimeType, TzifOwned, TzifTransition,
};

/// A bundle of code copied from `src/shared`.
///
/// The main thing we use in here is the parsing routine for TZif data and
/// shared data types for representing TZif data.
mod shared;

// Public API docs are in Jiff.
#[proc_macro]
pub fn include(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as Include);
    proc_macro::TokenStream::from(input.quote())
}

// Public API docs are in Jiff.
#[cfg(feature = "tzdb")]
#[proc_macro]
pub fn get(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as Get);
    proc_macro::TokenStream::from(input.quote())
}

/// The entry point for the `include!` macro.
#[derive(Debug)]
struct Include {
    tzif: TzifOwned,
}

impl Include {
    fn from_path_only(path: &str) -> Result<Include, String> {
        const NEEDLE: &str = "zoneinfo/";

        let Some(zoneinfo) = path.rfind(NEEDLE) else {
            return Err(format!(
                "could not extract IANA time zone identifier from \
                 file path `{path}` \
                 (could not find `zoneinfo` in path), \
                 please provide IANA time zone identifier as second \
                 parameter",
            ));
        };
        let idstart = zoneinfo.saturating_add(NEEDLE.len());
        let id = &path[idstart..];
        Include::from_path_with_id(id, path)
    }

    fn from_path_with_id(id: &str, path: &str) -> Result<Include, String> {
        let id = id.to_string();
        let data = std::fs::read(path)
            .map_err(|e| format!("failed to read {path}: {e}"))?;
        let tzif = TzifOwned::parse(Some(id.clone()), &data).map_err(|e| {
            format!("failed to parse TZif data from {path}: {e}")
        })?;
        Ok(Include { tzif })
    }

    fn quote(&self) -> proc_macro2::TokenStream {
        self.tzif.quote()
    }
}

impl syn::parse::Parse for Include {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Include> {
        let lit1 = input.parse::<syn::LitStr>()?.value();
        if !input.lookahead1().peek(syn::Token![,]) {
            return Ok(
                Include::from_path_only(&lit1).map_err(|e| input.error(e))?
            );
        }
        input.parse::<syn::Token![,]>()?;
        if input.is_empty() {
            return Ok(
                Include::from_path_only(&lit1).map_err(|e| input.error(e))?
            );
        }
        let lit2 = input.parse::<syn::LitStr>()?.value();
        // Permit optional trailing comma.
        if input.lookahead1().peek(syn::Token![,]) {
            input.parse::<syn::Token![,]>()?;
        }
        Ok(Include::from_path_with_id(&lit2, &lit1)
            .map_err(|e| input.error(e))?)
    }
}

/// The entry point for the `get!` macro.
#[cfg(feature = "tzdb")]
#[derive(Debug)]
struct Get {
    tzif: TzifOwned,
}

#[cfg(feature = "tzdb")]
impl Get {
    fn from_id(id: &str) -> Result<Get, String> {
        let (id, data) = jiff_tzdb::get(id).ok_or_else(|| {
            format!("could not find time zone `{id}` in bundled tzdb")
        })?;
        let id = id.to_string();
        let tzif = TzifOwned::parse(Some(id.clone()), &data).map_err(|e| {
            format!("failed to parse TZif data from bundled `{id}`: {e}")
        })?;
        Ok(Get { tzif })
    }

    fn quote(&self) -> proc_macro2::TokenStream {
        self.tzif.quote()
    }
}

#[cfg(feature = "tzdb")]
impl syn::parse::Parse for Get {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Get> {
        let lit1 = input.parse::<syn::LitStr>()?.value();
        if input.lookahead1().peek(syn::Token![,]) {
            input.parse::<syn::Token![,]>()?;
        }
        Ok(Get::from_id(&lit1).map_err(|e| input.error(e))?)
    }
}

// Everything below at this point is quasi-quoting the `shared` data type
// values into `static` data structures as Rust source code.

impl TzifOwned {
    fn quote(&self) -> proc_macro2::TokenStream {
        let fixed = self.fixed.quote();
        let types = self.types.iter().map(TzifLocalTimeType::quote);
        let mut transitions = vec![];
        for (i, this) in self.transitions.iter().enumerate() {
            let prev = &self.transitions[i.saturating_sub(1)];
            let prev_offset = self.types[usize::from(prev.type_index)].offset;
            let this_offset = self.types[usize::from(this.type_index)].offset;
            transitions.push(this.quote(prev_offset, this_offset));
        }
        quote! {
            {
                static TZ: jiff::tz::TimeZone =
                    jiff::tz::TimeZone::__internal_from_tzif(
                        &#fixed.to_jiff(&[#(#types),*], &[#(#transitions),*])
                    );
                // SAFETY: Since we are guaranteed that the `TimeZone` is
                // constructed above as a static TZif time zone, it follows
                // that it is safe to memcpy's its internal representation.
                //
                // NOTE: We arrange things this way so that `jiff::tz::get!`
                // can be used "by value" in most contexts. Basically, we
                // "pin" the time zone to a static so that it has a guaranteed
                // static lifetime. Otherwise, since `TimeZone` has a `Drop`
                // impl, it's easy to run afoul of this and have it be dropped
                // earlier than you like. Since this particular variant of
                // `TimeZone` can always be memcpy'd internally, we just do
                // this dance here to save the user from having to write out
                // their own `static`.
                //
                // NOTE: It would be nice if we could make this `copy` routine
                // safe, or at least panic if it's misused. But to do that, you
                // need to know the time zone variant. And to know the time
                // zone variant, you need to "look" at the tag in the pointer.
                // And looking at the address of a pointer in a `const` context
                // is precarious.
                unsafe { TZ.copy() }
            }
        }
    }
}

impl TzifFixed<String> {
    fn quote(&self) -> proc_macro2::TokenStream {
        let TzifFixed {
            ref name,
            version,
            checksum,
            ref designations,
            ref posix_tz,
        } = *self;
        let name = name.as_ref().unwrap();
        let posix_tz = posix_tz
            .as_ref()
            .map(|tz| {
                let tz = tz.quote();
                quote!(Some(#tz))
            })
            .unwrap_or_else(|| quote!(None));
        quote! {
            jiff::shared::TzifFixed {
                name: Some(#name),
                version: #version,
                checksum: #checksum,
                designations: #designations,
                posix_tz: #posix_tz,
            }
        }
    }
}

impl TzifLocalTimeType {
    fn quote(&self) -> proc_macro2::TokenStream {
        let TzifLocalTimeType {
            offset,
            is_dst,
            ref designation,
            ref indicator,
        } = *self;
        let desig_start = designation.0;
        let desig_end = designation.1;
        let indicator = indicator.quote();
        quote! {
            jiff::shared::TzifLocalTimeType {
                offset: #offset,
                is_dst: #is_dst,
                designation: (#desig_start, #desig_end),
                indicator: #indicator,
            }.to_jiff()
        }
    }
}

impl TzifIndicator {
    fn quote(&self) -> proc_macro2::TokenStream {
        match *self {
            TzifIndicator::LocalWall => quote! {
                jiff::shared::TzifIndicator::LocalWall
            },
            TzifIndicator::LocalStandard => quote! {
                jiff::shared::TzifIndicator::LocalStandard
            },
            TzifIndicator::UTStandard => quote! {
                jiff::shared::TzifIndicator::UTStandard
            },
        }
    }
}

impl TzifTransition {
    fn quote(
        &self,
        prev_offset: i32,
        this_offset: i32,
    ) -> proc_macro2::TokenStream {
        let TzifTransition { timestamp, type_index } = *self;
        quote! {
            jiff::shared::TzifTransition {
                timestamp: #timestamp,
                type_index: #type_index,
            }.to_jiff(#prev_offset, #this_offset)
        }
    }
}

impl PosixTimeZone<String> {
    fn quote(&self) -> proc_macro2::TokenStream {
        let PosixTimeZone { ref std_abbrev, std_offset, ref dst } = *self;
        let dst = dst
            .as_ref()
            .map(|dst| {
                let dst = dst.quote();
                quote!(Some(#dst))
            })
            .unwrap_or_else(|| quote!(None));
        quote! {
            jiff::shared::PosixTimeZone {
                std_abbrev: #std_abbrev,
                std_offset: #std_offset,
                dst: #dst,
            }
        }
    }
}

impl PosixDst<String> {
    fn quote(&self) -> proc_macro2::TokenStream {
        let PosixDst { ref abbrev, offset, ref rule } = *self;
        let rule = rule
            .as_ref()
            .map(|r| {
                let r = r.quote();
                quote!(Some(#r))
            })
            .unwrap_or_else(|| quote!(None));
        quote! {
            jiff::shared::PosixDst {
                abbrev: #abbrev,
                offset: #offset,
                rule: #rule,
            }
        }
    }
}

impl PosixRule {
    fn quote(&self) -> proc_macro2::TokenStream {
        let start = self.start.quote();
        let end = self.end.quote();
        quote! {
            jiff::shared::PosixRule { start: #start, end: #end }
        }
    }
}

impl PosixDayTime {
    fn quote(&self) -> proc_macro2::TokenStream {
        let PosixDayTime { ref date, time } = *self;
        let date = date.quote();
        quote! {
            jiff::shared::PosixDayTime { date: #date, time: #time }
        }
    }
}

impl PosixDay {
    fn quote(&self) -> proc_macro2::TokenStream {
        match *self {
            PosixDay::JulianOne(day) => quote! {
                jiff::shared::PosixDay::JulianOne(#day)
            },
            PosixDay::JulianZero(day) => quote! {
                jiff::shared::PosixDay::JulianZero(#day)
            },
            PosixDay::WeekdayOfMonth { month, week, weekday } => quote! {
                jiff::shared::PosixDay::WeekdayOfMonth {
                    month: #month,
                    week: #week,
                    weekday: #weekday,
                }
            },
        }
    }
}
