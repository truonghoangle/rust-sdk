# Translation blockers of the elicitation schema builders (X01–X75) and the missing float types

Status: **worked around** by translation patch 08 (`formal/trusted/patches/08-elicitation-schema.patch`,
human decision XD1) and by the `F64`/`F32` carriers with `autoImplicit = false` (human decision
XD3, 2026-11-28). **No upstream issue filed** as of 2026-11-28; the drafts below are not filed.
Measured 2026-11-28 with Aeneas `nightly-2026.11.24-fb44cb4` (`formal/lakefile.toml`), Charon
0.1.324, Rust `nightly-2026-09-17`, Lean `v4.36.0`. The crate measurements translate the copy of
upstream `7caec76` with patches 01–07 (`scripts/apply-patches.sh`), one target at a time
(`start_from` = that target), with the options of `scripts/aeneas-translate.sh`. The standalone
reproducers are one-file crates (`[package] name = "repro"`, `edition = "2024"`, an empty
`[workspace]`), translated with `charon cargo --preset=aeneas --start-from "repro::<fn>"` and
`aeneas -backend lean -split-files`; their sources are below (the scratch directories that held
them are not kept).

## Issue 1: `f32`/`f64` are printed as `F32`/`F64`, which the Aeneas library does not define

**Effect here.** `Rmcp.Types` uses `F32` (`model.annotated.Annotations.priority : Option F32`,
in the translation since Phase 2) and, with the X01–X75 targets, `F64`
(`model.elicitation_schema.NumberSchema.{minimum, maximum, default} : Option F64`). With Lean's
default `autoImplicit` the undefined name became an implicit argument of the field:
`Annotations.priority : {F32 : Type} → Option F32` (only `none` inhabits it), and the structure
moved to `Type 1`, which forced every containing type (`PrimitiveSchemaDefinition`, the
`BTreeMap` model) up a universe. Nothing reported it: the build passed.

**Workaround (XD3).** `formal/trusted/Rmcp/TypesExternal.lean` defines the root types `F64` and
`F32` as abstract types over `opaque` carriers (no axiom; no statement may inspect them), and the
library `Rmcp` is built with `autoImplicit = false`, so any undefined name in the translation is
now a build error.

**Reproducer** (`float`, target `repro::keep`):

```rust
//! Aeneas prints Rust's f64/f32 as `F64`/`F32`, which its Lean library does not define.
pub struct S {
    pub x: Option<f64>,
    pub y: Option<f32>,
}

pub fn keep(s: S) -> S {
    s
}
```

Charon and Aeneas exit 0 and print `x : Option F64`, `y : Option F32` in `Types.lean`. Built
against the Aeneas library with the default options, `S.mk : ({F32 : Type} → Option F32) →
({F32 : Type} → Option F32) → S`; with `-DautoImplicit=false`: `error: Unknown identifier 'F64'`
(line 27) and `Unknown identifier 'F32'` (line 28).

## Issue 2: `BTreeMap::keys().cloned().collect()` stops Aeneas

**Effect here.** `ElicitationSchema::new` (X40) and `ElicitationSchemaBuilder::build` (X74)
compute `properties.keys().cloned().collect()`. Worked around by the opaque wrapper
`prim::sorted_keys` (patch 08, hunks prim, E6, E7).

**Reproducer** (`btree_keys`, target `repro::keys`):

```rust
//! Aeneas internal error / fatal CFailure on `BTreeMap::keys().cloned().collect()`.
use std::collections::BTreeMap;

pub fn keys(m: &BTreeMap<String, u8>) -> Vec<String> {
    m.keys().cloned().collect()
}
```

Aeneas: `[Error] Internal error, please file an issue` at
`/rustc/library/core/src/iter/traits/iterator.rs`, lines 42:0-42:24 (the `Iterator` trait
declaration), then `Fatal error: exception Aeneas.Errors.CFailure(_)` raised from
`Aeneas__SymbolicToPureTypes.translate_fun_sigs` (`symbolic/SymbolicToPureTypes.ml` lines
1005–1006), called from `Translate.translate_crate_to_pure.translate_method_sig`.

## Issue 3: a loop or closure calling `contains_key` on a `BTreeMap` whose values hold a `Cow<'static, str>`

**Effect here.** The validation loop of X74 (`for f in &self.required { if
!self.properties.contains_key(f) { return Err(..) } }`; the values are
`PrimitiveSchemaDefinition`, whose schemas hold `Option<Cow<'static, str>>` titles). Every
rewrite that keeps the map inside the loop fails (a `for` with a flag: "unsupported nested
borrows"; a `while` with an index: "Not implemented"; `.iter().all(|f|
self.properties.contains_key(f))`, also through an opaque `contains_key` wrapper: "Internal
error" in the closure's `call_mut`). Worked around in patch 08 (E7) by checking the names
against the key list from `prim::sorted_keys`.

**Reproducer** (`btree_static_loop`; targets `repro::one`, `repro::all_while`, `repro::all_iter`):

```rust
//! Aeneas fails on a loop or closure that calls `contains_key` on a BTreeMap whose value type
//! holds a `Cow<'static, str>`; the same code with `V { t: Option<String> }` translates.
use std::borrow::Cow;
use std::collections::BTreeMap;

pub struct V {
    pub t: Option<Cow<'static, str>>,
}

pub struct B {
    pub properties: BTreeMap<String, V>,
    pub required: Vec<String>,
}

pub fn one(b: B) -> bool {
    b.properties.contains_key(&b.required[0])
}

pub fn all_while(b: B) -> bool {
    let mut all_present = true;
    let mut i = 0;
    while i < b.required.len() {
        if !b.properties.contains_key(&b.required[i]) {
            all_present = false;
        }
        i += 1;
    }
    all_present
}

pub fn all_iter(b: B) -> bool {
    b.required.iter().all(|f| b.properties.contains_key(f))
}
```

`one` translates. `all_while`: `[Error] Not implemented` at `src/lib.rs` lines 23:8-25:9 (the
`if` in the loop), body not translated. `all_iter`: `[Error] Internal error, please file an
issue` at lines 32:26-32:58 (the closure), the body of its `FnMut::call_mut` not translated.
Control (`btree_static_loop_control`): the same code with `pub t: Option<String>` translates all
three without error, so the `Cow<'static, str>` (a `'static` borrow inside the map's value type)
is what triggers it.

## Issue 4: `Iterator` instances of `Zip` and `Map` use fields the library's `Iterator` lacks

**Effect here.** `EnumSchemaBuilder<SingleSelect|MultiSelect>::build` (X33, X38) compute
`titles.into_iter().zip(values).map(|(title, const_)| ConstTitle { .. }).collect()`. Worked
around in patch 08 (E8) by the translated loop `const_titles`.

**Reproducer** (`zip_map`, target `repro::pairs`):

```rust
//! Iterator adapters Zip and Map: generated Iterator instances use fields the Aeneas library's
//! Iterator structure does not have.
pub struct P {
    pub a: String,
    pub b: String,
}

pub fn pairs(xs: Vec<String>, ys: Vec<String>) -> Vec<P> {
    xs.into_iter().zip(ys).map(|(a, b)| P { a, b }).collect()
}
```

Charon and Aeneas exit 0, with `[Warn] When retrieving the builtin information for trait decl
'core::iter::traits::iterator::Iterator', could not find the information for item 'zip'. The
model defined in the Lean library seems to be missing the corresponding field.` (also for `map`,
`extract/Extract.ml` line 2867). Building the output against the Aeneas library fails:
`` `zip` is not a field of structure `core.iter.traits.iterator.Iterator` `` (and `map`,
`collect`; six errors in `Funs.lean`).

## Issue 5: early return inside a loop

**Effect here.** X74's validation loop returns `Err` from inside the `for` loop:
`[Error] Early returns inside of loops are not supported yet`. A documented limitation; worked
around in patch 08 (E7) by `iter().all(..)`.

**Reproducer** (`loop_return`, target `repro::check`; `B::with_default` in the same file translates):

```rust
//! `check`: a `for` loop with an early `return Err(..)` inside (X74 before patch 08) fails;
//! `B::with_default` (the loop shape of X35 before patch 08) translates.
pub struct B {
    pub values: Vec<String>,
    pub default: Vec<String>,
}

impl B {
    pub fn with_default(mut self, defaults: Vec<String>) -> Result<B, String> {
        for value in &defaults {
            if !self.values.contains(value) {
                return Err("not a member".to_owned());
            }
        }
        self.default = defaults;
        Ok(self)
    }
}

pub fn check(b: &B, required: &Vec<String>) -> Result<(), &'static str> {
    if !required.is_empty() {
        for name in required {
            if !b.values.contains(name) {
                return Err("missing");
            }
        }
    }
    Ok(())
}
```

Aeneas exits 1: `[Error] Early returns inside of loops are not supported yet` at `src/lib.rs`
lines 20:0-29:1, body ignored.

## Issue 6 (not reduced): internal error in `EnumSchemaBuilder<MultiSelect>::with_default`

**Effect here.** X35 before patch 08: `[Error] Internal error, please file an issue` at
`crates/rmcp/src/model/elicitation_schema.rs` lines 1000:8-1023:5 (the `for` loop with an early
`return Err(..to_string())`, then the `if let … && …` bound checks), compiler source
`interp/Interp.ml` line 686; the body is not translated. Worked around in patch 08 (E3) by
`iter().all(..)`. **Not reduced:** standalone crates with the same shape (a method taking `mut
self` with a `Vec<String>` field, the loop over `&defaults` with `contains` and an early `return
Err`, followed by the two `if let Some(..) = .. && ..` checks, with `to_owned` or `to_string`
literals) translate without error, so a further ingredient of the crate (likely the
`EnumSchemaBuilder<T>` type parameter or its other fields) matters. To reproduce in the crate:
in a scratch copy, apply patches 01–07, set `start_from` to
`rmcp::model::elicitation_schema::EnumSchemaBuilder::with_default` and run Charon and Aeneas with
the options of `scripts/aeneas-translate.sh`.

## Library gaps (no defect; patch 08 avoids them)

- `format!` translates to `alloc::fmt::format` of a `core::fmt::Arguments`, which the Aeneas
  library defines as `Unit`: no exact model of a formatted string is possible (patch 08 hunk E1
  moves the `format!` of `enum_titles` into the opaque `prim::titles_mismatch_message`).
- `"…".to_string()` translates to the blanket `ToString::to_string` through `Display for str`,
  whose `core::fmt::Formatter` is opaque in the library (hunks E2–E5 use `to_owned`, which has a
  reviewed model).

## Draft upstream issues (AeneasVerif/aeneas; not filed)

> **Title:** Rust `f32`/`f64` are emitted as `F32`/`F64`, which the Lean library does not define
>
> A struct field of type `f64`/`f32` is printed as `F64`/`F32` in `Types.lean`, but the Lean
> backend library has no such definitions. With Lean's default `autoImplicit`, the field
> silently becomes `{F64 : Type} → Option F64` and the structure moves to `Type 1`; with
> `autoImplicit false` the build fails with "Unknown identifier `F64`". Versions: Aeneas
> nightly-2026.11.24-fb44cb4, Charon 0.1.324, rustc nightly-2026-09-17. Reproducer: the
> `float` crate above. Expected: `F32`/`F64` defined in the library (even as opaque types), or
> listed in the generated `TypesExternal_Template.lean` so that users must provide them.
> Suggestion: emit `set_option autoImplicit false` in the generated files so such gaps fail.

> **Title:** Internal error / CFailure on `BTreeMap::keys().cloned().collect()`
>
> Translating `m.keys().cloned().collect::<Vec<String>>()` for `m: &BTreeMap<String, u8>` fails
> with "Internal error, please file an issue" at the `Iterator` trait declaration
> (`core/src/iter/traits/iterator.rs` 42) and then `Fatal error: exception
> Aeneas.Errors.CFailure` from `SymbolicToPureTypes.translate_fun_sigs`. Reproducer: the
> `btree_keys` crate above.

> **Title:** Loop or closure over a `BTreeMap` whose value type holds `Cow<'static, str>` fails
>
> `contains_key` on a `BTreeMap<String, V>` inside a `while` loop ("Not implemented") or inside
> an `Iterator::all` closure ("Internal error" in `call_mut`) fails when `V` holds an
> `Option<Cow<'static, str>>`; the same code with `Option<String>` translates. Reproducer: the
> `btree_static_loop` crate and its control above.

> **Title:** `Zip`/`Map` iterator instances reference `zip`, `map`, `collect` fields missing from
> the Lean `Iterator` structure
>
> `xs.into_iter().zip(ys).map(f).collect()` translates with the warning "could not find the
> information for item 'zip'" (and `map`), and the generated `Funs.lean` does not build:
> "`zip` is not a field of structure `core.iter.traits.iterator.Iterator`" (also `map`,
> `collect`). Reproducer: the `zip_map` crate above.

(Before filing: attach the reproducer crates and the exact logs; do not include project-private
details. Issue 5 is a documented limitation and Issue 6 is not reduced; neither has a draft.)
