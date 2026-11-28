/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Defs.Bytes
public import Defs.IntParse
public import Defs.JsonRpc
public import Defs.Wire
public import Defs.RequestState
public import Defs.CodecState
public import Defs.Skill
public import Defs.ElicitationSchema

@[expose] public section

/-!
# Defs

Root of the `Defs` library: the definitions used by the public spec statements (plan Section 5).
Maintained by hand (formal/CONTRIBUTING.md, "Library roots"). Imports `Defs.Bytes`,
`Defs.IntParse` and `Defs.JsonRpc` (signed off at S24, 2026-11-24) and `Defs.Wire`,
`Defs.RequestState`, `Defs.CodecState` (signed off at S05; back here since the public
`request_state.rs` statements use them; `Defs.RequestState` since R09–R15, 2026-11-25, with the
R09–R15 definitions added to `Defs.CodecState`), `Defs.Skill` (the `skill.rs` model, signed off
2026-11-25) and `Defs.ElicitationSchema` (the elicitation schema builders, signed off 2026-11-28,
decision XS6). The definitions used only by internal statements
(`Defs.Methods`, `Defs.Tower` at S24; `Defs.Sse`, `Defs.Net` at S25) live in modules
`Proofs.Defs.*` under `formal/proofs/Proofs/Defs/`, with their Lean names unchanged (human decision
2026-11-24).
-/
