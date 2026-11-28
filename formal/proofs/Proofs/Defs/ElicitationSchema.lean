/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas

@[expose] public section

/-!
# Definitions used only by the internal `elicitation_schema.rs` statements

Signed off by the spec owner (Hoang Le Truong) on 2026-11-28 (decision XS6) together with the
statements; drafted by AI (Claude Code, `claude-opus-5-5`) for the specification stage of the
elicitation schema builders (X01–X75).

The definitions of `Defs.ElicitationSchema` that only internal statements use (decision XS3,
2026-11-28; human decision 2026-11-24 on `proofs/Proofs/Defs/`): the error message of the
intermediate X74 `ElicitationSchemaBuilder::build` (its statements go to
`formal/proofs/Proofs/Internal/Model/ElicitationSchema.lean`). The definitions of the public
statements are in `formal/specs/Defs/ElicitationSchema.lean`, in the same Lean namespace.

**Line citations.** "upstream" is `crates/rmcp/src/model/elicitation_schema.rs` at origin/main
`7caec76`; "patched" is the copy with translation patches 01–08 applied, whose line numbers the
`Source:` lines of `Rmcp/Funs.lean` give.
-/

namespace Defs.ElicitationSchema

/-- The error of `ElicitationSchemaBuilder::build` when a required name is not a property
(upstream line 1769, patched line 1764). -/
def requiredNotInPropertiesMsg : String := "Required field does not exist in properties"

end Defs.ElicitationSchema
