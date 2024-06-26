import Lake
open Lake DSL

package «my_sketchbook» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require std from git "https://github.com/leanprover/std4" @ "main"

@[default_target]
lean_lib «MySketchbook» where
  -- add any library configuration options here
