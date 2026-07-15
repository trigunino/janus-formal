import Lake
open Lake DSL

package janus_formal where
  moreLeanArgs := #["-DmaxHeartbeats=800000"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

@[default_target]
lean_lib JanusFormal where
  roots := #[`JanusFormal]
