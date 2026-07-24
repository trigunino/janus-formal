import Lake
open Lake DSL

package janus_formal where
  buildDir := ".b"
  leanLibDir := "l"
  irDir := "i"
  moreLeanArgs := #["-DmaxHeartbeats=800000"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

lean_lib RellichKondrachovEuclidean where
  roots := #[`RellichKondrachov]

@[default_target]
lean_lib JanusFormal where
  roots := #[`JanusFormal]
