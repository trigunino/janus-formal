namespace JanusFormal
namespace P0EFTJanusZ2RegularSigmaCollarAlgebraGate

set_option autoImplicit false

structure RegularSigmaCollarAlgebraGate where
  collarAnsatzDeclared : Prop
  fullTRhoBlockNonDegenerate : Prop
  inducedHNonDegenerate : Prop
  regularHKPipelineAllowed : Prop
  horizonA0Zero : Prop

theorem regular_hK_requires_induced_h_non_degenerate
    (g : RegularSigmaCollarAlgebraGate)
    (hAllowed : g.regularHKPipelineAllowed)
    (hImplies : g.regularHKPipelineAllowed -> g.inducedHNonDegenerate) :
    g.inducedHNonDegenerate := by
  exact hImplies hAllowed

theorem horizon_A0_zero_blocks_regular_hK
    (g : RegularSigmaCollarAlgebraGate)
    (_hHorizon : g.horizonA0Zero)
    (hNoH : Not g.inducedHNonDegenerate)
    (hImplies : g.regularHKPipelineAllowed -> g.inducedHNonDegenerate) :
    Not g.regularHKPipelineAllowed := by
  intro hAllowed
  exact hNoH (hImplies hAllowed)

end P0EFTJanusZ2RegularSigmaCollarAlgebraGate
end JanusFormal
