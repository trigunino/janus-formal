namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermLctZ2OddDensityGate

set_option autoImplicit false

structure LctZ2OddDensityGate where
  symbolicPrimitiveReady : Prop
  integrationConstantOddCompatible : Prop
  alphaResZ2AntiInvarianceProved : Prop
  fieldSpaceExactnessNoEvenConstant : Prop
  lCtZ2OddDensityProved : Prop

def lCtOddReady (g : LctZ2OddDensityGate) : Prop :=
  g.symbolicPrimitiveReady /\
  g.integrationConstantOddCompatible /\
  g.alphaResZ2AntiInvarianceProved /\
  g.fieldSpaceExactnessNoEvenConstant /\
  g.lCtZ2OddDensityProved

theorem alpha_res_odd_plus_zero_constant_gives_lct_odd
    (g : LctZ2OddDensityGate)
    (hTransport :
      g.symbolicPrimitiveReady ->
      g.integrationConstantOddCompatible ->
      g.alphaResZ2AntiInvarianceProved ->
      g.fieldSpaceExactnessNoEvenConstant ->
      g.lCtZ2OddDensityProved)
    (hPrimitive : g.symbolicPrimitiveReady)
    (hConstant : g.integrationConstantOddCompatible)
    (hAlpha : g.alphaResZ2AntiInvarianceProved)
    (hExact : g.fieldSpaceExactnessNoEvenConstant) :
    g.lCtZ2OddDensityProved := by
  exact hTransport hPrimitive hConstant hAlpha hExact

theorem missing_alpha_res_anti_invariance_blocks_lct_odd
    (g : LctZ2OddDensityGate)
    (hMissing : Not g.alphaResZ2AntiInvarianceProved) :
    Not (lCtOddReady g) := by
  intro hReady
  exact hMissing hReady.2.2.1

end P0EFTJanusZ2SigmaCountertermLctZ2OddDensityGate
end JanusFormal
