namespace JanusFormal
namespace P0EFTJanusComplexRealityCP1FromJanusPTGate

set_option autoImplicit false

structure CP1FromJanusPTGate where
  localBoundarySpinorVariablesReady : Prop
  genericSpinorRestrictionReady : Prop
  genericAPSProjectionFormulaReady : Prop
  projectivizedNonzeroSpinorLineDefinesCP1 : Prop
  globalZ2SigmaSpinorProjectionReady : Prop
  resolvedTunnelPinLiftReady : Prop
  plusMinusSpinorBundleDataReady : Prop

def cp1MathematicalCandidateReady (g : CP1FromJanusPTGate) : Prop :=
  g.localBoundarySpinorVariablesReady /\
  g.genericSpinorRestrictionReady /\
  g.genericAPSProjectionFormulaReady /\
  g.projectivizedNonzeroSpinorLineDefinesCP1

def cp1DerivedFromJanusPT (g : CP1FromJanusPTGate) : Prop :=
  cp1MathematicalCandidateReady g /\
  g.globalZ2SigmaSpinorProjectionReady /\
  g.resolvedTunnelPinLiftReady /\
  g.plusMinusSpinorBundleDataReady

theorem local_cp1_without_global_projection_not_janus_derived
    (g : CP1FromJanusPTGate)
    (hMissing : Not g.globalZ2SigmaSpinorProjectionReady) :
    Not (cp1DerivedFromJanusPT g) := by
  intro h
  exact hMissing h.right.left

end P0EFTJanusComplexRealityCP1FromJanusPTGate
end JanusFormal
