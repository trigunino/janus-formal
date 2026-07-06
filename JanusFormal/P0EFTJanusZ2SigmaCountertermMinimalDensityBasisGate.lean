namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermMinimalDensityBasisGate

set_option autoImplicit false

structure MinimalDensityBasisGate where
  toyExactModelImported : Prop
  localityRestrictionDeclared : Prop
  z2ParityFilterDeclared : Prop
  torsionlessBranchFilterDeclared : Prop
  constantRemovedByNormalization : Prop
  linearKTermKept : Prop
  kSquaredTermKept : Prop
  intrinsicCurvatureTermKept : Prop
  zeroReferenceConstraintAvailable : Prop
  metricResidualTraceConstraintAvailable : Prop
  extrinsicResidualTraceConstraintAvailable : Prop
  coefficientSystemSolvable : Prop

def minimalBasisDeclared (g : MinimalDensityBasisGate) : Prop :=
  g.toyExactModelImported /\
  g.localityRestrictionDeclared /\
  g.z2ParityFilterDeclared /\
  g.torsionlessBranchFilterDeclared /\
  g.constantRemovedByNormalization /\
  g.linearKTermKept /\
  g.kSquaredTermKept /\
  g.intrinsicCurvatureTermKept

def minimalCoefficientSystemReady (g : MinimalDensityBasisGate) : Prop :=
  minimalBasisDeclared g /\
  g.zeroReferenceConstraintAvailable /\
  g.metricResidualTraceConstraintAvailable /\
  g.extrinsicResidualTraceConstraintAvailable /\
  g.coefficientSystemSolvable

theorem minimal_basis_does_not_solve_without_metric_trace
    (g : MinimalDensityBasisGate)
    (hMissing : Not g.metricResidualTraceConstraintAvailable) :
    Not (minimalCoefficientSystemReady g) := by
  intro hReady
  exact hMissing hReady.2.2.1

theorem minimal_basis_does_not_solve_without_extrinsic_trace
    (g : MinimalDensityBasisGate)
    (hMissing : Not g.extrinsicResidualTraceConstraintAvailable) :
    Not (minimalCoefficientSystemReady g) := by
  intro hReady
  exact hMissing hReady.2.2.2.1

end P0EFTJanusZ2SigmaCountertermMinimalDensityBasisGate
end JanusFormal
