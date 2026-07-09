namespace JanusFormal
namespace P0EFTJanusOmegaDynamicsCandidateMatrixGate

set_option autoImplicit false

structure OmegaDynamicsCandidateMatrixGate where
  ConformalEinsteinTraceCandidate : Prop
  BimetricDeterminantRatioCandidate : Prop
  VisibleMatterConservationCandidate : Prop
  VariableConstantsClockCandidate : Prop
  DilatonCompensatorIsExtensionOnly : Prop
  ConformalEinsteinTraceRecommendedFirst : Prop
  ConformalTraceReductionDerived : Prop

def OmegaDynamicsMatrixClosed
    (g : OmegaDynamicsCandidateMatrixGate) : Prop :=
  g.ConformalEinsteinTraceCandidate /\
  g.ConformalEinsteinTraceRecommendedFirst /\
  g.ConformalTraceReductionDerived

def OmegaDynamicsMatrixFrontier
    (g : OmegaDynamicsCandidateMatrixGate) : Prop :=
  g.ConformalEinsteinTraceCandidate /\
  g.BimetricDeterminantRatioCandidate /\
  g.VisibleMatterConservationCandidate /\
  g.VariableConstantsClockCandidate /\
  g.DilatonCompensatorIsExtensionOnly /\
  g.ConformalEinsteinTraceRecommendedFirst /\
  Not g.ConformalTraceReductionDerived

theorem omega_matrix_selects_trace_but_needs_reduction
    (g : OmegaDynamicsCandidateMatrixGate)
    (hFrontier : OmegaDynamicsMatrixFrontier g) :
    Not (OmegaDynamicsMatrixClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.2.2 h.2.2

end P0EFTJanusOmegaDynamicsCandidateMatrixGate
end JanusFormal
