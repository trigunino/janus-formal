namespace JanusFormal
namespace P0EFTJanusWeylCuspPhysicalClockCandidateMatrixGate

set_option autoImplicit false

structure WeylCuspPhysicalClockCandidateMatrixGate where
  VisibleMatterJordanFrameCandidate : Prop
  BimetricScaleRatioClockCandidate : Prop
  ThermalPhotonClockCandidate : Prop
  DilatonCompensatorIsExtensionOnly : Prop
  PureConformalGeometryClockRejected : Prop
  VisibleMatterFrameRecommendedFirst : Prop
  MatterCouplingPullbackDerived : Prop

def PhysicalClockMatrixClosed
    (g : WeylCuspPhysicalClockCandidateMatrixGate) : Prop :=
  g.VisibleMatterJordanFrameCandidate /\
  g.VisibleMatterFrameRecommendedFirst /\
  g.MatterCouplingPullbackDerived

def PhysicalClockMatrixFrontier
    (g : WeylCuspPhysicalClockCandidateMatrixGate) : Prop :=
  g.VisibleMatterJordanFrameCandidate /\
  g.BimetricScaleRatioClockCandidate /\
  g.ThermalPhotonClockCandidate /\
  g.DilatonCompensatorIsExtensionOnly /\
  g.PureConformalGeometryClockRejected /\
  g.VisibleMatterFrameRecommendedFirst /\
  Not g.MatterCouplingPullbackDerived

theorem physical_clock_matrix_needs_matter_pullback
    (g : WeylCuspPhysicalClockCandidateMatrixGate)
    (hFrontier : PhysicalClockMatrixFrontier g) :
    Not (PhysicalClockMatrixClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.2.2 h.2.2

end P0EFTJanusWeylCuspPhysicalClockCandidateMatrixGate
end JanusFormal
