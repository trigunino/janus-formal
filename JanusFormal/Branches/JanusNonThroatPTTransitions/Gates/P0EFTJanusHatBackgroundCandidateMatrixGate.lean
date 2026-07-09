namespace JanusFormal
namespace P0EFTJanusHatBackgroundCandidateMatrixGate

set_option autoImplicit false

structure HatBackgroundCandidateMatrixGate where
  ProjectiveS4RP4ConformalBackgroundCandidate : Prop
  FlatMilneReferenceBackgroundCandidate : Prop
  MinusSectorBackgroundCandidate : Prop
  ArbitraryRegularHatMetricRejected : Prop
  ProjectiveS4RP4RecommendedFirst : Prop
  ProjectiveConformalTimeCurvatureMapDerived : Prop

def HatBackgroundMatrixClosed
    (g : HatBackgroundCandidateMatrixGate) : Prop :=
  g.ProjectiveS4RP4ConformalBackgroundCandidate /\
  g.ProjectiveS4RP4RecommendedFirst /\
  g.ProjectiveConformalTimeCurvatureMapDerived

def HatBackgroundMatrixFrontier
    (g : HatBackgroundCandidateMatrixGate) : Prop :=
  g.ProjectiveS4RP4ConformalBackgroundCandidate /\
  g.FlatMilneReferenceBackgroundCandidate /\
  g.MinusSectorBackgroundCandidate /\
  g.ArbitraryRegularHatMetricRejected /\
  g.ProjectiveS4RP4RecommendedFirst /\
  Not g.ProjectiveConformalTimeCurvatureMapDerived

theorem hat_background_matrix_needs_projective_map
    (g : HatBackgroundCandidateMatrixGate)
    (hFrontier : HatBackgroundMatrixFrontier g) :
    Not (HatBackgroundMatrixClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.2 h.2.2

end P0EFTJanusHatBackgroundCandidateMatrixGate
end JanusFormal
