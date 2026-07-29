import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D

/-!
# Candidate-A GHY diffeomorphism covariance

The Candidate-A non-null faces use the canonical throat, whose extrinsic
curvature is identically zero.  Since the GHY block evaluates its exact curve
at the base parameter, every face contribution vanishes.  Its covariance is
therefore unconditional and does not need a separate transformation input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAGHYDiffeomorphismCovariance4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusNonNullGHYExactInverseCurve
open P0EFTJanusFiniteStratifiedBoundaryVariation
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The canonical-throat Candidate-A GHY block vanishes for every action
datum. -/
theorem globalCandidateAGHYAction_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    globalCandidateAGHYAction period hPeriod data = 0 := by
  classical
  unfold globalCandidateAGHYAction totalNonNullGHYCurve
  apply Finset.sum_eq_zero
  intro face _
  have hExtrinsic :
      (data.boundary.nonNullFaces period hPeriod face).geometry.extrinsicCurvature =
        0 := rfl
  have hDensity :
      nonNullGHYDensity
          (data.boundary.nonNullFaces period hPeriod face).einsteinScale
          (data.boundary.nonNullFaces period hPeriod face).geometry =
        0 :=
    nonNullGHYDensity_zero_of_extrinsicCurvature_zero
      (data.boundary.nonNullFaces period hPeriod face).einsteinScale
      (data.boundary.nonNullFaces period hPeriod face).geometry hExtrinsic
  simp only [nonNullGHYCurve, nonNullGHYExactInverseCurve_zero, hDensity,
    mul_zero]

/-- Any two Candidate-A GHY blocks agree; in particular the genuine
time-translation or diffeomorphism action needs no additional GHY
hypothesis. -/
theorem globalCandidateAGHYAction_configuration_independent
    {sourceConfiguration targetConfiguration :
      GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (source :
      GlobalCandidateAActionData period hPeriod sourceConfiguration couplings
        NonNullFace NullFace)
    (target :
      GlobalCandidateAActionData period hPeriod targetConfiguration couplings
        NonNullFace NullFace) :
    globalCandidateAGHYAction period hPeriod target =
      globalCandidateAGHYAction period hPeriod source := by
  rw [globalCandidateAGHYAction_eq_zero period hPeriod target,
    globalCandidateAGHYAction_eq_zero period hPeriod source]

end
end P0EFTJanusProgramPCandidateAGHYDiffeomorphismCovariance4D
