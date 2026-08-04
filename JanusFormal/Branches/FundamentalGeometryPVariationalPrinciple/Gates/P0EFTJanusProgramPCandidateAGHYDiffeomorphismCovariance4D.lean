import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D

/-!
# Candidate-A fixed-GHY control and covariance interface

The historical fixed Candidate-A faces use the canonical throat, whose
extrinsic curvature is identically zero.  Their contribution vanishes.  The
mobile normal-graph source is not reduced to this control: covariance of a
general family must preserve its sourced Robin datum.
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

/-- The canonical-throat fixed control has zero GHY action. -/
theorem globalCandidateAGHYAction_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (hFixed : data.nonNullBoundary =
      .fixed (data.boundary.nonNullFaces period hPeriod)) :
    globalCandidateAGHYAction period hPeriod data = 0 := by
  classical
  rw [globalCandidateAGHYAction, hFixed,
    globalCandidateANonNullBoundaryAction_fixed]
  unfold totalNonNullGHYCurve
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

/-- A transformation preserving the sourced non-null datum preserves its
Candidate-A GHY value. -/
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
        NonNullFace NullFace)
    (hDatum : target.nonNullBoundary = source.nonNullBoundary) :
    globalCandidateAGHYAction period hPeriod target =
      globalCandidateAGHYAction period hPeriod source := by
  unfold globalCandidateAGHYAction
  rw [hDatum]

end
end P0EFTJanusProgramPCandidateAGHYDiffeomorphismCovariance4D
