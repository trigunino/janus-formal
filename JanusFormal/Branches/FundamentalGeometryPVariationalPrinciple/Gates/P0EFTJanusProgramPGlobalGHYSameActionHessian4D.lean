import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAGHYDiffeomorphismCovariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrange4D

/-!
# Global Candidate-A fixed-GHY Hessian control

For a family explicitly selecting the historical canonical-throat fixed
source, the exact GHY summand is constant and its first and second Fréchet
derivatives vanish.  The mobile source is intentionally excluded from this
control and is handled by the normal-boundary chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGHYSameActionHessian4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPCandidateAGHYDiffeomorphismCovariance4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- The exact GHY summand pulled back to one regular Candidate-A chart. -/
def globalCandidateAGHYPullback
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    chart.Configuration → Real :=
  fun configuration =>
    globalCandidateAGHYAction period hPeriod
      (chart.family.dataAt configuration)

theorem globalCandidateAGHYPullback_eq_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (hFixed : ∀ configuration,
      (chart.family.dataAt configuration).nonNullBoundary =
        .fixed ((chart.family.dataAt configuration).boundary.nonNullFaces
          period hPeriod)) :
    globalCandidateAGHYPullback period hPeriod chart = 0 := by
  funext configuration
  exact globalCandidateAGHYAction_eq_zero period hPeriod
    (chart.family.dataAt configuration) (hFixed configuration)

theorem globalCandidateAGHYPullback_contDiff
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (hFixed : ∀ configuration,
      (chart.family.dataAt configuration).nonNullBoundary =
        .fixed ((chart.family.dataAt configuration).boundary.nonNullFaces
          period hPeriod)) :
    ContDiff Real ∞
      (globalCandidateAGHYPullback period hPeriod chart) := by
  rw [globalCandidateAGHYPullback_eq_zero period hPeriod chart hFixed]
  exact contDiff_const

theorem globalCandidateAGHYPullback_fderiv_eq_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (hFixed : ∀ current,
      (chart.family.dataAt current).nonNullBoundary =
        .fixed ((chart.family.dataAt current).boundary.nonNullFaces
          period hPeriod))
    (configuration : chart.Configuration) :
    fderiv Real
        (globalCandidateAGHYPullback period hPeriod chart)
        configuration =
      0 := by
  rw [globalCandidateAGHYPullback_eq_zero period hPeriod chart hFixed]
  simp

/-- The actual second Fréchet derivative of the exact Candidate-A GHY
summand, not a separately selected operator. -/
def globalCandidateAGHYSameActionHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (configuration : chart.Configuration) :
    chart.Configuration →L[Real] chart.Configuration →L[Real] Real :=
  fderiv Real
    (fderiv Real (globalCandidateAGHYPullback period hPeriod chart))
    configuration

theorem globalCandidateAGHYSameActionHessian_eq_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (hFixed : ∀ current,
      (chart.family.dataAt current).nonNullBoundary =
        .fixed ((chart.family.dataAt current).boundary.nonNullFaces
          period hPeriod))
    (configuration : chart.Configuration) :
    globalCandidateAGHYSameActionHessian period hPeriod chart configuration =
      0 := by
  unfold globalCandidateAGHYSameActionHessian
  rw [globalCandidateAGHYPullback_eq_zero period hPeriod chart hFixed]
  simp

theorem globalCandidateAGHYSameActionHessian_symmetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (MappingTorus (reflectedSphereData period hPeriod))}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (hFixed : ∀ current,
      (chart.family.dataAt current).nonNullBoundary =
        .fixed ((chart.family.dataAt current).boundary.nonNullFaces
          period hPeriod))
    (configuration first second : chart.Configuration) :
    globalCandidateAGHYSameActionHessian period hPeriod chart configuration
        first second =
      globalCandidateAGHYSameActionHessian period hPeriod chart configuration
        second first := by
  rw [globalCandidateAGHYSameActionHessian_eq_zero
    period hPeriod chart hFixed configuration]
  rfl

end
end P0EFTJanusProgramPGlobalGHYSameActionHessian4D
end JanusFormal
