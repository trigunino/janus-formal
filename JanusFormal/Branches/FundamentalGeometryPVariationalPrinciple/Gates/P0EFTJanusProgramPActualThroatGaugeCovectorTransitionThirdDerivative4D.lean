import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D

/-!
# Third derivative of the actual throat gauge covector transition

The centered covector-frame transition is smooth at every valid local
presentation.  This gate exposes its genuine third Frechet derivative in the
target base chart and proves the two adjacent symmetries of that coefficient.

This is only the third-order fiber-transition coefficient.  No third-jet
transport, cocycle, physical atlas, or current descent is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeCovectorTransitionThirdDerivative4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugePresentationAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatGaugeSecondOrderJetPresentationAt period hPeriod current

private abbrev CovectorEnd :=
  FramedCovector ThroatCoverCoordinates →L[Real]
    FramedCovector ThroatCoverCoordinates

local instance covectorEndNormedAddCommGroup :
    NormedAddCommGroup CovectorEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorEndNormedSpace : NormedSpace Real CovectorEnd :=
  ContinuousLinearMap.toNormedSpace

private abbrev CovectorTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] CovectorEnd

local instance covectorTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup CovectorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorTransitionFirstDerivativeNormedSpace :
    NormedSpace Real CovectorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev CovectorTransitionSecondDerivative :=
  ThroatCoverCoordinates →L[Real] CovectorTransitionFirstDerivative

local instance covectorTransitionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup CovectorTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorTransitionSecondDerivativeNormedSpace :
    NormedSpace Real CovectorTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private theorem fderiv_continuousLinearMap_apply_const
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (maps : E → F →L[Real] G) (point direction : E) (vector : F)
    (hMaps : DifferentiableAt Real maps point) :
    fderiv Real (fun current => maps current vector) point direction =
      fderiv Real maps point direction vector := by
  let evaluation : (F →L[Real] G) →L[Real] G :=
    ContinuousLinearMap.apply Real G vector
  have hDerivative :
      fderiv Real (evaluation ∘ maps) point =
        evaluation.comp (fderiv Real maps point) :=
    (evaluation.hasFDerivAt.comp point hMaps.hasFDerivAt).fderiv
  have hFunction :
      evaluation ∘ maps = fun current => maps current vector := by
    funext current
    rfl
  rw [hFunction] at hDerivative
  have hApply := congrArg
    (fun derivative : E →L[Real] G => derivative direction) hDerivative
  simpa only [evaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using hApply

/-- Genuine third derivative of the forward covector-frame transition,
expressed in the target base chart. -/
def throatGaugeCovectorTargetTransitionThirdDerivativeAt
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] CovectorEnd :=
  fderiv Real
    (fderiv Real
      (fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          source.frameAnchor target.frameAnchor target.chartAnchor)))
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)

/-- The first two directions of the third fiber-transition coefficient
commute. -/
theorem throatGaugeCovectorTargetTransitionThirdDerivativeAt_swap_first_second
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    throatGaugeCovectorTargetTransitionThirdDerivativeAt period hPeriod
        source target first second third =
      throatGaugeCovectorTargetTransitionThirdDerivativeAt period hPeriod
        source target second first third := by
  have hFirstDerivative :
      ContDiffAt Real 2
        (fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            source.frameAnchor target.frameAnchor target.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) :=
    (throatGaugeCovectorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod source.frameAnchor target.frameAnchor target.chartAnchor
        current ⟨source.frame_mem, target.frame_mem⟩ target.chart_mem).fderiv_right
          (m := 2) (by
            change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
            exact WithTop.coe_le_coe.mpr le_top)
  have hSymmetric :=
    (hFirstDerivative.isSymmSndFDerivAt (by norm_num)).eq first second
  exact congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real] CovectorEnd =>
      derivative third) hSymmetric

/-- The last two directions of the third fiber-transition coefficient
commute. -/
theorem throatGaugeCovectorTargetTransitionThirdDerivativeAt_swap_second_third
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    throatGaugeCovectorTargetTransitionThirdDerivativeAt period hPeriod
        source target first second third =
      throatGaugeCovectorTargetTransitionThirdDerivativeAt period hPeriod
        source target first third second := by
  let transition :=
    throatGaugeCovectorTransitionCenteredChart period hPeriod
      source.frameAnchor target.frameAnchor target.chartAnchor
  let coordinate :=
    extChartAt throatCoverModelWithCorners target.chartAnchor current
  have hTransitionC3 : ContDiffAt Real 3 transition coordinate :=
    (throatGaugeCovectorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod source.frameAnchor target.frameAnchor target.chartAnchor
        current ⟨source.frame_mem, target.frame_mem⟩ target.chart_mem).of_le (by
          change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hHessian :
      DifferentiableAt Real
        (fderiv Real (fderiv Real transition)) coordinate :=
    ((hTransitionC3.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hHessianAtSecond :
      DifferentiableAt Real
        (fun nearby =>
          fderiv Real (fderiv Real transition) nearby second) coordinate :=
    hHessian.clm_apply (differentiableAt_const (c := second))
  have hHessianAtThird :
      DifferentiableAt Real
        (fun nearby =>
          fderiv Real (fderiv Real transition) nearby third) coordinate :=
    hHessian.clm_apply (differentiableAt_const (c := third))
  have hNearbySymmetry :
      Filter.EventuallyEq (𝓝 coordinate)
        (fun nearby =>
          fderiv Real (fderiv Real transition) nearby second third)
        (fun nearby =>
          fderiv Real (fderiv Real transition) nearby third second) := by
    filter_upwards [hTransitionC3.eventually (by norm_num)]
      with nearby hNearby
    exact (hNearby.isSymmSndFDerivAt (𝕜 := Real) (by norm_num)).eq
      second third
  have hDerivativeEquality := hNearbySymmetry.fderiv_eq (𝕜 := Real)
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real] CovectorEnd =>
      derivative first) hDerivativeEquality
  have hOuterSecond :
      fderiv Real
          (fun nearby =>
            fderiv Real (fderiv Real transition) nearby second)
          coordinate first =
        fderiv Real (fderiv Real (fderiv Real transition))
          coordinate first second :=
    fderiv_continuousLinearMap_apply_const _ coordinate first second hHessian
  have hOuterThird :
      fderiv Real
          (fun nearby =>
            fderiv Real (fderiv Real transition) nearby third)
          coordinate first =
        fderiv Real (fderiv Real (fderiv Real transition))
          coordinate first third :=
    fderiv_continuousLinearMap_apply_const _ coordinate first third hHessian
  have hSecondThird :
      fderiv Real
          (fun nearby =>
            fderiv Real (fderiv Real transition) nearby second third)
          coordinate first =
        fderiv Real (fderiv Real (fderiv Real transition))
          coordinate first second third := by
    calc
      _ = fderiv Real
          (fun nearby => fderiv Real (fderiv Real transition) nearby second)
          coordinate first third :=
        fderiv_continuousLinearMap_apply_const _ coordinate first third
          hHessianAtSecond
      _ = _ := by
        exact congrArg
          (fun derivative : CovectorTransitionFirstDerivative =>
            derivative third) hOuterSecond
  have hThirdSecond :
      fderiv Real
          (fun nearby =>
            fderiv Real (fderiv Real transition) nearby third second)
          coordinate first =
        fderiv Real (fderiv Real (fderiv Real transition))
          coordinate first third second := by
    calc
      _ = fderiv Real
          (fun nearby => fderiv Real (fderiv Real transition) nearby third)
          coordinate first second :=
        fderiv_continuousLinearMap_apply_const _ coordinate first second
          hHessianAtThird
      _ = _ := by
        exact congrArg
          (fun derivative : CovectorTransitionFirstDerivative =>
            derivative second) hOuterThird
  rw [hSecondThird, hThirdSecond] at hApplied
  simpa only [throatGaugeCovectorTargetTransitionThirdDerivativeAt,
    transition, coordinate] using hApplied

end
end P0EFTJanusProgramPActualThroatGaugeCovectorTransitionThirdDerivative4D
end JanusFormal
