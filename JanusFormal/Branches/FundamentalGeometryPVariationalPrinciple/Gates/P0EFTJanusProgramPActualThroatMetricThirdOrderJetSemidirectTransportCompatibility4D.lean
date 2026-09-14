import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartThirdOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransportCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPContinuousLinearMapThirdOrderLeibniz4D

/-!
# Compatibility of metric third-jet semidirect transport

The actual third-order semidirect transport sends an extracted smooth metric
jet to the extraction in the target frame and chart.  The lower jet is the
existing second-order compatibility theorem; only the third derivative is
proved here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransportCompatibility4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 3000000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartThirdOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransportCompatibility4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPContinuousLinearMapThirdOrderLeibniz4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  ThroatCovariantTwoTensorModel

private abbrev MetricThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates TensorModel

private abbrev TensorEnd :=
  TensorModel →L[Real] TensorModel

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorModelNormedSpace

local instance tensorEndNormedAddCommGroup :
    NormedAddCommGroup TensorEnd :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorEndNormedAddCommGroup

local instance tensorEndNormedSpace : NormedSpace Real TensorEnd :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorEndNormedSpace

private abbrev TensorTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] TensorEnd

local instance tensorTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup TensorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorTransitionFirstDerivativeNormedSpace :
    NormedSpace Real TensorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev TensorTransitionSecondDerivative :=
  ThroatCoverCoordinates →L[Real] TensorTransitionFirstDerivative

local instance tensorTransitionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup TensorTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorTransitionSecondDerivativeNormedSpace :
    NormedSpace Real TensorTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private theorem contDiffThree_le_infty :
    (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
  change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
  exact WithTop.coe_le_coe.mpr le_top

/-- Semidirect transport of an extracted smooth metric third jet is exactly
the third jet extracted in the target frame and chart. -/
theorem throatMetricThirdOrderJetSemidirectTransportAt_extracted
    {current : EffectiveThroat period hPeriod}
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (source target :
      ThroatMetricSecondOrderJetFrameChartAt period hPeriod current) :
    throatMetricThirdOrderJetSemidirectTransportAt period hPeriod
        source target
        (throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor
          source.frameAnchor source.chartAnchor current source.frame_mem
            source.chart_mem) =
      throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor
        target.frameAnchor target.chartAnchor current target.frame_mem
          target.chart_mem := by
  let sourceRepresentative :=
    throatTensorFrameChartRepresentative period hPeriod tensor
      source.frameAnchor source.chartAnchor
  let sourceInTargetRepresentative :=
    throatTensorFrameChartRepresentative period hPeriod tensor
      source.frameAnchor target.chartAnchor
  let targetRepresentative :=
    throatTensorFrameChartRepresentative period hPeriod tensor
      target.frameAnchor target.chartAnchor
  let sourceJet :=
    throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor
      source.frameAnchor source.chartAnchor current source.frame_mem
        source.chart_mem
  let sourceInTargetJet :=
    throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor
      source.frameAnchor target.chartAnchor current source.frame_mem
        target.chart_mem
  let targetJet :=
    throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor
      target.frameAnchor target.chartAnchor current target.frame_mem
        target.chart_mem
  let baseTransition :=
    throatGaugeBaseChartTransition period hPeriod
      target.chartAnchor source.chartAnchor
  let fiberTransition :=
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
      source.frameAnchor target.frameAnchor target.chartAnchor
  let sourceCoordinate :=
    extChartAt throatCoverModelWithCorners source.chartAnchor current
  let targetCoordinate :=
    extChartAt throatCoverModelWithCorners target.chartAnchor current
  let Ainv := fderiv Real baseTransition targetCoordinate
  let Binv := fderiv Real (fderiv Real baseTransition) targetCoordinate
  let Cinv :=
    fderiv Real (fderiv Real (fderiv Real baseTransition)) targetCoordinate
  let D : TensorEnd :=
    throatCovariantTwoTensorFrameTransitionAt period hPeriod
      source.frameAnchor target.frameAnchor current
  let E := fderiv Real fiberTransition targetCoordinate
  let F := fderiv Real (fderiv Real fiberTransition) targetCoordinate
  let G :=
    fderiv Real (fderiv Real (fderiv Real fiberTransition)) targetCoordinate
  change throatMetricThirdOrderJetSemidirectTransportAt period hPeriod
    source target sourceJet = targetJet
  have hFrames : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) source.frameAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) target.frameAnchor).baseSet :=
    ⟨source.frame_mem, target.frame_mem⟩
  have hBaseAt : baseTransition targetCoordinate = sourceCoordinate := by
    simpa only [baseTransition, targetCoordinate, sourceCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod
        target.chartAnchor source.chartAnchor current target.chart_mem
  have hCoordinateInverse :
      (extChartAt throatCoverModelWithCorners target.chartAnchor).symm
          targetCoordinate = current := by
    simpa only [targetCoordinate] using
      (extChartAt throatCoverModelWithCorners target.chartAnchor).left_inv
        target.chart_mem
  have hBaseRegularity : ContDiffAt Real 3 baseTransition targetCoordinate :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      target.chartAnchor source.chartAnchor current target.chart_mem
        source.chart_mem).of_le contDiffThree_le_infty
  have hSourceRegularity :
      ContDiffAt Real 3 sourceRepresentative sourceCoordinate :=
    (throatTensorFrameChartRepresentative_contDiffAt_infty period hPeriod
      tensor source.frameAnchor source.chartAnchor current source.frame_mem
        source.chart_mem).of_le contDiffThree_le_infty
  have hSourceAtRegularity :
      ContDiffAt Real 3 sourceRepresentative
        (baseTransition targetCoordinate) := by
    simpa only [hBaseAt] using hSourceRegularity
  have hSourceInTargetRegularity :
      ContDiffAt Real 3 sourceInTargetRepresentative targetCoordinate :=
    (throatTensorFrameChartRepresentative_contDiffAt_infty period hPeriod
      tensor source.frameAnchor target.chartAnchor current source.frame_mem
        target.chart_mem).of_le contDiffThree_le_infty
  have hFiberRegularity :
      ContDiffAt Real 3 fiberTransition targetCoordinate :=
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod source.frameAnchor target.frameAnchor target.chartAnchor
        current hFrames target.chart_mem).of_le contDiffThree_le_infty
  have hSourceValue : sourceInTargetJet.value = sourceJet.value := by
    simp only [sourceInTargetJet, sourceJet,
      throatTensorThirdOrderJetInFrameChartAt_value]
  have hBaseFirst :
      sourceInTargetJet.firstDerivative =
        sourceJet.firstDerivative.comp Ainv := by
    simpa only [sourceInTargetJet, sourceJet, Ainv, baseTransition,
      targetCoordinate,
      throatTensorThirdOrderJetInFrameChartAt_firstDerivative,
      throatTensorSecondOrderJetInFrameChartAt_firstDerivative] using
        throatTensorSecondOrderJetInFrameChartAt_firstDerivative_transition
          period hPeriod tensor source.frameAnchor target.chartAnchor
            source.chartAnchor current source.frame_mem target.chart_mem
              source.chart_mem
  have hBaseSecond (first second : ThroatCoverCoordinates) :
      sourceInTargetJet.secondDerivative first second =
        sourceJet.secondDerivative (Ainv first) (Ainv second) +
          sourceJet.firstDerivative (Binv first second) := by
    simpa only [sourceInTargetJet, sourceJet, Ainv, Binv, baseTransition,
      targetCoordinate,
      throatTensorThirdOrderJetInFrameChartAt_firstDerivative,
      throatTensorThirdOrderJetInFrameChartAt_secondDerivative,
      throatTensorSecondOrderJetInFrameChartAt_firstDerivative,
      throatTensorSecondOrderJetInFrameChartAt_secondDerivative] using
        throatTensorSecondOrderJetInFrameChartAt_secondDerivative_transition_apply
          period hPeriod tensor source.frameAnchor target.chartAnchor
            source.chartAnchor current source.frame_mem target.chart_mem
              source.chart_mem first second
  have hBaseGerm : sourceInTargetRepresentative =ᶠ[𝓝 targetCoordinate]
      sourceRepresentative ∘ baseTransition := by
    simpa only [sourceInTargetRepresentative, sourceRepresentative,
      baseTransition, targetCoordinate] using
      throatTensorFrameChartRepresentative_baseChartTransition_eventuallyEq
        period hPeriod tensor source.frameAnchor target.chartAnchor
          source.chartAnchor current target.chart_mem source.chart_mem
  have hBaseThird (first second third : ThroatCoverCoordinates) :
      sourceInTargetJet.thirdDerivative first second third =
        sourceJet.thirdDerivative
            (Ainv first) (Ainv second) (Ainv third) +
          sourceJet.secondDerivative
            (Binv first second) (Ainv third) +
          sourceJet.secondDerivative
            (Binv first third) (Ainv second) +
          sourceJet.secondDerivative
            (Binv second third) (Ainv first) +
          sourceJet.firstDerivative (Cinv first second third) := by
    have hFirstDerivativeGerm := hBaseGerm.fderiv (𝕜 := Real)
    have hSecondDerivativeGerm := hFirstDerivativeGerm.fderiv (𝕜 := Real)
    have hThirdDerivativeGerm :=
      hSecondDerivativeGerm.fderiv_eq (𝕜 := Real)
    have hApplied := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates →L[Real]
            ThroatCoverCoordinates →L[Real] TensorModel =>
        derivative first second third) hThirdDerivativeGerm
    have hFormula := third_fderiv_comp_apply baseTransition
      sourceRepresentative targetCoordinate hBaseRegularity
        hSourceAtRegularity first second third
    rw [hBaseAt] at hFormula
    have hCombined := hApplied.trans hFormula
    simpa only [sourceInTargetJet, sourceJet,
      sourceInTargetRepresentative, sourceRepresentative, Ainv, Binv, Cinv,
      throatTensorThirdOrderJetInFrameChartAt_firstDerivative,
      throatTensorThirdOrderJetInFrameChartAt_secondDerivative,
      throatTensorThirdOrderJetInFrameChartAt_thirdDerivative] using hCombined
  have hFiberGerm :
      (fun coordinate => fiberTransition coordinate
        (sourceInTargetRepresentative coordinate)) =ᶠ[𝓝 targetCoordinate]
        targetRepresentative := by
    simpa only [fiberTransition, sourceInTargetRepresentative,
      targetRepresentative, targetCoordinate] using
      throatTensorFrameChartRepresentative_frameTransition_eventuallyEq
        period hPeriod tensor source.frameAnchor target.frameAnchor
          target.chartAnchor current hFrames target.chart_mem
  have hFiberAt : fiberTransition targetCoordinate = D := by
    simp only [fiberTransition, targetCoordinate, D,
      throatCovariantTwoTensorTransitionCenteredChart, hCoordinateInverse]
  have hSourceInTargetValueAt :
      sourceInTargetRepresentative targetCoordinate =
        sourceInTargetJet.value := by
    simp only [sourceInTargetRepresentative, sourceInTargetJet,
      throatTensorThirdOrderJetInFrameChartAt_value,
      throatTensorFrameChartRepresentative, Function.comp_apply]
    rw [hCoordinateInverse]
    rfl
  have hFiberThird (first second third : ThroatCoverCoordinates) :
      targetJet.thirdDerivative first second third =
        D (sourceInTargetJet.thirdDerivative first second third) +
          E first (sourceInTargetJet.secondDerivative second third) +
          E second (sourceInTargetJet.secondDerivative first third) +
          E third (sourceInTargetJet.secondDerivative first second) +
          F first second (sourceInTargetJet.firstDerivative third) +
          F first third (sourceInTargetJet.firstDerivative second) +
          F second third (sourceInTargetJet.firstDerivative first) +
          G first second third sourceInTargetJet.value := by
    have hFirstDerivativeGerm := hFiberGerm.fderiv (𝕜 := Real)
    have hSecondDerivativeGerm := hFirstDerivativeGerm.fderiv (𝕜 := Real)
    have hThirdDerivativeGerm :=
      hSecondDerivativeGerm.fderiv_eq (𝕜 := Real)
    have hApplied := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates →L[Real]
            ThroatCoverCoordinates →L[Real] TensorModel =>
        derivative first second third) hThirdDerivativeGerm
    have hProduct := third_fderiv_clm_apply_apply fiberTransition
      sourceInTargetRepresentative targetCoordinate first second third
        hFiberRegularity hSourceInTargetRegularity
    have hCombined := hApplied.symm.trans hProduct
    rw [hFiberAt] at hCombined
    rw [hSourceInTargetValueAt] at hCombined
    simpa only [targetJet, sourceInTargetJet, targetRepresentative,
      sourceInTargetRepresentative, targetCoordinate, E, F, G,
      throatTensorThirdOrderJetInFrameChartAt_value,
      throatTensorThirdOrderJetInFrameChartAt_firstDerivative,
      throatTensorThirdOrderJetInFrameChartAt_secondDerivative,
      throatTensorThirdOrderJetInFrameChartAt_thirdDerivative] using hCombined
  apply FramedThirdOrderJet.ext_components
  · simpa only [sourceJet, targetJet,
      throatMetricThirdOrderJetSemidirectTransportAt_truncate,
      throatTensorThirdOrderJetInFrameChartAt_truncate] using
      throatMetricSecondOrderJetSemidirectTransportAt_extracted
        period hPeriod tensor source target
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    apply ContinuousLinearMap.ext
    intro third
    have hTransportThird :
        (throatMetricThirdOrderJetSemidirectTransportAt period hPeriod
          source target sourceJet).thirdDerivative first second third =
          D (sourceJet.thirdDerivative
            (Ainv first) (Ainv second) (Ainv third)) +
          D (sourceJet.secondDerivative
            (Binv first second) (Ainv third)) +
          D (sourceJet.secondDerivative
            (Binv first third) (Ainv second)) +
          D (sourceJet.secondDerivative
            (Binv second third) (Ainv first)) +
          D (sourceJet.firstDerivative (Cinv first second third)) +
          E first (sourceJet.secondDerivative (Ainv second) (Ainv third)) +
          E second (sourceJet.secondDerivative (Ainv first) (Ainv third)) +
          E third (sourceJet.secondDerivative (Ainv first) (Ainv second)) +
          E first (sourceJet.firstDerivative (Binv second third)) +
          E second (sourceJet.firstDerivative (Binv first third)) +
          E third (sourceJet.firstDerivative (Binv first second)) +
          F first second (sourceJet.firstDerivative (Ainv third)) +
          F first third (sourceJet.firstDerivative (Ainv second)) +
          F second third (sourceJet.firstDerivative (Ainv first)) +
          G first second third sourceJet.value := by
      rfl
    rw [hTransportThird]
    rw [hFiberThird first second third]
    rw [hBaseThird first second third]
    rw [hBaseSecond second third]
    rw [hBaseSecond first third]
    rw [hBaseSecond first second]
    rw [hBaseFirst]
    rw [hSourceValue]
    simp only [map_add, ContinuousLinearMap.comp_apply]
    abel

/-- The physical induced metric is the canonical specialization of the
generic third-order compatibility theorem. -/
theorem globalGaugeFixedThroatMetricThirdOrderJetSemidirectTransportAt_extracted
    {current : EffectiveThroat period hPeriod}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (source target :
      ThroatMetricSecondOrderJetFrameChartAt period hPeriod current) :
    throatMetricThirdOrderJetSemidirectTransportAt period hPeriod
        source target
        (globalGaugeFixedThroatMetricThirdOrderJetInFrameChartAt period hPeriod
          configuration sector source.frameAnchor source.chartAnchor current
            source.frame_mem source.chart_mem) =
      globalGaugeFixedThroatMetricThirdOrderJetInFrameChartAt period hPeriod
        configuration sector target.frameAnchor target.chartAnchor current
          target.frame_mem target.chart_mem := by
  simpa only [globalGaugeFixedThroatMetricThirdOrderJetInFrameChartAt] using
    throatMetricThirdOrderJetSemidirectTransportAt_extracted period hPeriod
      (globalGaugeFixedInducedMetricBySector period hPeriod configuration sector)
        source target

end
end P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransportCompatibility4D
end JanusFormal
