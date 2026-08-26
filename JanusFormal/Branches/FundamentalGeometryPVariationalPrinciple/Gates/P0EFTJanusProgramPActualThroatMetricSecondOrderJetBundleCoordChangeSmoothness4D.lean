import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetTransitionSmoothRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D

/-!
# Smoothness of throat metric second-jet coordinate changes

This gate upgrades continuity of the concrete semidirect coordinate changes
to `C∞` regularity on every double atlas overlap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetTransitionSmoothRegularity4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev MetricJet :=
  FramedSecondOrderJet ThroatCoverCoordinates TensorModel

private abbrev TensorEnd := TensorModel →L[Real] TensorModel

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorModelNormedSpace

local instance tensorEndNormedAddCommGroup :
    NormedAddCommGroup TensorEnd :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorEndNormedAddCommGroup

local instance tensorEndNormedSpace : NormedSpace Real TensorEnd :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorEndNormedSpace

private abbrev TensorTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] TensorEnd

local instance tensorTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup TensorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorTransitionFirstDerivativeNormedSpace :
    NormedSpace Real TensorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev BundleIndex :=
  ThroatMetricSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private def bundleOverlap
    (first second : BundleIndex period hPeriod) :
    Set (EffectiveThroat period hPeriod) :=
  throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
    throatMetricSecondOrderJetBundleBaseSet period hPeriod second

/-- Identity coefficients used only to totalize a semidirect change away
from its double overlap. -/
def identityMetricFramedSecondOrderJetSemidirectChange :
    FramedSecondOrderJetSemidirectChange ThroatCoverCoordinates
      TensorModel where
  baseFirst := ContinuousLinearMap.id Real ThroatCoverCoordinates
  baseSecond := 0
  baseSecond_symmetric first second := by simp
  fiberValue := ContinuousLinearMap.id Real
    TensorModel
  fiberFirst := 0
  fiberSecond := 0
  fiberSecond_symmetric first second := by simp

/-- A globally defined coefficient family whose overlap branch is the
metric semidirect change. -/
def throatMetricSecondOrderJetBundleTotalChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    FramedSecondOrderJetSemidirectChange ThroatCoverCoordinates
      TensorModel := by
  classical
  exact if hCurrent : current ∈ bundleOverlap period hPeriod first second then
      throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
        first second ⟨current, hCurrent⟩
    else
      identityMetricFramedSecondOrderJetSemidirectChange

private theorem baseFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (throatGaugeBaseChartTransition period hPeriod second.2 first.2)
          (extChartAt throatCoverModelWithCorners second.2 current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈
      (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatGaugeBaseChartTransition_fderiv_contDiffAt_infty period hPeriod
      second.2 first.2 current hCurrent.2.2
        hCurrent.1.2).contMDiffAt.comp current
          (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

private theorem baseSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod second.2 first.2))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈
      (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatGaugeBaseChartTransition_secondFDeriv_contDiffAt_infty
      period hPeriod second.2 first.2 current hCurrent.2.2
        hCurrent.1.2).contMDiffAt.comp current
          (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

private theorem fiberValue_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, TensorEnd) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (throatCovariantTwoTensorFrameTransitionAt period hPeriod
          first.1 second.1 current : TensorEnd))
      (bundleOverlap period hPeriod first second) :=
  (throatCovariantTwoTensorTrivializationTransitionAt_contMDiffOn
    period hPeriod first.1 second.1).mono (by
      intro current hCurrent
      exact ⟨hCurrent.1.1, hCurrent.2.1⟩)

private theorem fiberFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, TensorTransitionFirstDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            first.1 second.1 second.2)
          (extChartAt throatCoverModelWithCorners second.2 current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈
      (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatCovariantTwoTensorTransitionCenteredChart_fderiv_contDiffAt_infty
      period hPeriod first.1 second.1 second.2 current
        ⟨hCurrent.1.1, hCurrent.2.1⟩
        hCurrent.2.2).contMDiffAt.comp current
          (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

private theorem fiberSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        TensorTransitionFirstDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
              first.1 second.1 second.2))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈
      (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatCovariantTwoTensorTransitionCenteredChart_secondFDeriv_contDiffAt_infty
      period hPeriod first.1 second.1 second.2 current
        ⟨hCurrent.1.1, hCurrent.2.1⟩
        hCurrent.2.2).contMDiffAt.comp current
          (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

private theorem totalChange_baseFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current ↦
        (throatMetricSecondOrderJetBundleTotalChange period hPeriod
          first second current).baseFirst)
      (bundleOverlap period hPeriod first second) := by
  apply (baseFirst_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatMetricSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [
    throatMetricSecondOrderJetBundleChangeOnOverlap,
    throatMetricSecondOrderJetFrameChartAt]

private theorem totalChange_baseSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current ↦
        (throatMetricSecondOrderJetBundleTotalChange period hPeriod
          first second current).baseSecond)
      (bundleOverlap period hPeriod first second) := by
  apply (baseSecond_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatMetricSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [
    throatMetricSecondOrderJetBundleChangeOnOverlap,
    throatMetricSecondOrderJetFrameChartAt]

private theorem totalChange_fiberValue_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, TensorEnd) ∞
      (fun current ↦
        (throatMetricSecondOrderJetBundleTotalChange period hPeriod
          first second current).fiberValue)
      (bundleOverlap period hPeriod first second) := by
  apply (fiberValue_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatMetricSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [
    throatMetricSecondOrderJetBundleChangeOnOverlap,
    throatMetricSecondOrderJetFrameChartAt]

private theorem totalChange_fiberFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, TensorTransitionFirstDerivative) ∞
      (fun current ↦
        (throatMetricSecondOrderJetBundleTotalChange period hPeriod
          first second current).fiberFirst)
      (bundleOverlap period hPeriod first second) := by
  apply (fiberFirst_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatMetricSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [
    throatMetricSecondOrderJetBundleChangeOnOverlap,
    throatMetricSecondOrderJetFrameChartAt]

private theorem totalChange_fiberSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        TensorTransitionFirstDerivative) ∞
      (fun current ↦
        (throatMetricSecondOrderJetBundleTotalChange period hPeriod
          first second current).fiberSecond)
      (bundleOverlap period hPeriod first second) := by
  apply (fiberSecond_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatMetricSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatMetricTargetFrameTransitionSecondDerivativeAt,
    throatMetricSecondOrderJetBundleChangeOnOverlap,
    throatMetricSecondOrderJetFrameChartAt]

/-- The totalized semidirect transport is smooth on the double overlap. -/
theorem throatMetricSecondOrderJetBundleTotalTransport_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, MetricJet →L[Real] MetricJet) ∞
      (fun current ↦
        (throatMetricSecondOrderJetBundleTotalChange period hPeriod
          first second current).toContinuousLinearMap)
      (bundleOverlap period hPeriod first second) :=
  contMDiffOn_semidirectTransport
    (throatMetricSecondOrderJetBundleTotalChange period hPeriod first second)
    (totalChange_baseFirst_contMDiffOn period hPeriod first second)
    (totalChange_baseSecond_contMDiffOn period hPeriod first second)
    (totalChange_fiberValue_contMDiffOn period hPeriod first second)
    (totalChange_fiberFirst_contMDiffOn period hPeriod first second)
    (totalChange_fiberSecond_contMDiffOn period hPeriod first second)

/-- Concrete second-jet coordinate changes are smooth on every double overlap. -/
theorem throatMetricSecondOrderJetBundleCoordChange_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, MetricJet →L[Real] MetricJet) ∞
      (throatMetricSecondOrderJetBundleCoordChange period hPeriod first second)
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) := by
  apply
    (throatMetricSecondOrderJetBundleTotalTransport_contMDiffOn
      period hPeriod first second).congr
  intro current hCurrent
  rw [throatMetricSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second current hCurrent]
  rw [throatMetricSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  rfl

end
end P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D
end JanusFormal

