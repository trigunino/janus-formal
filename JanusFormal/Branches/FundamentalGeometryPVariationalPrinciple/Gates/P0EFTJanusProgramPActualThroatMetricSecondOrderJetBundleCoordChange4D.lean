import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransportGroupoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportContinuity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetTransitionSmoothRegularity4D

/-!
# Coordinate changes for the throat metric second-jet atlas

The metric semidirect transport is installed on every double frame/chart
overlap and totalized by the identity away from the overlap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D

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
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportContinuity4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransportGroupoid4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
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

local instance tensorEndNormedAddCommGroup : NormedAddCommGroup TensorEnd :=
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

/-- Points at which two metric frame/chart indices are simultaneously valid. -/
abbrev ThroatMetricSecondOrderJetBundleOverlap
    (first second : BundleIndex period hPeriod) :=
  {current : EffectiveThroat period hPeriod //
    current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second}

/-- Frozen metric semidirect coefficients on a double atlas overlap. -/
def throatMetricSecondOrderJetBundleChangeOnOverlap
    (first second : BundleIndex period hPeriod)
    (point : ThroatMetricSecondOrderJetBundleOverlap period hPeriod
      first second) :
    FramedSecondOrderJetSemidirectChange ThroatCoverCoordinates TensorModel :=
  throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
    (throatMetricSecondOrderJetFrameChartAt period hPeriod first point
      point.property.1)
    (throatMetricSecondOrderJetFrameChartAt period hPeriod second point
      point.property.2)

/-- Continuous-linear metric second-jet transport on one double overlap. -/
def throatMetricSecondOrderJetBundleTransportOnOverlap
    (first second : BundleIndex period hPeriod)
    (point : ThroatMetricSecondOrderJetBundleOverlap period hPeriod
      first second) : MetricJet →L[Real] MetricJet :=
  (throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
    first second point).toContinuousLinearMap

/-- Totalized coordinate change; only its overlap restriction is used. -/
def throatMetricSecondOrderJetBundleCoordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) : MetricJet →L[Real] MetricJet := by
  classical
  exact if hCurrent : current ∈
        throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
          throatMetricSecondOrderJetBundleBaseSet period hPeriod second then
      throatMetricSecondOrderJetBundleTransportOnOverlap period hPeriod
        first second ⟨current, hCurrent⟩
    else
      ContinuousLinearMap.id Real MetricJet

theorem throatMetricSecondOrderJetBundleCoordChange_eq_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) :
    throatMetricSecondOrderJetBundleCoordChange period hPeriod
        first second current =
      throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
        (throatMetricSecondOrderJetFrameChartAt period hPeriod first
          current hCurrent.1)
        (throatMetricSecondOrderJetFrameChartAt period hPeriod second
          current hCurrent.2) := by
  simp only [throatMetricSecondOrderJetBundleCoordChange, dif_pos hCurrent,
    throatMetricSecondOrderJetBundleTransportOnOverlap,
    throatMetricSecondOrderJetBundleChangeOnOverlap,
    throatMetricSecondOrderJetSemidirectTransportAt]

@[simp]
theorem throatMetricSecondOrderJetBundleCoordChange_apply_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second)
    (jet : MetricJet) :
    throatMetricSecondOrderJetBundleCoordChange period hPeriod
        first second current jet =
      throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
        (throatMetricSecondOrderJetFrameChartAt period hPeriod first
          current hCurrent.1)
        (throatMetricSecondOrderJetFrameChartAt period hPeriod second
          current hCurrent.2) jet := by
  exact congrArg (fun transport : MetricJet →L[Real] MetricJet ↦ transport jet)
    (throatMetricSecondOrderJetBundleCoordChange_eq_of_mem
      period hPeriod first second current hCurrent)

@[simp]
theorem throatMetricSecondOrderJetBundleCoordChange_self
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :
    throatMetricSecondOrderJetBundleCoordChange period hPeriod
        index index current =
      ContinuousLinearMap.id Real MetricJet := by
  rw [throatMetricSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod index index current ⟨hCurrent, hCurrent⟩]
  exact throatMetricSecondOrderJetSemidirectTransportAt_self period hPeriod _

theorem throatMetricSecondOrderJetBundleCoordChange_comp
    (first middle last : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod middle ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod last) :
    (throatMetricSecondOrderJetBundleCoordChange period hPeriod
        middle last current).comp
        (throatMetricSecondOrderJetBundleCoordChange period hPeriod
          first middle current) =
      throatMetricSecondOrderJetBundleCoordChange period hPeriod
        first last current := by
  rw [throatMetricSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod middle last current ⟨hCurrent.1.2, hCurrent.2⟩]
  rw [throatMetricSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first middle current ⟨hCurrent.1.1, hCurrent.1.2⟩]
  rw [throatMetricSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first last current ⟨hCurrent.1.1, hCurrent.2⟩]
  exact (throatMetricSecondOrderJetSemidirectTransportAt_comp period hPeriod
    (throatMetricSecondOrderJetFrameChartAt period hPeriod first
      current hCurrent.1.1)
    (throatMetricSecondOrderJetFrameChartAt period hPeriod middle
      current hCurrent.1.2)
    (throatMetricSecondOrderJetFrameChartAt period hPeriod last
      current hCurrent.2)).symm

theorem throatMetricSecondOrderJetBundleCoordChange_inverse_comp
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatMetricSecondOrderJetBundleCoordChange period hPeriod
        second first current).comp
        (throatMetricSecondOrderJetBundleCoordChange period hPeriod
          first second current) =
      ContinuousLinearMap.id Real MetricJet := by
  rw [throatMetricSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod second first current ⟨hCurrent.2, hCurrent.1⟩]
  rw [throatMetricSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second current hCurrent]
  exact throatMetricSecondOrderJetSemidirectTransportAt_inverse_comp
    period hPeriod _ _

theorem throatMetricSecondOrderJetBundleCoordChange_comp_inverse
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatMetricSecondOrderJetBundleCoordChange period hPeriod
        first second current).comp
        (throatMetricSecondOrderJetBundleCoordChange period hPeriod
          second first current) =
      ContinuousLinearMap.id Real MetricJet := by
  rw [throatMetricSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second current hCurrent]
  rw [throatMetricSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod second first current ⟨hCurrent.2, hCurrent.1⟩]
  exact throatMetricSecondOrderJetSemidirectTransportAt_comp_inverse
    period hPeriod _ _

/-! ## Continuity on double overlaps -/

private theorem bundleChangeOnOverlap_baseFirst_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseFirst) := by
  have hContinuous : Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        fderiv Real
          (throatGaugeBaseChartTransition period hPeriod second.2 first.2)
          (extChartAt throatCoverModelWithCorners second.2 point)) := by
    apply continuous_iff_continuousAt.mpr
    intro point
    have hEffective : ContinuousAt (fun current :
        EffectiveThroat period hPeriod ↦
          fderiv Real
            (throatGaugeBaseChartTransition period hPeriod second.2 first.2)
            (extChartAt throatCoverModelWithCorners second.2 current)) point :=
      (throatGaugeBaseChartTransition_fderiv_contDiffAt_infty period hPeriod
        second.2 first.2 point point.property.2.2
          point.property.1.2).continuousAt.comp
        (continuousAt_extChartAt' point.property.2.2)
    convert hEffective.comp continuousAt_subtype_val using 1
    rfl
  simpa [throatMetricSecondOrderJetBundleChangeOnOverlap,
    throatMetricSecondOrderJetFrameChartAt] using hContinuous

private theorem bundleChangeOnOverlap_baseSecond_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseSecond) := by
  have hContinuous : Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        fderiv Real
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod second.2 first.2))
          (extChartAt throatCoverModelWithCorners second.2 point)) := by
    apply continuous_iff_continuousAt.mpr
    intro point
    have hEffective : ContinuousAt (fun current :
        EffectiveThroat period hPeriod ↦
          fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                second.2 first.2))
            (extChartAt throatCoverModelWithCorners second.2 current)) point :=
      (throatGaugeBaseChartTransition_secondFDeriv_contDiffAt_infty
        period hPeriod second.2 first.2 point point.property.2.2
          point.property.1.2).continuousAt.comp
        (continuousAt_extChartAt' point.property.2.2)
    convert hEffective.comp continuousAt_subtype_val using 1
    rfl
  simpa [throatMetricSecondOrderJetBundleChangeOnOverlap,
    throatMetricSecondOrderJetFrameChartAt] using hContinuous

private theorem bundleChangeOnOverlap_fiberValue_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberValue) := by
  apply continuous_iff_continuousAt.mpr
  intro point
  have hOverlap :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) first.1).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) second.1).baseSet ∈
        𝓝 (point : EffectiveThroat period hPeriod) :=
    ((trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) first.1).open_baseSet.inter
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) second.1).open_baseSet).mem_nhds
          ⟨point.property.1.1, point.property.2.1⟩
  have hEffective :=
    ((throatCovariantTwoTensorTrivializationTransitionAt_contMDiffOn
      period hPeriod first.1 second.1).contMDiffAt hOverlap).continuousAt
  change ContinuousAt (fun nearby :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatCovariantTwoTensorFrameTransitionAt period hPeriod
          first.1 second.1 nearby : TensorEnd)) point
  convert hEffective.comp continuousAt_subtype_val using 1
  rfl

private theorem bundleChangeOnOverlap_fiberFirst_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberFirst) := by
  have hContinuous : Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            first.1 second.1 second.2)
          (extChartAt throatCoverModelWithCorners second.2 point)) := by
    apply continuous_iff_continuousAt.mpr
    intro point
    have hEffective : ContinuousAt (fun current :
        EffectiveThroat period hPeriod ↦
          fderiv Real
            (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
              first.1 second.1 second.2)
            (extChartAt throatCoverModelWithCorners second.2 current)) point :=
      (throatCovariantTwoTensorTransitionCenteredChart_fderiv_contDiffAt_infty
        period hPeriod first.1 second.1 second.2 point
          ⟨point.property.1.1, point.property.2.1⟩
          point.property.2.2).continuousAt.comp
        (continuousAt_extChartAt' point.property.2.2)
    convert hEffective.comp continuousAt_subtype_val using 1
    rfl
  simpa [throatMetricSecondOrderJetBundleChangeOnOverlap,
    throatMetricSecondOrderJetFrameChartAt] using hContinuous

private theorem bundleChangeOnOverlap_fiberSecond_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberSecond) := by
  have hContinuous : Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        fderiv Real
          (fderiv Real
            (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
              first.1 second.1 second.2))
          (extChartAt throatCoverModelWithCorners second.2 point)) := by
    apply continuous_iff_continuousAt.mpr
    intro point
    have hEffective : ContinuousAt (fun current :
        EffectiveThroat period hPeriod ↦
          fderiv Real
            (fderiv Real
              (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
                first.1 second.1 second.2))
            (extChartAt throatCoverModelWithCorners second.2 current)) point :=
      (throatCovariantTwoTensorTransitionCenteredChart_secondFDeriv_contDiffAt_infty
        period hPeriod first.1 second.1 second.2 point
          ⟨point.property.1.1, point.property.2.1⟩
          point.property.2.2).continuousAt.comp
        (continuousAt_extChartAt' point.property.2.2)
    convert hEffective.comp continuousAt_subtype_val using 1
    rfl
  simpa [throatMetricSecondOrderJetBundleChangeOnOverlap,
    throatMetricTargetFrameTransitionSecondDerivativeAt,
    throatMetricSecondOrderJetFrameChartAt] using hContinuous

theorem throatMetricSecondOrderJetBundleTransportOnOverlap_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (throatMetricSecondOrderJetBundleTransportOnOverlap
      period hPeriod first second) := by
  exact continuous_semidirectTransport
    (throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
      first second)
    (bundleChangeOnOverlap_baseFirst_continuous period hPeriod first second)
    (bundleChangeOnOverlap_baseSecond_continuous period hPeriod first second)
    (bundleChangeOnOverlap_fiberValue_continuous period hPeriod first second)
    (bundleChangeOnOverlap_fiberFirst_continuous period hPeriod first second)
    (bundleChangeOnOverlap_fiberSecond_continuous period hPeriod first second)

theorem throatMetricSecondOrderJetBundleCoordChange_continuousOn
    (first second : BundleIndex period hPeriod) :
    ContinuousOn
      (throatMetricSecondOrderJetBundleCoordChange period hPeriod first second)
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) := by
  rw [continuousOn_iff_continuous_restrict]
  have hContinuous :=
    throatMetricSecondOrderJetBundleTransportOnOverlap_continuous
      period hPeriod first second
  convert hContinuous using 1
  funext point
  change throatMetricSecondOrderJetBundleCoordChange period hPeriod
      first second point =
    throatMetricSecondOrderJetBundleTransportOnOverlap period hPeriod
      first second point
  rw [throatMetricSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second point point.property]
  rfl

end
end P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D
end JanusFormal
