import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransportGroupoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportContinuity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetTransitionSmoothRegularity4D

/-!
# Coordinate changes for the throat SpinC second-jet atlas

The SpinC semidirect transport is installed on every double
trivialization/chart overlap and totalized by the identity away from it.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChange4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportContinuity4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransportGroupoid4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetTransitionSmoothRegularity4D

variable (period : Real) (hPeriod : period ≠ 0)
variable (choice : NormalRootChoice)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCModel := D9DoubledMatterFiber

private abbrev SpinCJet :=
  FramedSecondOrderJet ThroatCoverCoordinates SpinCModel

private abbrev SpinCEnd := SpinCModel →L[Real] SpinCModel

local instance spinCEndNormedAddCommGroup : NormedAddCommGroup SpinCEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCEndNormedSpace : NormedSpace Real SpinCEnd :=
  ContinuousLinearMap.toNormedSpace

private abbrev SpinCTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] SpinCEnd

local instance spinCTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCTransitionFirstDerivativeNormedSpace :
    NormedSpace Real SpinCTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Points at which two SpinC frame/chart indices are simultaneously valid. -/
abbrev ThroatSpinCSecondOrderJetBundleOverlap
    (first second : BundleIndex period hPeriod) :=
  {current : EffectiveThroat period hPeriod //
    current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second}

/-- Frozen SpinC semidirect coefficients on a double atlas overlap. -/
def throatSpinCSecondOrderJetBundleChangeOnOverlap
    (first second : BundleIndex period hPeriod)
    (point : ThroatSpinCSecondOrderJetBundleOverlap period hPeriod
      first second) :
    FramedSecondOrderJetSemidirectChange ThroatCoverCoordinates SpinCModel :=
  throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
    (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod first point
      point.property.1)
    (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod second point
      point.property.2)

/-- Continuous-linear SpinC second-jet transport on one double overlap. -/
def throatSpinCSecondOrderJetBundleTransportOnOverlap
    (first second : BundleIndex period hPeriod)
    (point : ThroatSpinCSecondOrderJetBundleOverlap period hPeriod
      first second) : SpinCJet →L[Real] SpinCJet :=
  (throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
    first second point).toContinuousLinearMap

/-- Totalized coordinate change; only its overlap restriction is used. -/
def throatSpinCSecondOrderJetBundleCoordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) : SpinCJet →L[Real] SpinCJet := by
  classical
  exact if hCurrent : current ∈
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
          throatSpinCSecondOrderJetBundleBaseSet period hPeriod second then
      throatSpinCSecondOrderJetBundleTransportOnOverlap period hPeriod choice
        first second ⟨current, hCurrent⟩
    else
      ContinuousLinearMap.id Real SpinCJet

theorem throatSpinCSecondOrderJetBundleCoordChange_eq_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) :
    throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
        first second current =
      throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
        (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod first
          current hCurrent.1)
        (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod second
          current hCurrent.2) := by
  simp only [throatSpinCSecondOrderJetBundleCoordChange, dif_pos hCurrent,
    throatSpinCSecondOrderJetBundleTransportOnOverlap,
    throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectTransportAt]

@[simp]
theorem throatSpinCSecondOrderJetBundleCoordChange_apply_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second)
    (jet : SpinCJet) :
    throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
        first second current jet =
      throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
        (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod first
          current hCurrent.1)
        (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod second
          current hCurrent.2) jet := by
  exact congrArg (fun transport : SpinCJet →L[Real] SpinCJet ↦ transport jet)
    (throatSpinCSecondOrderJetBundleCoordChange_eq_of_mem
      period hPeriod choice first second current hCurrent)

@[simp]
theorem throatSpinCSecondOrderJetBundleCoordChange_self
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
        index index current =
      ContinuousLinearMap.id Real SpinCJet := by
  rw [throatSpinCSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice index index current ⟨hCurrent, hCurrent⟩]
  exact throatSpinCSecondOrderJetSemidirectTransportAt_self
    period hPeriod choice _

theorem throatSpinCSecondOrderJetBundleCoordChange_comp
    (first middle last : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod middle ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod last) :
    (throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
        middle last current).comp
        (throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
          first middle current) =
      throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
        first last current := by
  rw [throatSpinCSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice middle last current ⟨hCurrent.1.2, hCurrent.2⟩]
  rw [throatSpinCSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice first middle current ⟨hCurrent.1.1, hCurrent.1.2⟩]
  rw [throatSpinCSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice first last current ⟨hCurrent.1.1, hCurrent.2⟩]
  exact (throatSpinCSecondOrderJetSemidirectTransportAt_comp period hPeriod choice
    (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod first
      current hCurrent.1.1)
    (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod middle
      current hCurrent.1.2)
    (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod last
      current hCurrent.2)).symm

theorem throatSpinCSecondOrderJetBundleCoordChange_inverse_comp
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
        second first current).comp
        (throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
          first second current) =
      ContinuousLinearMap.id Real SpinCJet := by
  rw [throatSpinCSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice second first current ⟨hCurrent.2, hCurrent.1⟩]
  rw [throatSpinCSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice first second current hCurrent]
  exact throatSpinCSecondOrderJetSemidirectTransportAt_inverse_comp
    period hPeriod choice _ _

theorem throatSpinCSecondOrderJetBundleCoordChange_comp_inverse
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
        first second current).comp
        (throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
          second first current) =
      ContinuousLinearMap.id Real SpinCJet := by
  rw [throatSpinCSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice first second current hCurrent]
  rw [throatSpinCSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice second first current ⟨hCurrent.2, hCurrent.1⟩]
  exact throatSpinCSecondOrderJetSemidirectTransportAt_comp_inverse
    period hPeriod choice _ _

/-! ## Continuity on double overlaps -/

private theorem bundleChangeOnOverlap_baseFirst_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).baseFirst) := by
  have hContinuous :=
    (throatSpinCSecondOrderJet_baseFirst_contMDiffOn
      period hPeriod first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
    ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
      fderiv Real
        (P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D.throatGaugeBaseChartTransition
          period hPeriod second.2 first.2)
        (extChartAt throatCoverModelWithCorners second.2 point)) at hContinuous
  simpa only [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectChangeAt_baseFirst,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_chartAnchor] using
      hContinuous

private theorem bundleChangeOnOverlap_baseSecond_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).baseSecond) := by
  have hContinuous :=
    (throatSpinCSecondOrderJet_baseSecond_contMDiffOn
      period hPeriod first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
    ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
      fderiv Real
        (fderiv Real
          (P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D.throatGaugeBaseChartTransition
            period hPeriod second.2 first.2))
        (extChartAt throatCoverModelWithCorners second.2 point)) at hContinuous
  simpa only [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectChangeAt_baseSecond,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_chartAnchor] using
      hContinuous

private theorem bundleChangeOnOverlap_fiberValue_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).fiberValue) := by
  have hContinuous :=
    (throatSpinCSecondOrderJet_fiberValue_contMDiffOn
      period hPeriod choice first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
    ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
      d9PrimitiveSpinCCoordChange period hPeriod choice first.1 second.1
        point) at hContinuous
  simpa only [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberValue,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_trivializationIndex]
      using hContinuous

private theorem bundleChangeOnOverlap_fiberFirst_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).fiberFirst) := by
  have hContinuous :=
    (throatSpinCSecondOrderJet_fiberFirst_contMDiffOn
      period hPeriod choice first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
    ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
      fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          first.1 second.1 second.2)
        (extChartAt throatCoverModelWithCorners second.2 point)) at hContinuous
  simpa only [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberFirst,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_trivializationIndex,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_chartAnchor] using
      hContinuous

private theorem bundleChangeOnOverlap_fiberSecond_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).fiberSecond) := by
  have hContinuous : ContinuousOn
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              first.1 second.1 second.2))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (throatSpinCSecondOrderJetBundleOverlap period hPeriod first second) :=
    (throatSpinCSecondOrderJet_fiberSecond_contMDiffOn
      period hPeriod choice first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
    ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
      fderiv Real
        (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            first.1 second.1 second.2))
        (extChartAt throatCoverModelWithCorners second.2 point)) at hContinuous
  simpa only [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberSecond,
    throatSpinCTargetTrivializationTransitionSecondDerivativeAt,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_trivializationIndex,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_chartAnchor] using
      hContinuous

theorem throatSpinCSecondOrderJetBundleTransportOnOverlap_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (throatSpinCSecondOrderJetBundleTransportOnOverlap
      period hPeriod choice first second) := by
  exact continuous_semidirectTransport
    (throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
      first second)
    (bundleChangeOnOverlap_baseFirst_continuous
      period hPeriod choice first second)
    (bundleChangeOnOverlap_baseSecond_continuous
      period hPeriod choice first second)
    (bundleChangeOnOverlap_fiberValue_continuous
      period hPeriod choice first second)
    (bundleChangeOnOverlap_fiberFirst_continuous
      period hPeriod choice first second)
    (bundleChangeOnOverlap_fiberSecond_continuous
      period hPeriod choice first second)

theorem throatSpinCSecondOrderJetBundleCoordChange_continuousOn
    (first second : BundleIndex period hPeriod) :
    ContinuousOn
      (throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
        first second)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) := by
  rw [continuousOn_iff_continuous_restrict]
  have hContinuous :=
    throatSpinCSecondOrderJetBundleTransportOnOverlap_continuous
      period hPeriod choice first second
  convert hContinuous using 1
  funext point
  change throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
      first second point =
    throatSpinCSecondOrderJetBundleTransportOnOverlap period hPeriod choice
      first second point
  rw [throatSpinCSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice first second point point.property]
  rfl

end
end P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChange4D
end JanusFormal
