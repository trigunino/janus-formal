import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransportGroupoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportContinuity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D

/-!
# Coordinate changes for the throat gauge second-jet atlas

The semidirect jet transport is installed on every double atlas overlap and
totalized by the identity away from that overlap.  Its groupoid and
continuity laws are proved here; the actual `VectorBundleCore` is left to the
next gate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D

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
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransportGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeJet :=
  FramedSecondOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

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

private abbrev BundleIndex :=
  ThroatGaugeSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The subtype of points at which two frame/chart pairs are simultaneously
valid. -/
abbrev ThroatGaugeSecondOrderJetBundleOverlap
    (first second : BundleIndex period hPeriod) :=
  {current : EffectiveThroat period hPeriod //
    current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second}

/-- Frozen semidirect coefficients on a double atlas overlap. -/
def throatGaugeSecondOrderJetBundleChangeOnOverlap
    (first second : BundleIndex period hPeriod)
    (point : ThroatGaugeSecondOrderJetBundleOverlap period hPeriod
      first second) :
    FramedSecondOrderJetSemidirectChange ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates) :=
  throatGaugeSecondOrderJetSemidirectChangeAt period hPeriod
    (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod first
      point point.property.1)
    (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod second
      point point.property.2)

/-- Continuous-linear transport on one double overlap. -/
def throatGaugeSecondOrderJetBundleTransportOnOverlap
    (first second : BundleIndex period hPeriod)
    (point : ThroatGaugeSecondOrderJetBundleOverlap period hPeriod
      first second) : GaugeJet →L[Real] GaugeJet :=
  (throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
    first second point).toContinuousLinearMap

/-- Totalized coordinate change.  Only its values on the double overlap are
used by the bundle core. -/
def throatGaugeSecondOrderJetBundleCoordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) : GaugeJet →L[Real] GaugeJet := by
  classical
  exact if hCurrent : current ∈
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
          throatGaugeSecondOrderJetBundleBaseSet period hPeriod second then
      throatGaugeSecondOrderJetBundleTransportOnOverlap period hPeriod
        first second ⟨current, hCurrent⟩
    else
      ContinuousLinearMap.id Real GaugeJet

theorem throatGaugeSecondOrderJetBundleCoordChange_eq_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) :
    throatGaugeSecondOrderJetBundleCoordChange period hPeriod
        first second current =
      throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
        (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod first
          current hCurrent.1)
        (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod second
          current hCurrent.2) := by
  simp only [throatGaugeSecondOrderJetBundleCoordChange, dif_pos hCurrent,
    throatGaugeSecondOrderJetBundleTransportOnOverlap,
    throatGaugeSecondOrderJetBundleChangeOnOverlap,
    throatGaugeSecondOrderJetSemidirectTransportAt]

@[simp]
theorem throatGaugeSecondOrderJetBundleCoordChange_apply_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second)
    (jet : GaugeJet) :
    throatGaugeSecondOrderJetBundleCoordChange period hPeriod
        first second current jet =
      throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
        (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod first
          current hCurrent.1)
        (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod second
          current hCurrent.2) jet := by
  exact congrArg (fun transport : GaugeJet →L[Real] GaugeJet ↦ transport jet)
    (throatGaugeSecondOrderJetBundleCoordChange_eq_of_mem
      period hPeriod first second current hCurrent)

@[simp]
theorem throatGaugeSecondOrderJetBundleCoordChange_self
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) :
    throatGaugeSecondOrderJetBundleCoordChange period hPeriod
        index index current =
      ContinuousLinearMap.id Real GaugeJet := by
  rw [throatGaugeSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod index index current ⟨hCurrent, hCurrent⟩]
  exact throatGaugeSecondOrderJetSemidirectTransportAt_self period hPeriod _

theorem throatGaugeSecondOrderJetBundleCoordChange_comp
    (first middle last : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod middle ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod last) :
    (throatGaugeSecondOrderJetBundleCoordChange period hPeriod
        middle last current).comp
        (throatGaugeSecondOrderJetBundleCoordChange period hPeriod
          first middle current) =
      throatGaugeSecondOrderJetBundleCoordChange period hPeriod
        first last current := by
  rw [throatGaugeSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod middle last current ⟨hCurrent.1.2, hCurrent.2⟩]
  rw [throatGaugeSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first middle current ⟨hCurrent.1.1, hCurrent.1.2⟩]
  rw [throatGaugeSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first last current ⟨hCurrent.1.1, hCurrent.2⟩]
  exact (throatGaugeSecondOrderJetSemidirectTransportAt_comp period hPeriod
    (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod first
      current hCurrent.1.1)
    (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod middle
      current hCurrent.1.2)
    (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod last
      current hCurrent.2)).symm

theorem throatGaugeSecondOrderJetBundleCoordChange_inverse_comp
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatGaugeSecondOrderJetBundleCoordChange period hPeriod
        second first current).comp
        (throatGaugeSecondOrderJetBundleCoordChange period hPeriod
          first second current) =
      ContinuousLinearMap.id Real GaugeJet := by
  rw [throatGaugeSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod second first current ⟨hCurrent.2, hCurrent.1⟩]
  rw [throatGaugeSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second current hCurrent]
  exact throatGaugeSecondOrderJetSemidirectTransportAt_inverse_comp
    period hPeriod _ _

/-! ## Continuity on overlaps -/

private theorem bundleChangeOnOverlap_baseFirst_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseFirst) := by
  have hContinuous : Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
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
  simpa [throatGaugeSecondOrderJetBundleChangeOnOverlap,
    zeroThroatGaugeSecondOrderJetPresentationAt] using hContinuous

private theorem bundleChangeOnOverlap_baseSecond_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseSecond) := by
  have hContinuous : Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
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
  simpa [throatGaugeSecondOrderJetBundleChangeOnOverlap,
    zeroThroatGaugeSecondOrderJetPresentationAt] using hContinuous

private theorem bundleChangeOnOverlap_fiberValue_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
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
    ((throatGaugeCovectorTrivializationTransitionAt_contMDiffOn
      period hPeriod first.1 second.1).contMDiffAt hOverlap).continuousAt
  change ContinuousAt (fun nearby :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          first.1 second.1 nearby :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates)) point
  convert hEffective.comp continuousAt_subtype_val using 1
  rfl

private theorem bundleChangeOnOverlap_fiberFirst_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberFirst) := by
  have hContinuous : Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            first.1 second.1 second.2)
          (extChartAt throatCoverModelWithCorners second.2 point)) := by
    apply continuous_iff_continuousAt.mpr
    intro point
    have hEffective : ContinuousAt (fun current :
        EffectiveThroat period hPeriod ↦
          fderiv Real
            (throatGaugeCovectorTransitionCenteredChart period hPeriod
              first.1 second.1 second.2)
            (extChartAt throatCoverModelWithCorners second.2 current)) point :=
      (throatGaugeCovectorTransitionCenteredChart_fderiv_contDiffAt_infty
        period hPeriod first.1 second.1 second.2 point
          ⟨point.property.1.1, point.property.2.1⟩
          point.property.2.2).continuousAt.comp
        (continuousAt_extChartAt' point.property.2.2)
    convert hEffective.comp continuousAt_subtype_val using 1
    rfl
  simpa [throatGaugeSecondOrderJetBundleChangeOnOverlap,
    zeroThroatGaugeSecondOrderJetPresentationAt] using hContinuous

private theorem bundleChangeOnOverlap_fiberSecond_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberSecond) := by
  have hContinuous : Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        fderiv Real
          (fderiv Real
            (throatGaugeCovectorTransitionCenteredChart period hPeriod
              first.1 second.1 second.2))
          (extChartAt throatCoverModelWithCorners second.2 point)) := by
    apply continuous_iff_continuousAt.mpr
    intro point
    have hEffective : ContinuousAt (fun current :
        EffectiveThroat period hPeriod ↦
          fderiv Real
            (fderiv Real
              (throatGaugeCovectorTransitionCenteredChart period hPeriod
                first.1 second.1 second.2))
            (extChartAt throatCoverModelWithCorners second.2 current)) point :=
      (throatGaugeCovectorTransitionCenteredChart_secondFDeriv_contDiffAt_infty
        period hPeriod first.1 second.1 second.2 point
          ⟨point.property.1.1, point.property.2.1⟩
          point.property.2.2).continuousAt.comp
        (continuousAt_extChartAt' point.property.2.2)
    convert hEffective.comp continuousAt_subtype_val using 1
    rfl
  simpa [throatGaugeSecondOrderJetBundleChangeOnOverlap,
    throatGaugeCovectorTargetTransitionSecondDerivativeAt,
    zeroThroatGaugeSecondOrderJetPresentationAt] using hContinuous

theorem throatGaugeSecondOrderJetBundleTransportOnOverlap_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (throatGaugeSecondOrderJetBundleTransportOnOverlap
      period hPeriod first second) := by
  exact continuous_semidirectTransport
    (throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
      first second)
    (bundleChangeOnOverlap_baseFirst_continuous period hPeriod first second)
    (bundleChangeOnOverlap_baseSecond_continuous period hPeriod first second)
    (bundleChangeOnOverlap_fiberValue_continuous period hPeriod first second)
    (bundleChangeOnOverlap_fiberFirst_continuous period hPeriod first second)
    (bundleChangeOnOverlap_fiberSecond_continuous period hPeriod first second)

theorem throatGaugeSecondOrderJetBundleCoordChange_continuousOn
    (first second : BundleIndex period hPeriod) :
    ContinuousOn
      (throatGaugeSecondOrderJetBundleCoordChange period hPeriod first second)
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) := by
  rw [continuousOn_iff_continuous_restrict]
  have hContinuous :=
    throatGaugeSecondOrderJetBundleTransportOnOverlap_continuous
      period hPeriod first second
  convert hContinuous using 1
  funext point
  change throatGaugeSecondOrderJetBundleCoordChange period hPeriod
      first second point =
    throatGaugeSecondOrderJetBundleTransportOnOverlap period hPeriod
      first second point
  rw [throatGaugeSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second point point.property]
  rfl

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D
end JanusFormal
