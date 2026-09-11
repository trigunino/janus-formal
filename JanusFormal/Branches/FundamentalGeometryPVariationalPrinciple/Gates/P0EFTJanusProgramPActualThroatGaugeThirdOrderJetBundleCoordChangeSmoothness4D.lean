import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetContinuousLinearCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetTransitionSmoothRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D

/-!
# Smoothness of throat gauge third-jet coordinate changes

This gate upgrades continuity of the concrete semidirect coordinate changes
to `C∞` regularity on every double atlas overlap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChangeSmoothness4D

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
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
open P0EFTJanusProgramPActualThroatGaugeCovectorTransitionThirdDerivative4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetContinuousLinearCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetTransitionSmoothRegularity4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeJet :=
  FramedThirdOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

private abbrev BaseTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates

local instance baseTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup BaseTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance baseTransitionFirstDerivativeNormedSpace :
    NormedSpace Real BaseTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev BaseTransitionSecondDerivative :=
  ThroatCoverCoordinates →L[Real] BaseTransitionFirstDerivative

local instance baseTransitionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup BaseTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance baseTransitionSecondDerivativeNormedSpace :
    NormedSpace Real BaseTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

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

private abbrev BundleIndex :=
  ThroatGaugeSecondOrderJetBundleIndex period hPeriod

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
  throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
    throatGaugeSecondOrderJetBundleBaseSet period hPeriod second

/-- Identity coefficients used only to totalize a semidirect change away
from its double overlap. -/
def identityFramedThirdOrderJetSemidirectChange :
    FramedThirdOrderJetSemidirectChange ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates) where
  toFramedSecondOrderJetSemidirectChange :=
    { baseFirst := ContinuousLinearMap.id Real ThroatCoverCoordinates
      baseSecond := 0
      baseSecond_symmetric := by simp
      fiberValue := ContinuousLinearMap.id Real
        (FramedCovector ThroatCoverCoordinates)
      fiberFirst := 0
      fiberSecond := 0
      fiberSecond_symmetric := by simp }
  baseThird := 0
  baseThird_swap_first_second := by simp
  baseThird_swap_second_third := by simp
  fiberThird := 0
  fiberThird_swap_first_second := by simp
  fiberThird_swap_second_third := by simp

/-- A globally defined coefficient family whose overlap branch is the
geometric semidirect change. -/
def throatGaugeThirdOrderJetBundleTotalChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    FramedThirdOrderJetSemidirectChange ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates) := by
  classical
  exact if hCurrent : current ∈ bundleOverlap period hPeriod first second then
      throatGaugeThirdOrderJetSemidirectChangeAt period hPeriod
        (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod first
          current hCurrent.1)
        (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod second
          current hCurrent.2)
    else
      identityFramedThirdOrderJetSemidirectChange

private theorem baseFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, BaseTransitionFirstDerivative) ∞
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
      𝓘(Real, BaseTransitionSecondDerivative) ∞
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

private theorem baseThird_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        BaseTransitionSecondDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                second.2 first.2)))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈
      (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatGaugeBaseChartTransition_thirdFDeriv_contDiffAt_infty
      period hPeriod second.2 first.2 current hCurrent.2.2
        hCurrent.1.2).contMDiffAt.comp current
          (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

private theorem fiberValue_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, CovectorEnd) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          first.1 second.1 current : CovectorEnd))
      (bundleOverlap period hPeriod first second) :=
  (throatGaugeCovectorTrivializationTransitionAt_contMDiffOn
    period hPeriod first.1 second.1).mono (by
      intro current hCurrent
      exact ⟨hCurrent.1.1, hCurrent.2.1⟩)

private theorem fiberFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, CovectorTransitionFirstDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            first.1 second.1 second.2)
          (extChartAt throatCoverModelWithCorners second.2 current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈
      (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatGaugeCovectorTransitionCenteredChart_fderiv_contDiffAt_infty
      period hPeriod first.1 second.1 second.2 current
        ⟨hCurrent.1.1, hCurrent.2.1⟩
        hCurrent.2.2).contMDiffAt.comp current
          (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

private theorem fiberSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, CovectorTransitionSecondDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (throatGaugeCovectorTransitionCenteredChart period hPeriod
              first.1 second.1 second.2))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈
      (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatGaugeCovectorTransitionCenteredChart_secondFDeriv_contDiffAt_infty
      period hPeriod first.1 second.1 second.2 current
        ⟨hCurrent.1.1, hCurrent.2.1⟩
        hCurrent.2.2).contMDiffAt.comp current
          (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

private theorem fiberThird_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        CovectorTransitionSecondDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (fderiv Real
              (throatGaugeCovectorTransitionCenteredChart period hPeriod
                first.1 second.1 second.2)))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈
      (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatGaugeCovectorTransitionCenteredChart_thirdFDeriv_contDiffAt_infty
      period hPeriod first.1 second.1 second.2 current
        ⟨hCurrent.1.1, hCurrent.2.1⟩
        hCurrent.2.2).contMDiffAt.comp current
          (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

private theorem totalChange_baseFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, BaseTransitionFirstDerivative) ∞
      (fun current ↦
        (throatGaugeThirdOrderJetBundleTotalChange period hPeriod
          first second current).baseFirst)
      (bundleOverlap period hPeriod first second) := by
  apply (baseFirst_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatGaugeThirdOrderJetSemidirectChangeAt,
    zeroThroatGaugeSecondOrderJetPresentationAt]

private theorem totalChange_baseSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, BaseTransitionSecondDerivative) ∞
      (fun current ↦
        (throatGaugeThirdOrderJetBundleTotalChange period hPeriod
          first second current).baseSecond)
      (bundleOverlap period hPeriod first second) := by
  apply (baseSecond_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatGaugeThirdOrderJetSemidirectChangeAt,
    throatGaugeSecondOrderJetSemidirectChangeAt,
    zeroThroatGaugeSecondOrderJetPresentationAt]

private theorem totalChange_baseThird_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        BaseTransitionSecondDerivative) ∞
      (fun current ↦
        (throatGaugeThirdOrderJetBundleTotalChange period hPeriod
          first second current).baseThird)
      (bundleOverlap period hPeriod first second) := by
  apply (baseThird_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatGaugeThirdOrderJetSemidirectChangeAt,
    actualThroatConstantFiberThirdOrderJetBaseChangeAt,
    zeroThroatGaugeSecondOrderJetPresentationAt]

private theorem totalChange_fiberValue_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, CovectorEnd) ∞
      (fun current ↦
        (throatGaugeThirdOrderJetBundleTotalChange period hPeriod
          first second current).fiberValue)
      (bundleOverlap period hPeriod first second) := by
  apply (fiberValue_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatGaugeThirdOrderJetSemidirectChangeAt,
    zeroThroatGaugeSecondOrderJetPresentationAt]

private theorem totalChange_fiberFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, CovectorTransitionFirstDerivative) ∞
      (fun current ↦
        (throatGaugeThirdOrderJetBundleTotalChange period hPeriod
          first second current).fiberFirst)
      (bundleOverlap period hPeriod first second) := by
  apply (fiberFirst_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatGaugeThirdOrderJetSemidirectChangeAt,
    zeroThroatGaugeSecondOrderJetPresentationAt]

private theorem totalChange_fiberSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, CovectorTransitionSecondDerivative) ∞
      (fun current ↦
        (throatGaugeThirdOrderJetBundleTotalChange period hPeriod
          first second current).fiberSecond)
      (bundleOverlap period hPeriod first second) := by
  apply (fiberSecond_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatGaugeThirdOrderJetSemidirectChangeAt,
    throatGaugeCovectorTargetTransitionSecondDerivativeAt,
    zeroThroatGaugeSecondOrderJetPresentationAt]

private theorem totalChange_fiberThird_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        CovectorTransitionSecondDerivative) ∞
      (fun current ↦
        (throatGaugeThirdOrderJetBundleTotalChange period hPeriod
          first second current).fiberThird)
      (bundleOverlap period hPeriod first second) := by
  apply (fiberThird_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatGaugeThirdOrderJetSemidirectChangeAt,
    throatGaugeCovectorTargetTransitionThirdDerivativeAt,
    zeroThroatGaugeSecondOrderJetPresentationAt]

/-- The totalized semidirect transport is smooth on the double overlap. -/
theorem throatGaugeThirdOrderJetBundleTotalTransport_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, GaugeJet →L[Real] GaugeJet) ∞
      (fun current ↦
        (throatGaugeThirdOrderJetBundleTotalChange period hPeriod
          first second current).toContinuousLinearMap)
      (bundleOverlap period hPeriod first second) :=
  P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D.contMDiffOn_semidirectTransport
    (throatGaugeThirdOrderJetBundleTotalChange period hPeriod first second)
    (totalChange_baseFirst_contMDiffOn period hPeriod first second)
    (totalChange_baseSecond_contMDiffOn period hPeriod first second)
    (totalChange_baseThird_contMDiffOn period hPeriod first second)
    (totalChange_fiberValue_contMDiffOn period hPeriod first second)
    (totalChange_fiberFirst_contMDiffOn period hPeriod first second)
    (totalChange_fiberSecond_contMDiffOn period hPeriod first second)
    (totalChange_fiberThird_contMDiffOn period hPeriod first second)

/-- Concrete third-jet coordinate changes are smooth on every double overlap. -/
theorem throatGaugeThirdOrderJetBundleContinuousCoordChange_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, GaugeJet →L[Real] GaugeJet) ∞
      (throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
        first second)
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) := by
  apply
    (throatGaugeThirdOrderJetBundleTotalTransport_contMDiffOn
      period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  apply ContinuousLinearMap.ext
  intro jet
  rw [throatGaugeThirdOrderJetBundleContinuousCoordChange_apply]
  rw [throatGaugeThirdOrderJetBundleCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  rfl

end
end P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChangeSmoothness4D
end JanusFormal
