import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D

/-!
# Smoothness of throat gauge second-jet coordinate changes

This gate upgrades continuity of the concrete semidirect coordinate changes
to `C∞` regularity on every double atlas overlap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChangeSmoothness4D

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
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D
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

private def bundleOverlap
    (first second : BundleIndex period hPeriod) :
    Set (EffectiveThroat period hPeriod) :=
  throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
    throatGaugeSecondOrderJetBundleBaseSet period hPeriod second

/-- Identity coefficients used only to totalize a semidirect change away
from its double overlap. -/
def identityFramedSecondOrderJetSemidirectChange :
    FramedSecondOrderJetSemidirectChange ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates) where
  baseFirst := ContinuousLinearMap.id Real ThroatCoverCoordinates
  baseSecond := 0
  baseSecond_symmetric first second := by simp
  fiberValue := ContinuousLinearMap.id Real
    (FramedCovector ThroatCoverCoordinates)
  fiberFirst := 0
  fiberSecond := 0
  fiberSecond_symmetric first second := by simp

/-- A globally defined coefficient family whose overlap branch is the
geometric semidirect change. -/
def throatGaugeSecondOrderJetBundleTotalChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    FramedSecondOrderJetSemidirectChange ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates) := by
  classical
  exact if hCurrent : current ∈ bundleOverlap period hPeriod first second then
      throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
        first second ⟨current, hCurrent⟩
    else
      identityFramedSecondOrderJetSemidirectChange

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
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        CovectorTransitionFirstDerivative) ∞
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

private theorem totalChange_baseFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current ↦
        (throatGaugeSecondOrderJetBundleTotalChange period hPeriod
          first second current).baseFirst)
      (bundleOverlap period hPeriod first second) := by
  apply (baseFirst_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [
    throatGaugeSecondOrderJetBundleChangeOnOverlap,
    zeroThroatGaugeSecondOrderJetPresentationAt]

private theorem totalChange_baseSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current ↦
        (throatGaugeSecondOrderJetBundleTotalChange period hPeriod
          first second current).baseSecond)
      (bundleOverlap period hPeriod first second) := by
  apply (baseSecond_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [
    throatGaugeSecondOrderJetBundleChangeOnOverlap,
    zeroThroatGaugeSecondOrderJetPresentationAt]

private theorem totalChange_fiberValue_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, CovectorEnd) ∞
      (fun current ↦
        (throatGaugeSecondOrderJetBundleTotalChange period hPeriod
          first second current).fiberValue)
      (bundleOverlap period hPeriod first second) := by
  apply (fiberValue_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [
    throatGaugeSecondOrderJetBundleChangeOnOverlap,
    zeroThroatGaugeSecondOrderJetPresentationAt]

private theorem totalChange_fiberFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, CovectorTransitionFirstDerivative) ∞
      (fun current ↦
        (throatGaugeSecondOrderJetBundleTotalChange period hPeriod
          first second current).fiberFirst)
      (bundleOverlap period hPeriod first second) := by
  apply (fiberFirst_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [
    throatGaugeSecondOrderJetBundleChangeOnOverlap,
    zeroThroatGaugeSecondOrderJetPresentationAt]

private theorem totalChange_fiberSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        CovectorTransitionFirstDerivative) ∞
      (fun current ↦
        (throatGaugeSecondOrderJetBundleTotalChange period hPeriod
          first second current).fiberSecond)
      (bundleOverlap period hPeriod first second) := by
  apply (fiberSecond_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatGaugeCovectorTargetTransitionSecondDerivativeAt,
    throatGaugeSecondOrderJetBundleChangeOnOverlap,
    zeroThroatGaugeSecondOrderJetPresentationAt]

/-- The totalized semidirect transport is smooth on the double overlap. -/
theorem throatGaugeSecondOrderJetBundleTotalTransport_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, GaugeJet →L[Real] GaugeJet) ∞
      (fun current ↦
        (throatGaugeSecondOrderJetBundleTotalChange period hPeriod
          first second current).toContinuousLinearMap)
      (bundleOverlap period hPeriod first second) :=
  contMDiffOn_semidirectTransport
    (throatGaugeSecondOrderJetBundleTotalChange period hPeriod first second)
    (totalChange_baseFirst_contMDiffOn period hPeriod first second)
    (totalChange_baseSecond_contMDiffOn period hPeriod first second)
    (totalChange_fiberValue_contMDiffOn period hPeriod first second)
    (totalChange_fiberFirst_contMDiffOn period hPeriod first second)
    (totalChange_fiberSecond_contMDiffOn period hPeriod first second)

/-- Concrete second-jet coordinate changes are smooth on every double overlap. -/
theorem throatGaugeSecondOrderJetBundleCoordChange_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, GaugeJet →L[Real] GaugeJet) ∞
      (throatGaugeSecondOrderJetBundleCoordChange period hPeriod first second)
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) := by
  apply
    (throatGaugeSecondOrderJetBundleTotalTransport_contMDiffOn
      period hPeriod first second).congr
  intro current hCurrent
  rw [throatGaugeSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second current hCurrent]
  rw [throatGaugeSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  rfl

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChangeSmoothness4D
end JanusFormal
