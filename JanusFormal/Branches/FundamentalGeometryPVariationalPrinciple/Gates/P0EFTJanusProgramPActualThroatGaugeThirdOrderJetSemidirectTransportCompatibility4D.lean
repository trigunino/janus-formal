import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartThirdOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPContinuousLinearMapThirdOrderLeibniz4D

/-!
# Compatibility of gauge third-jet semidirect transport

The actual third-order semidirect transport sends an extracted smooth gauge
jet to the extraction in the target frame and base chart. The lower jet is
recovered from the existing second-order local-representative compatibility;
only the third derivative is proved directly here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransportCompatibility4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 3000000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeFrameTransitionInBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartThirdOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPContinuousLinearMapThirdOrderLeibniz4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeCovector :=
  FramedCovector ThroatCoverCoordinates

private abbrev GaugeThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates GaugeCovector

private abbrev GaugeFirstDerivative :=
  ThroatCoverCoordinates →L[Real] GaugeCovector

local instance gaugeFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup GaugeFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeFirstDerivativeNormedSpace :
    NormedSpace Real GaugeFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev GaugeSecondDerivative :=
  ThroatCoverCoordinates →L[Real] GaugeFirstDerivative

local instance gaugeSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup GaugeSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeSecondDerivativeNormedSpace :
    NormedSpace Real GaugeSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev GaugePresentationAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatGaugeSecondOrderJetPresentationAt period hPeriod current

private abbrev GaugeEnd :=
  GaugeCovector →L[Real] GaugeCovector

local instance gaugeEndNormedAddCommGroup : NormedAddCommGroup GaugeEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeEndNormedSpace : NormedSpace Real GaugeEnd :=
  ContinuousLinearMap.toNormedSpace

private abbrev GaugeTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] GaugeEnd

local instance gaugeTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup GaugeTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeTransitionFirstDerivativeNormedSpace :
    NormedSpace Real GaugeTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev GaugeTransitionSecondDerivative :=
  ThroatCoverCoordinates →L[Real] GaugeTransitionFirstDerivative

local instance gaugeTransitionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup GaugeTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeTransitionSecondDerivativeNormedSpace :
    NormedSpace Real GaugeTransitionSecondDerivative :=
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

private theorem throatGaugeSecondOrderJetSemidirectTransportAt_extracted
    {current : EffectiveThroat period hPeriod}
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (source target : GaugePresentationAt period hPeriod current) :
    throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod source target
        (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component source.frameAnchor source.chartAnchor current
            source.frame_mem source.chart_mem) =
      throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
        component target.frameAnchor target.chartAnchor current
          target.frame_mem target.chart_mem := by
  let sourceIndex : ThroatGaugeSecondOrderJetBundleIndex period hPeriod :=
    (source.frameAnchor, source.chartAnchor)
  let targetIndex : ThroatGaugeSecondOrderJetBundleIndex period hPeriod :=
    (target.frameAnchor, target.chartAnchor)
  have hSource : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod sourceIndex :=
    ⟨source.frame_mem, source.chart_mem⟩
  have hTarget : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod targetIndex :=
    ⟨target.frame_mem, target.chart_mem⟩
  have hCompatibility :=
    actualThroatGaugeSecondOrderJetLocalRepresentative_coordChange
      period hPeriod potential component sourceIndex targetIndex current
        ⟨hSource, hTarget⟩
  rw [throatGaugeSecondOrderJetVectorBundleCore_coordChange,
    throatGaugeSecondOrderJetBundleCoordChange_apply_of_mem period hPeriod
      sourceIndex targetIndex current ⟨hSource, hTarget⟩] at hCompatibility
  simp only [actualThroatGaugeSecondOrderJetLocalRepresentative,
    dif_pos hSource, dif_pos hTarget] at hCompatibility
  change throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
      source target
        (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component source.frameAnchor source.chartAnchor current
            source.frame_mem source.chart_mem) =
    throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component target.frameAnchor target.chartAnchor current
        target.frame_mem target.chart_mem at hCompatibility
  exact hCompatibility

/-- Semidirect transport of an extracted smooth gauge third jet is exactly
the third jet extracted in the target frame and base chart. -/
theorem throatGaugeThirdOrderJetSemidirectTransportAt_extracted
    {current : EffectiveThroat period hPeriod}
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (source target : GaugePresentationAt period hPeriod current) :
    throatGaugeThirdOrderJetSemidirectTransportAt period hPeriod source target
        (throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
          component source.frameAnchor source.chartAnchor current
            source.frame_mem source.chart_mem) =
      throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
        component target.frameAnchor target.chartAnchor current
          target.frame_mem target.chart_mem := by
  let sourceRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      source.frameAnchor source.chartAnchor
  let sourceInTargetRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      source.frameAnchor target.chartAnchor
  let targetRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      target.frameAnchor target.chartAnchor
  let sourceJet :=
    throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
      component source.frameAnchor source.chartAnchor current source.frame_mem
        source.chart_mem
  let sourceInTargetJet :=
    throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
      component source.frameAnchor target.chartAnchor current source.frame_mem
        target.chart_mem
  let targetJet :=
    throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
      component target.frameAnchor target.chartAnchor current target.frame_mem
        target.chart_mem
  let baseTransition :=
    throatGaugeBaseChartTransition period hPeriod
      target.chartAnchor source.chartAnchor
  let fiberTransition :=
    throatGaugeCovectorTransitionCenteredChart period hPeriod
      source.frameAnchor target.frameAnchor target.chartAnchor
  let sourceCoordinate :=
    extChartAt throatCoverModelWithCorners source.chartAnchor current
  let targetCoordinate :=
    extChartAt throatCoverModelWithCorners target.chartAnchor current
  let Ainv := fderiv Real baseTransition targetCoordinate
  let Binv := fderiv Real (fderiv Real baseTransition) targetCoordinate
  let Cinv :=
    fderiv Real (fderiv Real (fderiv Real baseTransition)) targetCoordinate
  let D : GaugeEnd :=
    throatGaugeCovectorTrivializationTransitionAt period hPeriod
      source.frameAnchor target.frameAnchor current
  let E := fderiv Real fiberTransition targetCoordinate
  let F := fderiv Real (fderiv Real fiberTransition) targetCoordinate
  let G :=
    fderiv Real (fderiv Real (fderiv Real fiberTransition)) targetCoordinate
  change throatGaugeThirdOrderJetSemidirectTransportAt period hPeriod
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
    (throatGaugeCovectorCenteredChart_contDiffAt_infty_of_mem_baseSet
      period hPeriod potential component source.frameAnchor source.chartAnchor
        current source.frame_mem source.chart_mem).of_le
          contDiffThree_le_infty
  have hSourceAtRegularity :
      ContDiffAt Real 3 sourceRepresentative
        (baseTransition targetCoordinate) := by
    simpa only [hBaseAt] using hSourceRegularity
  have hSourceInTargetRegularity :
      ContDiffAt Real 3 sourceInTargetRepresentative targetCoordinate :=
    (throatGaugeCovectorCenteredChart_contDiffAt_infty_of_mem_baseSet
      period hPeriod potential component source.frameAnchor target.chartAnchor
        current source.frame_mem target.chart_mem).of_le
          contDiffThree_le_infty
  have hFiberRegularity :
      ContDiffAt Real 3 fiberTransition targetCoordinate :=
    (throatGaugeCovectorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod source.frameAnchor target.frameAnchor target.chartAnchor
        current hFrames target.chart_mem).of_le contDiffThree_le_infty
  have hSourceValue : sourceInTargetJet.value = sourceJet.value := by
    simp only [sourceInTargetJet, sourceJet,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_value]
  have hBaseFirst :
      sourceInTargetJet.firstDerivative =
        sourceJet.firstDerivative.comp Ainv := by
    simpa only [sourceInTargetJet, sourceJet, Ainv, baseTransition,
      targetCoordinate,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_firstDerivative,
      throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative] using
        throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative_transition
          period hPeriod potential component source.frameAnchor
            target.chartAnchor source.chartAnchor current source.frame_mem
              target.chart_mem source.chart_mem
  have hBaseSecond (first second : ThroatCoverCoordinates) :
      sourceInTargetJet.secondDerivative first second =
        sourceJet.secondDerivative (Ainv first) (Ainv second) +
          sourceJet.firstDerivative (Binv first second) := by
    simpa only [sourceInTargetJet, sourceJet, Ainv, Binv, baseTransition,
      targetCoordinate,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_firstDerivative,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_secondDerivative,
      throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative,
      throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative] using
        throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative_transition_apply
          period hPeriod potential component source.frameAnchor
            target.chartAnchor source.chartAnchor current source.frame_mem
              target.chart_mem source.chart_mem first second
  have hBaseGerm : sourceInTargetRepresentative =ᶠ[𝓝 targetCoordinate]
      sourceRepresentative ∘ baseTransition := by
    simpa only [sourceInTargetRepresentative, sourceRepresentative,
      baseTransition, targetCoordinate] using
      throatGaugeCovectorCenteredChart_baseChartTransition_eventuallyEq
        period hPeriod potential component source.frameAnchor
          target.chartAnchor source.chartAnchor current target.chart_mem
            source.chart_mem
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
            ThroatCoverCoordinates →L[Real] GaugeCovector ↦
        derivative first second third) hThirdDerivativeGerm
    have hFormula := third_fderiv_comp_apply baseTransition
      sourceRepresentative targetCoordinate hBaseRegularity
        hSourceAtRegularity first second third
    rw [hBaseAt] at hFormula
    have hCombined := hApplied.trans hFormula
    simpa only [sourceInTargetJet, sourceJet,
      sourceInTargetRepresentative, sourceRepresentative, Ainv, Binv, Cinv,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_firstDerivative,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_secondDerivative,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_thirdDerivative] using
        hCombined
  have hFiberGerm :
      (fun coordinate => fiberTransition coordinate
        (sourceInTargetRepresentative coordinate)) =ᶠ[𝓝 targetCoordinate]
        targetRepresentative := by
    simpa only [fiberTransition, sourceInTargetRepresentative,
      targetRepresentative, targetCoordinate] using
      throatGaugeCovectorCenteredChart_frameTransition_eventuallyEq_of_mem_source
        period hPeriod potential component source.frameAnchor
          target.frameAnchor target.chartAnchor current hFrames target.chart_mem
  have hFiberAt : fiberTransition targetCoordinate = D := by
    simp only [fiberTransition, targetCoordinate, D,
      throatGaugeCovectorTransitionCenteredChart, hCoordinateInverse]
  have hSourceInTargetValueAt :
      sourceInTargetRepresentative targetCoordinate =
        sourceInTargetJet.value := by
    simp only [sourceInTargetRepresentative, sourceInTargetJet,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_value,
      throatGaugeCovectorCenteredChart, hCoordinateInverse]
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
            ThroatCoverCoordinates →L[Real] GaugeCovector ↦
        derivative first second third) hThirdDerivativeGerm
    have hProduct := third_fderiv_clm_apply_apply fiberTransition
      sourceInTargetRepresentative targetCoordinate first second third
        hFiberRegularity hSourceInTargetRegularity
    have hCombined := hApplied.symm.trans hProduct
    rw [hFiberAt, hSourceInTargetValueAt] at hCombined
    simpa only [targetJet, sourceInTargetJet, targetRepresentative,
      sourceInTargetRepresentative, targetCoordinate, E, F, G,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_value,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_firstDerivative,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_secondDerivative,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_thirdDerivative] using
        hCombined
  apply FramedThirdOrderJet.ext_components
  · simpa only [sourceJet, targetJet,
      throatGaugeThirdOrderJetSemidirectTransportAt_truncate,
      throatGaugeCovectorThirdOrderJetInBaseChartAt_truncate] using
      throatGaugeSecondOrderJetSemidirectTransportAt_extracted period hPeriod
        potential component source target
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    apply ContinuousLinearMap.ext
    intro third
    have hTransportThird :
        (throatGaugeThirdOrderJetSemidirectTransportAt period hPeriod
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
    rw [hTransportThird, hFiberThird first second third,
      hBaseThird first second third, hBaseSecond second third,
      hBaseSecond first third, hBaseSecond first second, hBaseFirst,
      hSourceValue]
    simp only [map_add, ContinuousLinearMap.comp_apply]
    abel

/-- Physical Candidate-A gauge data is the canonical specialization of the
generic third-order compatibility theorem. -/
theorem globalCandidateAThroatGaugeThirdOrderJetSemidirectTransportAt_extracted
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {current : EffectiveThroat period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (source target : GaugePresentationAt period hPeriod current) :
    throatGaugeThirdOrderJetSemidirectTransportAt period hPeriod source target
        (globalCandidateAThroatGaugeThirdOrderJetInBaseChartAt period hPeriod
          data sector component source.frameAnchor source.chartAnchor current
            source.frame_mem source.chart_mem) =
      globalCandidateAThroatGaugeThirdOrderJetInBaseChartAt period hPeriod
        data sector component target.frameAnchor target.chartAnchor current
          target.frame_mem target.chart_mem := by
  simpa only [globalCandidateAThroatGaugeThirdOrderJetInBaseChartAt] using
    throatGaugeThirdOrderJetSemidirectTransportAt_extracted period hPeriod
      (globalCandidateAThroatPotentialBySector period hPeriod data sector)
        component source target

end
end P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransportCompatibility4D
end JanusFormal
