import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartThirdOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransportCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPContinuousLinearMapThirdOrderLeibniz4D

/-!
# Compatibility of SpinC third-jet semidirect transport

The actual third-order semidirect transport sends an extracted smooth SpinC
jet to the extraction in the target trivialization and chart.  The lower jet
is the existing second-order compatibility theorem; only the third derivative
is proved here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransportCompatibility4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1200000

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartThirdOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransportCompatibility4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPContinuousLinearMapThirdOrderLeibniz4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev SpinCEnd :=
  D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber

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

private abbrev SpinCTransitionSecondDerivative :=
  ThroatCoverCoordinates →L[Real] SpinCTransitionFirstDerivative

local instance spinCTransitionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCTransitionSecondDerivativeNormedSpace :
    NormedSpace Real SpinCTransitionSecondDerivative :=
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

/-- Semidirect transport of an extracted smooth SpinC third jet is exactly
the third jet extracted in the target trivialization and chart. -/
theorem throatSpinCThirdOrderJetSemidirectTransportAt_extracted
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (source target :
      ThroatSpinCSecondOrderJetTrivializationChartAt period hPeriod current) :
    throatSpinCThirdOrderJetSemidirectTransportAt period hPeriod choice
        source target
        (d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt
          period hPeriod choice state source.trivializationIndex
            source.chartAnchor current source.trivialization_mem
              source.chart_mem) =
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt
        period hPeriod choice state target.trivializationIndex
          target.chartAnchor current target.trivialization_mem
            target.chart_mem := by
  let sourceRepresentative :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state source.trivializationIndex source.chartAnchor
  let sourceInTargetRepresentative :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state source.trivializationIndex target.chartAnchor
  let targetRepresentative :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state target.trivializationIndex target.chartAnchor
  let sourceJet :=
    d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt
      period hPeriod choice state source.trivializationIndex
        source.chartAnchor current source.trivialization_mem source.chart_mem
  let sourceInTargetJet :=
    d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt
      period hPeriod choice state source.trivializationIndex
        target.chartAnchor current source.trivialization_mem target.chart_mem
  let targetJet :=
    d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt
      period hPeriod choice state target.trivializationIndex
        target.chartAnchor current target.trivialization_mem target.chart_mem
  let baseTransition :=
    throatGaugeBaseChartTransition period hPeriod
      target.chartAnchor source.chartAnchor
  let fiberTransition :=
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
      source.trivializationIndex target.trivializationIndex target.chartAnchor
  let sourceCoordinate :=
    extChartAt throatCoverModelWithCorners source.chartAnchor current
  let targetCoordinate :=
    extChartAt throatCoverModelWithCorners target.chartAnchor current
  let Ainv := fderiv Real baseTransition targetCoordinate
  let Binv := fderiv Real (fderiv Real baseTransition) targetCoordinate
  let Cinv :=
    fderiv Real (fderiv Real (fderiv Real baseTransition)) targetCoordinate
  let D := d9PrimitiveSpinCCoordChange period hPeriod choice
    source.trivializationIndex target.trivializationIndex current
  let E := fderiv Real fiberTransition targetCoordinate
  let F := fderiv Real (fderiv Real fiberTransition) targetCoordinate
  let G :=
    fderiv Real (fderiv Real (fderiv Real fiberTransition)) targetCoordinate
  change throatSpinCThirdOrderJetSemidirectTransportAt period hPeriod choice
    source target sourceJet = targetJet
  have hIndices : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod source.trivializationIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod target.trivializationIndex :=
    ⟨source.trivialization_mem, target.trivialization_mem⟩
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
    (d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_infty
      period hPeriod choice state source.trivializationIndex
        source.chartAnchor current source.trivialization_mem source.chart_mem).of_le
          contDiffThree_le_infty
  have hSourceAtRegularity :
      ContDiffAt Real 3 sourceRepresentative
        (baseTransition targetCoordinate) := by
    simpa only [hBaseAt] using hSourceRegularity
  have hSourceInTargetRegularity :
      ContDiffAt Real 3 sourceInTargetRepresentative targetCoordinate :=
    (d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_infty
      period hPeriod choice state source.trivializationIndex
        target.chartAnchor current source.trivialization_mem target.chart_mem).of_le
          contDiffThree_le_infty
  have hFiberRegularity :
      ContDiffAt Real 3 fiberTransition targetCoordinate :=
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty period hPeriod
      choice source.trivializationIndex target.trivializationIndex
        target.chartAnchor current hIndices target.chart_mem).of_le
          contDiffThree_le_infty
  have hSourceValue : sourceInTargetJet.value = sourceJet.value := by
    simp only [sourceInTargetJet, sourceJet,
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_value]
  have hBaseFirst :
      sourceInTargetJet.firstDerivative =
        sourceJet.firstDerivative.comp Ainv := by
    simpa only [sourceInTargetJet, sourceJet, Ainv, baseTransition,
      targetCoordinate,
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_firstDerivative,
      d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative]
      using
        P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D.d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative_transition
          period hPeriod choice state source.trivializationIndex
            target.chartAnchor source.chartAnchor current
              source.trivialization_mem target.chart_mem source.chart_mem
  have hBaseSecond (first second : ThroatCoverCoordinates) :
      sourceInTargetJet.secondDerivative first second =
        sourceJet.secondDerivative (Ainv first) (Ainv second) +
          sourceJet.firstDerivative (Binv first second) := by
    simpa only [sourceInTargetJet, sourceJet, Ainv, Binv, baseTransition,
      targetCoordinate,
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_firstDerivative,
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_secondDerivative,
      d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative,
      d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative]
      using
        P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D.d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative_transition_apply
          period hPeriod choice state source.trivializationIndex
            target.chartAnchor source.chartAnchor current
              source.trivialization_mem target.chart_mem source.chart_mem
                first second
  have hBaseGerm : sourceInTargetRepresentative =ᶠ[𝓝 targetCoordinate]
      sourceRepresentative ∘ baseTransition := by
    simpa only [sourceInTargetRepresentative, sourceRepresentative,
      baseTransition, targetCoordinate] using
      d9PrimitiveSpinCSectionTrivializationChartRepresentative_baseChartTransition_eventuallyEq
        period hPeriod choice state source.trivializationIndex
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
            ThroatCoverCoordinates →L[Real] D9DoubledMatterFiber =>
        derivative first second third) hThirdDerivativeGerm
    have hFormula := third_fderiv_comp_apply baseTransition
      sourceRepresentative targetCoordinate hBaseRegularity
        hSourceAtRegularity first second third
    rw [hBaseAt] at hFormula
    have hCombined := hApplied.trans hFormula
    simpa only [sourceInTargetJet, sourceJet,
      sourceInTargetRepresentative, sourceRepresentative, Ainv, Binv, Cinv,
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_firstDerivative,
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_secondDerivative,
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_thirdDerivative]
      using hCombined
  have hFiberGerm :
      (fun coordinate => fiberTransition coordinate
        (sourceInTargetRepresentative coordinate)) =ᶠ[𝓝 targetCoordinate]
        targetRepresentative := by
    simpa only [fiberTransition, sourceInTargetRepresentative,
      targetRepresentative, targetCoordinate] using
      d9PrimitiveSpinCSectionTrivializationChartRepresentative_transition_eventuallyEq
        period hPeriod choice state source.trivializationIndex
          target.trivializationIndex target.chartAnchor current hIndices
            target.chart_mem
  have hFiberAt : fiberTransition targetCoordinate = D := by
    simp only [fiberTransition, targetCoordinate, D,
      d9PrimitiveSpinCTransitionCenteredChart,
      hCoordinateInverse]
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
            ThroatCoverCoordinates →L[Real] D9DoubledMatterFiber =>
        derivative first second third) hThirdDerivativeGerm
    have hProduct := third_fderiv_clm_apply_apply fiberTransition
      sourceInTargetRepresentative targetCoordinate first second third
        hFiberRegularity hSourceInTargetRegularity
    have hCombined := hApplied.symm.trans hProduct
    rw [hFiberAt] at hCombined
    simpa only [targetJet, sourceInTargetJet, targetRepresentative,
      sourceInTargetRepresentative, targetCoordinate, E, F, G,
      d9PrimitiveSpinCSectionTrivializationChartRepresentative,
      Function.comp_apply, hCoordinateInverse,
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_value,
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_firstDerivative,
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_secondDerivative,
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_thirdDerivative]
      using hCombined
  apply FramedThirdOrderJet.ext_components
  · simpa only [sourceJet, targetJet,
      throatSpinCThirdOrderJetSemidirectTransportAt_truncate,
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_truncate]
      using throatSpinCSecondOrderJetSemidirectTransportAt_extracted
        period hPeriod choice state source target
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    apply ContinuousLinearMap.ext
    intro third
    have hTransportThird :
        (throatSpinCThirdOrderJetSemidirectTransportAt period hPeriod choice
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

/-- Physical primitive SpinC matter is the canonical specialization of the
generic third-order compatibility theorem. -/
theorem globalGaugeFixedSpinCMatterThirdOrderJetSemidirectTransportAt_extracted
    {current : EffectiveThroat period hPeriod}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (source target :
      ThroatSpinCSecondOrderJetTrivializationChartAt period hPeriod current) :
    throatSpinCThirdOrderJetSemidirectTransportAt period hPeriod
        .positiveQuarter source target
        (globalGaugeFixedSpinCMatterThirdOrderJetInTrivializationChartAt
          period hPeriod configuration sector source.trivializationIndex
            source.chartAnchor current source.trivialization_mem
              source.chart_mem) =
      globalGaugeFixedSpinCMatterThirdOrderJetInTrivializationChartAt
        period hPeriod configuration sector target.trivializationIndex
          target.chartAnchor current target.trivialization_mem
            target.chart_mem :=
  throatSpinCThirdOrderJetSemidirectTransportAt_extracted period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector) source target

end
end P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransportCompatibility4D
end JanusFormal
