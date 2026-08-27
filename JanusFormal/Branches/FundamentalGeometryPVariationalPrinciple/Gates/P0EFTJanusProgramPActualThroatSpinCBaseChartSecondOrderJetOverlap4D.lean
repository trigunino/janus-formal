import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D

/-!
# Base-chart overlap law for actual throat SpinC second jets

With the SpinC trivialization fixed, arbitrary-chart representatives are
related by the genuine extended-chart transition.  Their first and second
Frechet derivatives therefore obey the exact chain rules.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- With the SpinC trivialization fixed, the first chart representative is
locally the second representative composed with the base-chart transition. -/
theorem d9PrimitiveSpinCSectionTrivializationChartRepresentative_baseChartTransition_eventuallyEq
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : ThroatBase period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
        choice state index firstCenter =ᶠ[
          𝓝 (extChartAt throatCoverModelWithCorners firstCenter current)]
      (d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
          choice state index secondCenter) ∘
        throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter := by
  have hFirstTarget :
      extChartAt throatCoverModelWithCorners firstCenter current ∈
        (extChartAt throatCoverModelWithCorners firstCenter).target :=
    (extChartAt throatCoverModelWithCorners firstCenter).map_source hFirst
  have hInverseContinuous :
      ContinuousAt
        (extChartAt throatCoverModelWithCorners firstCenter).symm
        (extChartAt throatCoverModelWithCorners firstCenter current) :=
    continuousAt_extChartAt_symm'' hFirstTarget
  have hSecondPreimage :
      (extChartAt throatCoverModelWithCorners firstCenter).symm ⁻¹'
          (extChartAt throatCoverModelWithCorners secondCenter).source ∈
        𝓝 (extChartAt throatCoverModelWithCorners firstCenter current) :=
    hInverseContinuous.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst]
      exact extChartAt_source_mem_nhds' hSecond)
  filter_upwards [hSecondPreimage] with coordinate hCoordinate
  have hSecondAt :
      (extChartAt throatCoverModelWithCorners firstCenter).symm coordinate ∈
        (extChartAt throatCoverModelWithCorners secondCenter).source :=
    hCoordinate
  simp only [d9PrimitiveSpinCSectionTrivializationChartRepresentative,
    throatGaugeBaseChartTransition, Function.comp_apply]
  rw [(extChartAt throatCoverModelWithCorners secondCenter).left_inv hSecondAt]

private theorem
    d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_two
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real 2
      (d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
        choice state index chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  (d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_infty
    period hPeriod choice state index chartAnchor current hTrivialization
      hChart).of_le (by
        show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)

@[simp]
theorem d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_value_transition
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period hPeriod
      choice state index firstCenter current hTrivialization hFirst).value =
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period hPeriod
      choice state index secondCenter current hTrivialization hSecond).value := by
  simp

/-- Exact first-order base-chart chain rule for a SpinC second jet. -/
theorem d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative_transition
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period hPeriod
      choice state index firstCenter current hTrivialization hFirst).firstDerivative =
      (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period hPeriod
        choice state index secondCenter current hTrivialization hSecond).firstDerivative.comp
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter)
              (extChartAt throatCoverModelWithCorners firstCenter current)) := by
  let transition :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let firstRepresentative :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state index firstCenter
  let secondRepresentative :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state index secondCenter
  let firstCoordinate :=
    extChartAt throatCoverModelWithCorners firstCenter current
  let secondCoordinate :=
    extChartAt throatCoverModelWithCorners secondCenter current
  have hTransition : ContDiffAt Real 2 transition firstCoordinate := by
    simpa only [transition, firstCoordinate] using
      throatGaugeBaseChartTransition_contDiffAt_two period hPeriod firstCenter
        secondCenter current hFirst hSecond
  have hSecondRepresentative : ContDiffAt Real 2 secondRepresentative
      secondCoordinate := by
    simpa only [secondRepresentative, secondCoordinate] using
      d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_two
        period hPeriod choice state index secondCenter current hTrivialization
          hSecond
  have hTransitionAt : transition firstCoordinate = secondCoordinate := by
    simpa only [transition, firstCoordinate, secondCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hGerm : firstRepresentative =ᶠ[𝓝 firstCoordinate]
      secondRepresentative ∘ transition := by
    simpa only [firstRepresentative, secondRepresentative, transition,
      firstCoordinate] using
      d9PrimitiveSpinCSectionTrivializationChartRepresentative_baseChartTransition_eventuallyEq
        period hPeriod choice state index firstCenter secondCenter current
          hFirst hSecond
  rw [d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative,
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative]
  calc
    fderiv Real firstRepresentative firstCoordinate =
        fderiv Real (secondRepresentative ∘ transition) firstCoordinate :=
      hGerm.fderiv_eq
    _ = (fderiv Real secondRepresentative secondCoordinate).comp
        (fderiv Real transition firstCoordinate) := by
      have hChain := fderiv_comp firstCoordinate
        (by simpa only [hTransitionAt] using
          hSecondRepresentative.differentiableAt (by norm_num))
        (hTransition.differentiableAt (by norm_num))
      simpa only [hTransitionAt] using hChain

/-- Exact second-order base-chart chain rule, including the Hessian of the
chart transition. -/
theorem d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative_transition_apply
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : ThroatCoverCoordinates) :
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period hPeriod
      choice state index firstCenter current hTrivialization hFirst).secondDerivative
        first second =
      (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period hPeriod
        choice state index secondCenter current hTrivialization hSecond).secondDerivative
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter)
              (extChartAt throatCoverModelWithCorners firstCenter current) first)
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter)
              (extChartAt throatCoverModelWithCorners firstCenter current) second) +
      (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period hPeriod
        choice state index secondCenter current hTrivialization hSecond).firstDerivative
            (fderiv Real
              (fderiv Real
                (throatGaugeBaseChartTransition period hPeriod
                  firstCenter secondCenter))
              (extChartAt throatCoverModelWithCorners firstCenter current)
                first second) := by
  let transition :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let firstRepresentative :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state index firstCenter
  let secondRepresentative :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state index secondCenter
  let firstCoordinate :=
    extChartAt throatCoverModelWithCorners firstCenter current
  let secondCoordinate :=
    extChartAt throatCoverModelWithCorners secondCenter current
  have hTransition : ContDiffAt Real 2 transition firstCoordinate := by
    simpa only [transition, firstCoordinate] using
      throatGaugeBaseChartTransition_contDiffAt_two period hPeriod firstCenter
        secondCenter current hFirst hSecond
  have hSecondRepresentative : ContDiffAt Real 2 secondRepresentative
      secondCoordinate := by
    simpa only [secondRepresentative, secondCoordinate] using
      d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_two
        period hPeriod choice state index secondCenter current hTrivialization
          hSecond
  have hTransitionAt : transition firstCoordinate = secondCoordinate := by
    simpa only [transition, firstCoordinate, secondCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hSecondRepresentativeAtTransition :
      ContDiffAt Real 2 secondRepresentative (transition firstCoordinate) := by
    simpa only [hTransitionAt] using hSecondRepresentative
  have hGerm : firstRepresentative =ᶠ[𝓝 firstCoordinate]
      secondRepresentative ∘ transition := by
    simpa only [firstRepresentative, secondRepresentative, transition,
      firstCoordinate] using
      d9PrimitiveSpinCSectionTrivializationChartRepresentative_baseChartTransition_eventuallyEq
        period hPeriod choice state index firstCenter secondCenter current
          hFirst hSecond
  have hSecondDerivative :
      fderiv Real (fderiv Real firstRepresentative) firstCoordinate =
        fderiv Real (fderiv Real (secondRepresentative ∘ transition))
          firstCoordinate :=
    (hGerm.fderiv).fderiv_eq
  rw [d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative,
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative,
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative]
  rw [show fderiv Real (fderiv Real firstRepresentative) firstCoordinate
      first second =
    fderiv Real (fderiv Real (secondRepresentative ∘ transition))
      firstCoordinate first second by
    exact congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates →L[Real] D9DoubledMatterFiber ↦
        derivative first second) hSecondDerivative]
  rw [second_fderiv_comp_apply transition secondRepresentative firstCoordinate
    hTransition hSecondRepresentativeAtTransition, hTransitionAt]

end
end P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D
end JanusFormal
