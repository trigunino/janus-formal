import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D

/-!
# Base-chart overlap law for actual throat metric second jets

With the tangent frame fixed, the arbitrary-chart tensor representatives are
related by the genuine extended-chart transition.  Their first and second
Frechet derivatives therefore obey the exact chain rules.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricBaseChartSecondOrderJetOverlap4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorModelNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- With the tensor frame fixed, the first chart representative is locally
the second representative composed with the genuine base-chart transition. -/
theorem throatTensorFrameChartRepresentative_baseChartTransition_eventuallyEq
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    throatTensorFrameChartRepresentative period hPeriod tensor
        frameAnchor firstCenter =ᶠ[
          𝓝 (extChartAt throatCoverModelWithCorners firstCenter current)]
      (throatTensorFrameChartRepresentative period hPeriod tensor
          frameAnchor secondCenter) ∘
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
  simp only [throatTensorFrameChartRepresentative,
    throatGaugeBaseChartTransition, Function.comp_apply]
  rw [(extChartAt throatCoverModelWithCorners secondCenter).left_inv hSecondAt]

private theorem throatTensorFrameChartRepresentative_contDiffAt_two
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real 2
      (throatTensorFrameChartRepresentative period hPeriod tensor
        frameAnchor chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  (throatTensorFrameChartRepresentative_contDiffAt_infty period hPeriod tensor
    frameAnchor chartAnchor current hFrame hChart).of_le (by
      show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)

/-- Exact first-order base-chart chain rule for the metric second-jet carrier. -/
theorem throatTensorSecondOrderJetInFrameChartAt_firstDerivative_transition
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      frameAnchor firstCenter current hFrame hFirst).firstDerivative =
      (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
        frameAnchor secondCenter current hFrame hSecond).firstDerivative.comp
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current)) := by
  let transition :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let firstRepresentative :=
    throatTensorFrameChartRepresentative period hPeriod tensor
      frameAnchor firstCenter
  let secondRepresentative :=
    throatTensorFrameChartRepresentative period hPeriod tensor
      frameAnchor secondCenter
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
      throatTensorFrameChartRepresentative_contDiffAt_two
        period hPeriod tensor frameAnchor secondCenter current hFrame hSecond
  have hTransitionAt : transition firstCoordinate = secondCoordinate := by
    simpa only [transition, firstCoordinate, secondCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hGerm : firstRepresentative =ᶠ[𝓝 firstCoordinate]
      secondRepresentative ∘ transition := by
    simpa only [firstRepresentative, secondRepresentative, transition,
      firstCoordinate] using
      throatTensorFrameChartRepresentative_baseChartTransition_eventuallyEq
        period hPeriod tensor frameAnchor firstCenter secondCenter current
          hFirst hSecond
  rw [throatTensorSecondOrderJetInFrameChartAt_firstDerivative,
    throatTensorSecondOrderJetInFrameChartAt_firstDerivative]
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
theorem throatTensorSecondOrderJetInFrameChartAt_secondDerivative_transition_apply
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : ThroatCoverCoordinates) :
    (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      frameAnchor firstCenter current hFrame hFirst).secondDerivative
        first second =
      (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
        frameAnchor secondCenter current hFrame hSecond).secondDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) first)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) second) +
      (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
        frameAnchor secondCenter current hFrame hSecond).firstDerivative
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter))
            (extChartAt throatCoverModelWithCorners firstCenter current)
              first second) := by
  let transition :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let firstRepresentative :=
    throatTensorFrameChartRepresentative period hPeriod tensor
      frameAnchor firstCenter
  let secondRepresentative :=
    throatTensorFrameChartRepresentative period hPeriod tensor
      frameAnchor secondCenter
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
      throatTensorFrameChartRepresentative_contDiffAt_two
        period hPeriod tensor frameAnchor secondCenter current hFrame hSecond
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
      throatTensorFrameChartRepresentative_baseChartTransition_eventuallyEq
        period hPeriod tensor frameAnchor firstCenter secondCenter current
          hFirst hSecond
  have hSecondDerivative :
      fderiv Real (fderiv Real firstRepresentative) firstCoordinate =
        fderiv Real (fderiv Real (secondRepresentative ∘ transition))
          firstCoordinate :=
    (hGerm.fderiv).fderiv_eq
  rw [throatTensorSecondOrderJetInFrameChartAt_secondDerivative,
    throatTensorSecondOrderJetInFrameChartAt_secondDerivative,
    throatTensorSecondOrderJetInFrameChartAt_firstDerivative]
  rw [show fderiv Real (fderiv Real firstRepresentative) firstCoordinate
      first second =
    fderiv Real (fderiv Real (secondRepresentative ∘ transition))
      firstCoordinate first second by
    exact congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates →L[Real] ThroatCovariantTwoTensorModel ↦
        derivative first second) hSecondDerivative]
  rw [second_fderiv_comp_apply transition secondRepresentative firstCoordinate
    hTransition hSecondRepresentativeAtTransition, hTransitionAt]

end
end P0EFTJanusProgramPActualThroatMetricBaseChartSecondOrderJetOverlap4D
end JanusFormal
