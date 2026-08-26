import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D

/-!
# Base-chart overlap law for the actual throat gauge jet

Keeping the tangent frame fixed, this gate separates the base-chart anchor
from the evaluation point and packages the genuine first- and second-order
chain rules into the actual local jet carrier.

This is local chart descent data, not yet a combined chart/frame cocycle or a
global jet-bundle section.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## A point independent of both frame and base-chart anchors -/

/-- The representative in the frame centered at `frameAnchor` is `C²` at a
point read in any extended chart whose source contains that point. -/
theorem throatGaugeCovectorCenteredChart_contDiffAt_two_of_mem_source
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real 2
      (throatGaugeCovectorCenteredChart period hPeriod potential component
        frameAnchor chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  let transition :=
    throatGaugeBaseChartTransition period hPeriod chartAnchor current
  let chartRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      frameAnchor chartAnchor
  let centeredRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      frameAnchor current
  let chartCoordinate :=
    extChartAt throatCoverModelWithCorners chartAnchor current
  have hTransition : ContDiffAt Real 2 transition chartCoordinate := by
    simpa only [transition, chartCoordinate] using
      throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
        chartAnchor current current hChart
        (mem_extChartAt_source current)
  have hCentered : ContDiffAt Real 2 centeredRepresentative
      (extChartAt throatCoverModelWithCorners current current) := by
    simpa only [centeredRepresentative] using
      throatGaugeCovectorCenteredChart_contDiffAt_two period hPeriod potential
        component frameAnchor current hFrame
  have hTransitionAt :
      transition chartCoordinate =
        extChartAt throatCoverModelWithCorners current current := by
    simpa only [transition, chartCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod
        chartAnchor current current hChart
  have hCenteredAt : ContDiffAt Real 2 centeredRepresentative
      (transition chartCoordinate) := by
    simpa only [hTransitionAt] using hCentered
  have hComposition : ContDiffAt Real 2
      (centeredRepresentative ∘ transition) chartCoordinate :=
    hCenteredAt.comp chartCoordinate hTransition
  have hGerm : chartRepresentative =ᶠ[𝓝 chartCoordinate]
      centeredRepresentative ∘ transition := by
    simpa only [chartRepresentative, centeredRepresentative, transition,
      chartCoordinate] using
      throatGaugeCovectorCenteredChart_baseChartTransition_eventuallyEq
        period hPeriod potential component frameAnchor chartAnchor current
          current hChart (mem_extChartAt_source current)
  exact hComposition.congr_of_eventuallyEq hGerm

/-- The value and two Fréchet derivatives in a frame and a base chart whose
anchors are independent of the evaluation point. -/
def throatGaugeCovectorSecondOrderJetInBaseChartAt
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates) :=
  chartwiseSecondOrderJetAt
    (throatGaugeCovectorCenteredChart period hPeriod potential component
      frameAnchor chartAnchor)
    (extChartAt throatCoverModelWithCorners chartAnchor current)
    (throatGaugeCovectorCenteredChart_contDiffAt_two_of_mem_source
      period hPeriod potential component frameAnchor chartAnchor current
        hFrame hChart)

@[simp]
theorem throatGaugeCovectorSecondOrderJetInBaseChartAt_value
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor chartAnchor current hFrame hChart).value =
      throatGaugeCovectorCoordinates period hPeriod potential component
        frameAnchor current := by
  rw [throatGaugeCovectorSecondOrderJetInBaseChartAt,
    chartwiseSecondOrderJetAt_value]
  simp only [throatGaugeCovectorCenteredChart]
  rw [(extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart]

@[simp]
theorem throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor chartAnchor current hFrame hChart).firstDerivative =
      fderiv Real
        (throatGaugeCovectorCenteredChart period hPeriod potential component
          frameAnchor chartAnchor)
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

@[simp]
theorem throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor chartAnchor current hFrame hChart).secondDerivative =
      fderiv Real
        (fderiv Real
          (throatGaugeCovectorCenteredChart period hPeriod potential component
            frameAnchor chartAnchor))
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

/-! ## Diagonal bridge to the two-parameter carrier -/

@[simp]
theorem throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative_diagonal
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor current current hFrame
        (mem_extChartAt_source current)).firstDerivative =
      (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
        component frameAnchor current hFrame).firstDerivative :=
  rfl

@[simp]
theorem throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative_diagonal
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor current current hFrame
        (mem_extChartAt_source current)).secondDerivative =
      (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
        component frameAnchor current hFrame).secondDerivative :=
  rfl

/-! ## Base-chart chain rules in the jet carrier -/

/-- The first-derivative fields in two base charts obey the exact chain rule,
with the tangent frame held fixed. -/
theorem throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative_transition
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor firstCenter current hFrame hFirst).firstDerivative =
      (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
        component frameAnchor secondCenter current hFrame hSecond).firstDerivative.comp
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current)) := by
  let transition :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let firstRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      frameAnchor firstCenter
  let secondRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
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
      throatGaugeCovectorCenteredChart_contDiffAt_two_of_mem_source
        period hPeriod potential component frameAnchor secondCenter current
          hFrame hSecond
  have hTransitionAt : transition firstCoordinate = secondCoordinate := by
    simpa only [transition, firstCoordinate, secondCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hGerm : firstRepresentative =ᶠ[𝓝 firstCoordinate]
      secondRepresentative ∘ transition := by
    simpa only [firstRepresentative, secondRepresentative, transition,
      firstCoordinate] using
      throatGaugeCovectorCenteredChart_baseChartTransition_eventuallyEq
        period hPeriod potential component frameAnchor firstCenter secondCenter
          current hFirst hSecond
  rw [throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative,
    throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative]
  calc
    fderiv Real firstRepresentative firstCoordinate =
        fderiv Real (secondRepresentative ∘ transition) firstCoordinate :=
      hGerm.fderiv_eq
    _ = (fderiv Real secondRepresentative secondCoordinate).comp
        (fderiv Real transition firstCoordinate) := by
      rw [fderiv_comp firstCoordinate
        (by simpa only [hTransitionAt] using
          hSecondRepresentative.differentiableAt (by norm_num))
        (hTransition.differentiableAt (by norm_num)), hTransitionAt]

/-- Pointwise second-order chain rule for composition. -/
theorem second_fderiv_comp_apply
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (inner : E → F) (outer : F → G) (point : E)
    (hInner : ContDiffAt Real 2 inner point)
    (hOuter : ContDiffAt Real 2 outer (inner point))
    (first second : E) :
    fderiv Real (fderiv Real (outer ∘ inner)) point first second =
      fderiv Real (fderiv Real outer) (inner point)
          (fderiv Real inner point first)
          (fderiv Real inner point second) +
        fderiv Real outer (inner point)
          (fderiv Real (fderiv Real inner) point first second) := by
  have hInnerDiff : DifferentiableAt Real inner point :=
    hInner.differentiableAt (by norm_num)
  have hInnerNear := hInner.eventually (by norm_num)
  have hOuterNearAt := hOuter.eventually (by norm_num)
  have hOuterNear := hInner.continuousAt.eventually hOuterNearAt
  have hFirstDerivative :
      (fderiv Real (outer ∘ inner)) =ᶠ[𝓝 point]
        (fun current =>
          (fderiv Real outer (inner current)).comp
            (fderiv Real inner current)) := by
    filter_upwards [hInnerNear, hOuterNear] with current hCurrentInner
      hCurrentOuter
    exact fderiv_comp current
      (hCurrentOuter.differentiableAt (by norm_num))
      (hCurrentInner.differentiableAt (by norm_num))
  have hSecondDerivative :
      fderiv Real (fderiv Real (outer ∘ inner)) point =
        fderiv Real
          (fun current =>
            (fderiv Real outer (inner current)).comp
              (fderiv Real inner current)) point :=
    hFirstDerivative.fderiv_eq
  rw [hSecondDerivative]
  have hOuterDerivative :
      ContDiffAt Real 1 (fderiv Real outer) (inner point) :=
    hOuter.fderiv_right (m := 1) (by norm_num)
  have hInnerDerivative :
      ContDiffAt Real 1 (fderiv Real inner) point :=
    hInner.fderiv_right (m := 1) (by norm_num)
  have hComposedOuterDerivative :
      DifferentiableAt Real
        (fun current => fderiv Real outer (inner current)) point :=
    (hOuterDerivative.differentiableAt (by norm_num)).comp point hInnerDiff
  have hInnerDerivativeDiff :
      DifferentiableAt Real (fderiv Real inner) point :=
    hInnerDerivative.differentiableAt (by norm_num)
  rw [fderiv_clm_comp hComposedOuterDerivative hInnerDerivativeDiff]
  have hComposedOuterFDeriv :
      fderiv Real (fun current => fderiv Real outer (inner current)) point =
        (fderiv Real (fderiv Real outer) (inner point)).comp
          (fderiv Real inner point) :=
    fderiv_comp point
      (hOuterDerivative.differentiableAt (by norm_num)) hInnerDiff
  rw [hComposedOuterFDeriv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  abel

/-- The second-derivative fields in two base charts obey the exact second-order
chain rule, including the non-tensorial Hessian of the chart transition. -/
theorem throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative_transition_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
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
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor firstCenter current hFrame hFirst).secondDerivative
        first second =
      (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
        component frameAnchor secondCenter current hFrame hSecond).secondDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) first)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) second) +
      (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
        component frameAnchor secondCenter current hFrame hSecond).firstDerivative
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter))
            (extChartAt throatCoverModelWithCorners firstCenter current)
              first second) := by
  let transition :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let firstRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      frameAnchor firstCenter
  let secondRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
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
      throatGaugeCovectorCenteredChart_contDiffAt_two_of_mem_source
        period hPeriod potential component frameAnchor secondCenter current
          hFrame hSecond
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
      throatGaugeCovectorCenteredChart_baseChartTransition_eventuallyEq
        period hPeriod potential component frameAnchor firstCenter secondCenter
          current hFirst hSecond
  have hSecondDerivative :
      fderiv Real (fderiv Real firstRepresentative) firstCoordinate =
        fderiv Real (fderiv Real (secondRepresentative ∘ transition))
          firstCoordinate :=
    (hGerm.fderiv).fderiv_eq
  rw [throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative,
    throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative,
    throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative]
  rw [show fderiv Real (fderiv Real firstRepresentative) firstCoordinate
      first second =
    fderiv Real (fderiv Real (secondRepresentative ∘ transition))
      firstCoordinate first second by
    exact congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates →L[Real]
            FramedCovector ThroatCoverCoordinates =>
        derivative first second) hSecondDerivative]
  rw [second_fderiv_comp_apply transition secondRepresentative firstCoordinate
    hTransition hSecondRepresentativeAtTransition, hTransitionAt]

end
end P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
end JanusFormal
