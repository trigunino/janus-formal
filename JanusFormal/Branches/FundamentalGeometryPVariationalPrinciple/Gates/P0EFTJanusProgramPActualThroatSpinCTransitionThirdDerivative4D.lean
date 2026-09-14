import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetTransitionSmoothRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCZeroOrderTransitionGroupoid4D

/-!
# Third derivative of the actual throat SpinC transition

The centered primitive SpinC transition is smooth at every valid
trivialization/chart pair.  This gate exposes its genuine third Frechet
derivative in the target base chart and proves the two adjacent symmetries of
that coefficient.

This is only the third-order fiber-transition coefficient.  No third-jet
transport, cocycle, physical atlas, or current descent is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCTransitionThirdDerivative4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatSpinCZeroOrderTransitionGroupoid4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetTransitionSmoothRegularity4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCTrivializationChartAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatSpinCSecondOrderJetTrivializationChartAt period hPeriod current

private abbrev SpinCEnd :=
  D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber

local instance spinCEndNormedAddCommGroup :
    NormedAddCommGroup SpinCEnd :=
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

private theorem fderiv_continuousLinearMap_apply_const
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (maps : E → F →L[Real] G) (point direction : E) (vector : F)
    (hMaps : DifferentiableAt Real maps point) :
    fderiv Real (fun current => maps current vector) point direction =
      fderiv Real maps point direction vector := by
  let evaluation : (F →L[Real] G) →L[Real] G :=
    ContinuousLinearMap.apply Real G vector
  have hDerivative :
      fderiv Real (evaluation ∘ maps) point =
        evaluation.comp (fderiv Real maps point) :=
    (evaluation.hasFDerivAt.comp point hMaps.hasFDerivAt).fderiv
  have hFunction :
      evaluation ∘ maps = fun current => maps current vector := by
    funext current
    rfl
  rw [hFunction] at hDerivative
  have hApply := congrArg
    (fun derivative : E →L[Real] G => derivative direction) hDerivative
  simpa only [evaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using hApply

private theorem thirdFDeriv_swap_second_third
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (function : E → F) (point first second third : E)
    (hFunction : ContDiffAt Real 3 function point) :
    fderiv Real (fderiv Real (fderiv Real function)) point first second third =
      fderiv Real (fderiv Real (fderiv Real function)) point first third second := by
  have hHessian :
      DifferentiableAt Real (fderiv Real (fderiv Real function)) point :=
    ((hFunction.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hHessianAtSecond :
      DifferentiableAt Real
        (fun nearby => fderiv Real (fderiv Real function) nearby second) point :=
    hHessian.clm_apply (differentiableAt_const (c := second))
  have hHessianAtThird :
      DifferentiableAt Real
        (fun nearby => fderiv Real (fderiv Real function) nearby third) point :=
    hHessian.clm_apply (differentiableAt_const (c := third))
  have hNearbySymmetry :
      Filter.EventuallyEq (𝓝 point)
        (fun nearby => fderiv Real (fderiv Real function) nearby second third)
        (fun nearby => fderiv Real (fderiv Real function) nearby third second) := by
    filter_upwards [hFunction.eventually (by norm_num)] with nearby hNearby
    exact (hNearby.isSymmSndFDerivAt (𝕜 := Real) (by norm_num)).eq second third
  have hDerivativeEquality := hNearbySymmetry.fderiv_eq (𝕜 := Real)
  have hApplied := congrArg
    (fun derivative : E →L[Real] F => derivative first) hDerivativeEquality
  have hOuterSecond :
      fderiv Real
          (fun nearby => fderiv Real (fderiv Real function) nearby second)
          point first =
        fderiv Real (fderiv Real (fderiv Real function)) point first second :=
    fderiv_continuousLinearMap_apply_const _ point first second hHessian
  have hOuterThird :
      fderiv Real
          (fun nearby => fderiv Real (fderiv Real function) nearby third)
          point first =
        fderiv Real (fderiv Real (fderiv Real function)) point first third :=
    fderiv_continuousLinearMap_apply_const _ point first third hHessian
  have hSecondThird :
      fderiv Real
          (fun nearby => fderiv Real (fderiv Real function) nearby second third)
          point first =
        fderiv Real (fderiv Real (fderiv Real function))
          point first second third := by
    calc
      _ = fderiv Real
          (fun nearby => fderiv Real (fderiv Real function) nearby second)
          point first third :=
        fderiv_continuousLinearMap_apply_const _ point first third
          hHessianAtSecond
      _ = _ := congrArg (fun derivative : E →L[Real] F => derivative third)
        hOuterSecond
  have hThirdSecond :
      fderiv Real
          (fun nearby => fderiv Real (fderiv Real function) nearby third second)
          point first =
        fderiv Real (fderiv Real (fderiv Real function))
          point first third second := by
    calc
      _ = fderiv Real
          (fun nearby => fderiv Real (fderiv Real function) nearby third)
          point first second :=
        fderiv_continuousLinearMap_apply_const _ point first second
          hHessianAtThird
      _ = _ := congrArg (fun derivative : E →L[Real] F => derivative second)
        hOuterThird
  rw [hSecondThird, hThirdSecond] at hApplied
  exact hApplied

private theorem transition_self_eventuallyEq
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (presentation : SpinCTrivializationChartAt period hPeriod current) :
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        presentation.trivializationIndex presentation.trivializationIndex
          presentation.chartAnchor =ᶠ[
            𝓝 (extChartAt throatCoverModelWithCorners
              presentation.chartAnchor current)]
      fun _ ↦ ContinuousLinearMap.id Real D9DoubledMatterFiber := by
  have hBaseNhds :
      d9PrimitiveSpinCBaseSet period hPeriod
          presentation.trivializationIndex ∈ 𝓝 current :=
    (d9PrimitiveSpinCBaseSet_isOpen period hPeriod
      presentation.trivializationIndex).mem_nhds presentation.trivialization_mem
  have hTarget :=
    (extChartAt throatCoverModelWithCorners presentation.chartAnchor).map_source
      presentation.chart_mem
  have hInverseContinuous := continuousAt_extChartAt_symm'' hTarget
  have hPreimage :
      (extChartAt throatCoverModelWithCorners presentation.chartAnchor).symm ⁻¹'
          d9PrimitiveSpinCBaseSet period hPeriod
            presentation.trivializationIndex ∈
        𝓝 (extChartAt throatCoverModelWithCorners
          presentation.chartAnchor current) :=
    hInverseContinuous.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners
        presentation.chartAnchor).left_inv presentation.chart_mem]
      exact hBaseNhds)
  filter_upwards [hPreimage] with coordinate hCoordinate
  exact d9PrimitiveSpinCCoordChange_self period hPeriod choice
    presentation.trivializationIndex
      ((extChartAt throatCoverModelWithCorners
        presentation.chartAnchor).symm coordinate) hCoordinate

/-- Genuine third derivative of the forward SpinC transition, expressed in
the target base chart. -/
def throatSpinCTargetTrivializationTransitionThirdDerivativeAt
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] SpinCEnd :=
  fderiv Real
    (fderiv Real
      (fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          source.trivializationIndex target.trivializationIndex
            target.chartAnchor)))
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)

/-- The first two directions of the third SpinC transition coefficient
commute. -/
theorem throatSpinCTargetTrivializationTransitionThirdDerivativeAt_swap_first_second
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    throatSpinCTargetTrivializationTransitionThirdDerivativeAt period hPeriod
        choice source target first second third =
      throatSpinCTargetTrivializationTransitionThirdDerivativeAt period hPeriod
        choice source target second first third := by
  have hFirstDerivative :
      ContDiffAt Real 2
        (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            source.trivializationIndex target.trivializationIndex
              target.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) :=
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod choice source.trivializationIndex
        target.trivializationIndex target.chartAnchor current
        ⟨source.trivialization_mem, target.trivialization_mem⟩
          target.chart_mem).fderiv_right (m := 2) (by
            change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
            exact WithTop.coe_le_coe.mpr le_top)
  have hSymmetric :=
    (hFirstDerivative.isSymmSndFDerivAt (by norm_num)).eq first second
  exact congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real] SpinCEnd =>
      derivative third) hSymmetric

/-- The last two directions of the third SpinC transition coefficient
commute. -/
theorem throatSpinCTargetTrivializationTransitionThirdDerivativeAt_swap_second_third
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    throatSpinCTargetTrivializationTransitionThirdDerivativeAt period hPeriod
        choice source target first second third =
      throatSpinCTargetTrivializationTransitionThirdDerivativeAt period hPeriod
        choice source target first third second := by
  let transition :=
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
      source.trivializationIndex target.trivializationIndex target.chartAnchor
  let coordinate :=
    extChartAt throatCoverModelWithCorners target.chartAnchor current
  have hTransitionC3 : ContDiffAt Real 3 transition coordinate :=
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod choice source.trivializationIndex
        target.trivializationIndex target.chartAnchor current
        ⟨source.trivialization_mem, target.trivialization_mem⟩
          target.chart_mem).of_le (by
            change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
            exact WithTop.coe_le_coe.mpr le_top)
  simpa only [throatSpinCTargetTrivializationTransitionThirdDerivativeAt,
    transition, coordinate] using
      thirdFDeriv_swap_second_third transition coordinate first second third
        hTransitionC3

/-- The genuine third derivative of a repeated SpinC transition vanishes. -/
@[simp]
theorem throatSpinCTargetTrivializationTransitionThirdDerivativeAt_self
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (presentation : SpinCTrivializationChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    throatSpinCTargetTrivializationTransitionThirdDerivativeAt period hPeriod
        choice presentation presentation first second third = 0 := by
  let transition :=
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
      presentation.trivializationIndex presentation.trivializationIndex
        presentation.chartAnchor
  let coordinate :=
    extChartAt throatCoverModelWithCorners presentation.chartAnchor current
  have hGerm : transition =ᶠ[𝓝 coordinate]
      fun _ ↦ ContinuousLinearMap.id Real D9DoubledMatterFiber := by
    simpa only [transition, coordinate] using
      transition_self_eventuallyEq period hPeriod choice presentation
  have hFirstDerivative :
      fderiv Real transition =ᶠ[𝓝 coordinate]
        fun _ => (0 : SpinCTransitionFirstDerivative) := by
    filter_upwards [hGerm.fderiv (𝕜 := Real)] with nearby hNearby
    simpa using hNearby
  have hSecondDerivative :
      fderiv Real (fderiv Real transition) =ᶠ[𝓝 coordinate]
        fun _ => (0 : SpinCTransitionSecondDerivative) := by
    filter_upwards [hFirstDerivative.fderiv (𝕜 := Real)]
      with nearby hNearby
    simpa using hNearby
  have hThirdDerivative :
      fderiv Real (fderiv Real (fderiv Real transition)) coordinate = 0 :=
    (hSecondDerivative.fderiv_eq (𝕜 := Real)).trans
      (hasFDerivAt_const (𝕜 := Real) (x := coordinate)
        (c := (0 : SpinCTransitionSecondDerivative))).fderiv
  simp only [throatSpinCTargetTrivializationTransitionThirdDerivativeAt]
  rw [hThirdDerivative]
  simp

end
end P0EFTJanusProgramPActualThroatSpinCTransitionThirdDerivative4D
end JanusFormal
