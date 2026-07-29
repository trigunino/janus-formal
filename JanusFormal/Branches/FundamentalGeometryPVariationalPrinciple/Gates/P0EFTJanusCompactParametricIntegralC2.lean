import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Compact parametric integral C² helpers

Shared differentiation-under-the-integral helpers for a finite measure on a
compact space.
-/

namespace JanusFormal
namespace P0EFTJanusCompactParametricIntegralC2

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

theorem hasDerivAt_integral_of_jointContinuous_compact
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopologyEither X Real]
    (measure : Measure X) [IsFiniteMeasure measure]
    (density derivative : Real → X → Real)
    (hDensity : Continuous density.uncurry)
    (hDerivative : Continuous derivative.uncurry)
    (hPointwise : ∀ parameter point,
      HasDerivAt (fun varied => density varied point)
        (derivative parameter point) parameter)
    (parameter : Real) :
    HasDerivAt (fun varied => ∫ point, density varied point ∂measure)
      (∫ point, derivative parameter point ∂measure) parameter := by
  have hCompact : IsCompact
      (Set.Icc (parameter - 1) (parameter + 1) ×ˢ
        (Set.univ : Set X)) :=
    isCompact_Icc.prod isCompact_univ
  let hBounded := hCompact.bddAbove_image hDerivative.norm.continuousOn
  let bound : Real := Classical.choose hBounded
  have hBound := Classical.choose_spec hBounded
  have hDensityMeasurable : ∀ᶠ varied in 𝓝 parameter,
      AEStronglyMeasurable (density varied) measure :=
    Filter.Eventually.of_forall fun varied =>
      (hDensity.comp (continuous_const.prodMk continuous_id))
        |>.aestronglyMeasurable
  have hDensityIntegrable : Integrable (density parameter) measure :=
    (hDensity.comp (continuous_const.prodMk continuous_id))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDerivativeMeasurable :
      AEStronglyMeasurable (derivative parameter) measure :=
    (hDerivative.comp (continuous_const.prodMk continuous_id))
      |>.aestronglyMeasurable
  have hDerivativeBound : ∀ᵐ point ∂measure,
      ∀ varied ∈ Set.Icc (parameter - 1) (parameter + 1),
        ‖derivative varied point‖ ≤ bound := by
    filter_upwards with point
    intro varied hVaried
    exact hBound (Set.mem_image_of_mem _
      (Set.mk_mem_prod hVaried (Set.mem_univ point)))
  have hResult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := density) (F' := derivative) (bound := fun _ : X => bound)
    (Icc_mem_nhds (sub_lt_self parameter zero_lt_one)
      (lt_add_of_pos_right parameter zero_lt_one))
    hDensityMeasurable hDensityIntegrable hDerivativeMeasurable
    hDerivativeBound (integrable_const bound)
    (Filter.Eventually.of_forall fun point varied _ => hPointwise varied point)
  exact hResult.2

theorem integral_contDiff_two_of_jointContinuous_compact
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopologyEither X Real]
    (measure : Measure X) [IsFiniteMeasure measure]
    (density firstDerivative secondDerivative : Real → X → Real)
    (hDensity : Continuous density.uncurry)
    (hFirst : Continuous firstDerivative.uncurry)
    (hSecond : Continuous secondDerivative.uncurry)
    (hDensityDerivative : ∀ parameter point,
      HasDerivAt (fun varied => density varied point)
        (firstDerivative parameter point) parameter)
    (hFirstDerivative : ∀ parameter point,
      HasDerivAt (fun varied => firstDerivative varied point)
        (secondDerivative parameter point) parameter) :
    ContDiff Real 2
      (fun parameter => ∫ point, density parameter point ∂measure) := by
  let action := fun parameter => ∫ point, density parameter point ∂measure
  let first := fun parameter =>
    ∫ point, firstDerivative parameter point ∂measure
  let second := fun parameter =>
    ∫ point, secondDerivative parameter point ∂measure
  have hAction : ∀ parameter, HasDerivAt action (first parameter) parameter :=
    fun parameter =>
      hasDerivAt_integral_of_jointContinuous_compact measure density firstDerivative
        hDensity hFirst hDensityDerivative parameter
  have hFirstAction : ∀ parameter,
      HasDerivAt first (second parameter) parameter :=
    fun parameter =>
      hasDerivAt_integral_of_jointContinuous_compact measure firstDerivative
        secondDerivative hFirst hSecond hFirstDerivative parameter
  have hSecondContinuous : Continuous second := by
    simpa [second] using
      (continuous_parametric_integral_of_continuous hSecond
        (s := (Set.univ : Set X)) isCompact_univ)
  have hFirstC1 : ContDiff Real 1 first := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun parameter => (hFirstAction parameter).differentiableAt, ?_⟩
    have hDeriv : deriv first = second := by
      funext parameter
      exact (hFirstAction parameter).deriv
    rw [hDeriv]
    exact hSecondContinuous
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiff_succ_iff_deriv]
  refine ⟨fun parameter => (hAction parameter).differentiableAt, ?_, ?_⟩
  · norm_num
  · have hDeriv : deriv action = first := by
      funext parameter
      exact (hAction parameter).deriv
    rw [hDeriv]
    exact hFirstC1

end

end P0EFTJanusCompactParametricIntegralC2
end JanusFormal
