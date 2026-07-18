import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace JanusFormal
namespace P0EFTJanusInvariantMeasureFlowIPP4D

set_option autoImplicit false

open MeasureTheory Set

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X]

theorem integral_derivative_eq_zero_of_invariant
    (mu : Measure X) [IsFiniteMeasure mu]
    (F F' : Real → X → Real)
    (hF : Continuous (fun input : Real × X ↦ F input.1 input.2))
    (hF' : Continuous (fun input : Real × X ↦ F' input.1 input.2))
    (hDerivative : ∀ parameter point,
      HasDerivAt (fun t ↦ F t point) (F' parameter point) parameter)
    (hInvariant : ∀ parameter,
      (∫ point, F parameter point ∂mu) = ∫ point, F 0 point ∂mu) :
    (∫ point, F' 0 point ∂mu) = 0 := by
  have hCompact : IsCompact
      (Set.Icc (-1 : Real) 1 ×ˢ (Set.univ : Set X)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨bound, hBound⟩ := hCompact.bddAbove_image hF'.norm.continuousOn
  have hSection (parameter : Real) : Continuous (F parameter) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hSection' (parameter : Real) : Continuous (F' parameter) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  have hMeasurable : ∀ᶠ parameter in nhds (0 : Real),
      AEStronglyMeasurable (F parameter) mu := by
    filter_upwards with parameter
    exact (hSection parameter).aestronglyMeasurable
  have hIntegrable : Integrable (F 0) mu :=
    (hSection 0).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDerivativeMeasurable : AEStronglyMeasurable (F' 0) mu :=
    (hSection' 0).aestronglyMeasurable
  have hDominated : ∀ᵐ point ∂mu, ∀ parameter ∈ Set.Icc (-1 : Real) 1,
      ‖F' parameter point‖ ≤ bound := by
    filter_upwards with point
    intro parameter hParameter
    exact hBound (Set.mem_image_of_mem _
      (Set.mk_mem_prod hParameter (Set.mem_univ point)))
  have hDifferentiate :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Icc_mem_nhds (by norm_num : (-1 : Real) < 0) (by norm_num : (0 : Real) < 1))
      hMeasurable hIntegrable hDerivativeMeasurable hDominated
      (integrable_const bound)
      (by
        filter_upwards with point
        intro parameter _
        exact hDerivative parameter point)).2
  have hIntegralFunction :
      (fun parameter ↦ ∫ point, F parameter point ∂mu) =
        fun _ ↦ ∫ point, F 0 point ∂mu :=
    funext hInvariant
  have hZeroDerivative : HasDerivAt
      (fun parameter ↦ ∫ point, F parameter point ∂mu) 0 0 := by
    rw [hIntegralFunction]
    exact hasDerivAt_const 0 _
  exact hDifferentiate.unique hZeroDerivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]

theorem integral_inner_derivative_eq_neg
    (mu : Measure X) [IsFiniteMeasure mu]
    (flow : Real → X → X)
    (hFlow : Continuous (fun input : Real × X ↦ flow input.1 input.2))
    (hFlowZero : ∀ point, flow 0 point = point)
    (hFlowEmbedding : ∀ parameter,
      MeasurableEmbedding (flow parameter))
    (hMeasurePreserving : ∀ parameter,
      MeasurePreserving (flow parameter) mu mu)
    (first second firstDerivative secondDerivative : X → E)
    (hFirst : Continuous first) (hSecond : Continuous second)
    (hFirstDerivative : Continuous firstDerivative)
    (hSecondDerivative : Continuous secondDerivative)
    (hFirstCurve : ∀ parameter point,
      HasDerivAt (fun t ↦ first (flow t point))
        (firstDerivative (flow parameter point)) parameter)
    (hSecondCurve : ∀ parameter point,
      HasDerivAt (fun t ↦ second (flow t point))
        (secondDerivative (flow parameter point)) parameter) :
    (∫ point, inner Real (first point) (secondDerivative point) ∂mu) =
      -∫ point, inner Real (firstDerivative point) (second point) ∂mu := by
  let F : Real → X → Real := fun parameter point ↦
    inner Real (first (flow parameter point)) (second (flow parameter point))
  let F' : Real → X → Real := fun parameter point ↦
    inner Real (first (flow parameter point))
        (secondDerivative (flow parameter point)) +
      inner Real (firstDerivative (flow parameter point))
        (second (flow parameter point))
  have hF : Continuous (fun input : Real × X ↦ F input.1 input.2) := by
    exact (hFirst.comp hFlow).inner (hSecond.comp hFlow)
  have hF' : Continuous (fun input : Real × X ↦ F' input.1 input.2) := by
    exact ((hFirst.comp hFlow).inner (hSecondDerivative.comp hFlow)).add
      ((hFirstDerivative.comp hFlow).inner (hSecond.comp hFlow))
  have hCurve : ∀ parameter point,
      HasDerivAt (fun t ↦ F t point) (F' parameter point) parameter := by
    intro parameter point
    simpa [F, F'] using
      (hFirstCurve parameter point).inner Real (hSecondCurve parameter point)
  have hInvariant : ∀ parameter,
      (∫ point, F parameter point ∂mu) = ∫ point, F 0 point ∂mu := by
    intro parameter
    calc
      (∫ point, F parameter point ∂mu) =
          ∫ point, inner Real (first point) (second point) ∂mu := by
            simpa [F] using
              (hMeasurePreserving parameter).integral_comp
                (hFlowEmbedding parameter)
                (fun point ↦ inner Real (first point) (second point))
      _ = ∫ point, F 0 point ∂mu := by simp [F, hFlowZero]
  have hSumZero := integral_derivative_eq_zero_of_invariant mu F F'
    hF hF' hCurve hInvariant
  have hFirstTerm : Integrable
      (fun point ↦ inner Real (first point) (secondDerivative point)) mu :=
    (hFirst.inner hSecondDerivative).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSecondTerm : Integrable
      (fun point ↦ inner Real (firstDerivative point) (second point)) mu :=
    (hFirstDerivative.inner hSecond).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [F', hFlowZero] at hSumZero
  rw [integral_add hFirstTerm hSecondTerm] at hSumZero
  linarith

end P0EFTJanusInvariantMeasureFlowIPP4D
end JanusFormal
