import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Absolutely summable coordinates synthesize a vector in a closed operator graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedGraphSeries4D
set_option autoImplicit false
noncomputable section
open scoped Topology

variable {ι H : Type*} [NormedAddCommGroup H] [NormedSpace Real H] [CompleteSpace H]

/-- The graph norm includes both the input and its actual operator image. -/
def graphModeWeight (input output : ι → H) (i : ι) : Real :=
  1 + ‖(input i, output i)‖

omit [NormedSpace Real H] [CompleteSpace H] in
theorem graphModeWeight_pos (input output : ι → H) (i : ι) :
    0 < graphModeWeight input output i := by
  exact add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)

def normalizedGraphMode (input output : ι → H) (i : ι) : H × H :=
  (graphModeWeight input output i)⁻¹ • (input i, output i)

omit [CompleteSpace H] in
theorem normalizedGraphMode_norm_le (input output : ι → H) (i : ι) :
    ‖normalizedGraphMode input output i‖ ≤ 1 := by
  rw [normalizedGraphMode, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (graphModeWeight_pos input output i)), ← div_eq_inv_mul]
  apply (div_le_one (graphModeWeight_pos input output i)).mpr
  change ‖(input i, output i)‖ ≤ 1 + ‖(input i, output i)‖
  exact le_add_of_nonneg_left zero_le_one

theorem graphSeries_summable (input output : ι → H) (coefficients : ι → Real)
    (hCoefficients : Summable (fun i => ‖coefficients i‖)) :
    Summable (fun i => coefficients i • normalizedGraphMode input output i) := by
  apply hCoefficients.of_norm_bounded
  intro i
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (normalizedGraphMode_norm_le input output i)

def graphSeries (input output : ι → H) (coefficients : ι → Real) : H × H :=
  ∑' i, coefficients i • normalizedGraphMode input output i

theorem graphSeries_hasSum (input output : ι → H) (coefficients : ι → Real)
    (hCoefficients : Summable (fun i => ‖coefficients i‖)) :
    HasSum (fun i => coefficients i • normalizedGraphMode input output i)
      (graphSeries input output coefficients) :=
  (graphSeries_summable input output coefficients hCoefficients).hasSum

omit [CompleteSpace H] in
theorem graphSeries_norm_le (input output : ι → H) (coefficients : ι → Real)
    (hCoefficients : Summable (fun i => ‖coefficients i‖)) :
    ‖graphSeries input output coefficients‖ ≤ ∑' i, ‖coefficients i‖ := by
  apply tsum_of_norm_bounded hCoefficients.hasSum
  intro i
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (normalizedGraphMode_norm_le input output i)

theorem graphSeries_mem_graph (operator : H →ₗ.[Real] H) (hClosed : operator.IsClosed)
    (input output : ι → H) (hModes : ∀ i, (input i, output i) ∈ operator.graph)
    (coefficients : ι → Real) (hCoefficients : Summable (fun i => ‖coefficients i‖)) :
    graphSeries input output coefficients ∈ operator.graph := by
  apply hClosed.mem_of_tendsto (graphSeries_hasSum input output coefficients hCoefficients)
  apply Filter.Eventually.of_forall
  intro indices
  exact operator.graph.sum_mem fun i _ => operator.graph.smul_mem _
    (operator.graph.smul_mem _ (hModes i))

theorem graphSeries_mem_domain (operator : H →ₗ.[Real] H) (hClosed : operator.IsClosed)
    (input output : ι → H) (hModes : ∀ i, (input i, output i) ∈ operator.graph)
    (coefficients : ι → Real) (hCoefficients : Summable (fun i => ‖coefficients i‖)) :
    (graphSeries input output coefficients).1 ∈ operator.domain := by
  obtain ⟨state, hInput, _⟩ := (LinearPMap.mem_graph_iff _).mp
    (graphSeries_mem_graph operator hClosed input output hModes coefficients hCoefficients)
  exact hInput ▸ state.property

theorem graphSeries_apply (operator : H →ₗ.[Real] H) (hClosed : operator.IsClosed)
    (input output : ι → H) (hModes : ∀ i, (input i, output i) ∈ operator.graph)
    (coefficients : ι → Real) (hCoefficients : Summable (fun i => ‖coefficients i‖)) :
    operator ⟨(graphSeries input output coefficients).1,
      graphSeries_mem_domain operator hClosed input output hModes coefficients hCoefficients⟩ =
      (graphSeries input output coefficients).2 := by
  obtain ⟨state, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp
    (graphSeries_mem_graph operator hClosed input output hModes coefficients hCoefficients)
  rw [← hOutput]
  apply congrArg operator
  exact Subtype.ext hInput.symm

end
end JanusFormal.P0EFTJanusProgramPT12ClosedGraphSeries4D
