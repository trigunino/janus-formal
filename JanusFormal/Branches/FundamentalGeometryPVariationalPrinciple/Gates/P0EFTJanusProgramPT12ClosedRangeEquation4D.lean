import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! A closed partial operator defined by an injective continuous range equation. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedRangeEquation4D
set_option autoImplicit false
noncomputable section
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G]
variable (source : E →L[Real] G) (target : F →L[Real] G)

def rangeEquationGraph : Submodule Real (E × F) :=
  (target.comp (ContinuousLinearMap.snd Real E F) -
    source.comp (ContinuousLinearMap.fst Real E F)).ker

theorem mem_rangeEquationGraph (input : E) (output : F) :
    (input, output) ∈ rangeEquationGraph source target ↔ target output = source input := by
  change target output - source input = 0 ↔ _
  exact sub_eq_zero

variable (hTarget : Function.Injective target)

def closedRangeEquation : E →ₗ.[Real] F := (rangeEquationGraph source target).toLinearPMap

include hTarget in
theorem closedRangeEquation_graph :
    (closedRangeEquation source target).graph = rangeEquationGraph source target := by
  apply Submodule.toLinearPMap_graph_eq
  rintro ⟨input, output⟩ hPair hInput
  change input = 0 at hInput
  apply hTarget
  have h := (mem_rangeEquationGraph source target input output).mp hPair
  simpa only [hInput, map_zero] using h

include hTarget in
theorem closedRangeEquation_graph_iff (input : E) (output : F) :
    (input, output) ∈ (closedRangeEquation source target).graph ↔ target output = source input := by
  rw [closedRangeEquation_graph source target hTarget, mem_rangeEquationGraph]

include hTarget in
theorem closedRangeEquation_isClosed : (closedRangeEquation source target).IsClosed := by
  change IsClosed ((closedRangeEquation source target).graph : Set (E × F))
  rw [closedRangeEquation_graph source target hTarget]
  exact ContinuousLinearMap.isClosed_ker _

include hTarget in
theorem closedRangeEquation_domain_iff (input : E) :
    input ∈ (closedRangeEquation source target).domain ↔ source input ∈ target.range := by
  constructor
  · intro hInput
    exact ⟨_, (closedRangeEquation_graph_iff source target hTarget input _).mp
      ((closedRangeEquation source target).mem_graph ⟨input, hInput⟩)⟩
  · rintro ⟨output, hOutput⟩
    obtain ⟨value, hInput, _⟩ := (LinearPMap.mem_graph_iff _).mp
      ((closedRangeEquation_graph_iff source target hTarget input output).mpr hOutput)
    change (value : E) = input at hInput
    rw [← hInput]
    exact value.property

end
end JanusFormal.P0EFTJanusProgramPT12ClosedRangeEquation4D
