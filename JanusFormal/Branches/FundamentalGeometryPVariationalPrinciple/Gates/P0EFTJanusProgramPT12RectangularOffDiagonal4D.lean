import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-! An off-diagonal closed operator between two different real Hilbert spaces. -/
namespace JanusFormal.P0EFTJanusProgramPT12RectangularOffDiagonal4D
set_option autoImplicit false
noncomputable section
open Set Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [NormedAddCommGroup F] [InnerProductSpace Real F]
variable (first : F →ₗ.[Real] E) (second : E →ₗ.[Real] F)

def rectangularOffDiagonalGraph : Submodule Real (WithLp 2 (E × F) × WithLp 2 (E × F)) where
  carrier := {pair | (pair.1.snd, pair.2.fst) ∈ first.graph ∧
    (pair.1.fst, pair.2.snd) ∈ second.graph}
  zero_mem' := ⟨first.graph.zero_mem, second.graph.zero_mem⟩
  add_mem' hx hy := ⟨first.graph.add_mem hx.1 hy.1, second.graph.add_mem hx.2 hy.2⟩
  smul_mem' scalar _ hx := ⟨first.graph.smul_mem scalar hx.1, second.graph.smul_mem scalar hx.2⟩

def rectangularOffDiagonalOperator : WithLp 2 (E × F) →ₗ.[Real] WithLp 2 (E × F) :=
  (rectangularOffDiagonalGraph first second).toLinearPMap

theorem rectangularOffDiagonalOperator_graph :
    (rectangularOffDiagonalOperator first second).graph = rectangularOffDiagonalGraph first second := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  apply WithLp.ofLp_injective 2
  exact Prod.ext
    (first.graph_fst_eq_zero_snd hPair.1 (congrArg WithLp.snd hZero))
    (second.graph_fst_eq_zero_snd hPair.2 (congrArg WithLp.fst hZero))

theorem rectangularOffDiagonalOperator_mem_graph_iff (input output : WithLp 2 (E × F)) :
    (input, output) ∈ (rectangularOffDiagonalOperator first second).graph ↔
      (input.snd, output.fst) ∈ first.graph ∧ (input.fst, output.snd) ∈ second.graph := by
  rw [rectangularOffDiagonalOperator_graph]
  rfl

theorem rectangularOffDiagonalOperator_domain_iff (input : WithLp 2 (E × F)) :
    input ∈ (rectangularOffDiagonalOperator first second).domain ↔
      input.fst ∈ second.domain ∧ input.snd ∈ first.domain := by
  constructor
  · intro hInput
    have h := (rectangularOffDiagonalOperator_mem_graph_iff first second _ _).mp
      ((rectangularOffDiagonalOperator first second).mem_graph ⟨input, hInput⟩)
    obtain ⟨x, hx, _⟩ := (first.mem_graph_iff).mp h.1
    obtain ⟨y, hy, _⟩ := (second.mem_graph_iff).mp h.2
    change (x : F) = input.snd at hx
    change (y : E) = input.fst at hy
    constructor
    · rw [← hy]; exact y.property
    · rw [← hx]; exact x.property
  · rintro ⟨hFirst, hSecond⟩
    exact ⟨(input, WithLp.toLp 2 (first ⟨input.snd, hSecond⟩, second ⟨input.fst, hFirst⟩)),
      ⟨first.mem_graph ⟨input.snd, hSecond⟩,
        second.mem_graph ⟨input.fst, hFirst⟩⟩, rfl⟩

theorem rectangularOffDiagonalOperator_apply (input : (rectangularOffDiagonalOperator first second).domain) :
    rectangularOffDiagonalOperator first second input = WithLp.toLp 2
      (first ⟨input.val.snd, ((rectangularOffDiagonalOperator_domain_iff first second _).mp input.property).2⟩,
       second ⟨input.val.fst, ((rectangularOffDiagonalOperator_domain_iff first second _).mp input.property).1⟩) := by
  have h := (rectangularOffDiagonalOperator_mem_graph_iff first second _ _).mp
    ((rectangularOffDiagonalOperator first second).mem_graph input)
  obtain ⟨x, hx, hValue⟩ := (first.mem_graph_iff).mp h.1
  obtain ⟨y, hy, hOther⟩ := (second.mem_graph_iff).mp h.2
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact hValue.symm.trans (congrArg first (Subtype.ext hx))
  · exact hOther.symm.trans (congrArg second (Subtype.ext hy))

theorem rectangularOffDiagonalOperator_dense_domain
    (hFirst : Dense (first.domain : Set F)) (hSecond : Dense (second.domain : Set E)) :
    Dense ((rectangularOffDiagonalOperator first second).domain : Set (WithLp 2 (E × F))) := by
  have h := (hSecond.prod hFirst).preimage
    (WithLp.prodContinuousLinearEquiv 2 Real E F).toHomeomorph.isOpenMap
  convert h using 1
  ext input
  exact rectangularOffDiagonalOperator_domain_iff first second input

theorem rectangularOffDiagonalOperator_isClosed (hFirst : first.IsClosed) (hSecond : second.IsClosed) :
    (rectangularOffDiagonalOperator first second).IsClosed := by
  rw [LinearPMap.IsClosed, rectangularOffDiagonalOperator_graph]
  exact (hFirst.preimage (by fun_prop : Continuous
      (fun pair : WithLp 2 (E × F) × WithLp 2 (E × F) => (pair.1.snd, pair.2.fst)))).inter
    (hSecond.preimage (by fun_prop : Continuous
      (fun pair : WithLp 2 (E × F) × WithLp 2 (E × F) => (pair.1.fst, pair.2.snd))))

end
end JanusFormal.P0EFTJanusProgramPT12RectangularOffDiagonal4D
