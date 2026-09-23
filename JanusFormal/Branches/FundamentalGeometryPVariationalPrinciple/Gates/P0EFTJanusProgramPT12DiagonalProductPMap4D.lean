import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-! The direct sum of two partially defined operators on distinct Hilbert spaces. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiagonalProductPMap4D
set_option autoImplicit false
noncomputable section
open Set Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [NormedAddCommGroup F] [InnerProductSpace Real F]
variable (first : E →ₗ.[Real] E) (second : F →ₗ.[Real] F)

def diagonalProductGraph : Submodule Real (WithLp 2 (E × F) × WithLp 2 (E × F)) where
  carrier := {pair | (pair.1.fst, pair.2.fst) ∈ first.graph ∧
    (pair.1.snd, pair.2.snd) ∈ second.graph}
  zero_mem' := ⟨first.graph.zero_mem, second.graph.zero_mem⟩
  add_mem' hx hy := ⟨first.graph.add_mem hx.1 hy.1, second.graph.add_mem hx.2 hy.2⟩
  smul_mem' scalar _ hx := ⟨first.graph.smul_mem scalar hx.1, second.graph.smul_mem scalar hx.2⟩

def diagonalProductOperator : WithLp 2 (E × F) →ₗ.[Real] WithLp 2 (E × F) :=
  (diagonalProductGraph first second).toLinearPMap

theorem diagonalProductOperator_graph :
    (diagonalProductOperator first second).graph = diagonalProductGraph first second := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  apply WithLp.ofLp_injective 2
  exact Prod.ext
    (first.graph_fst_eq_zero_snd hPair.1 (congrArg WithLp.fst hZero))
    (second.graph_fst_eq_zero_snd hPair.2 (congrArg WithLp.snd hZero))

theorem diagonalProductOperator_mem_graph_iff (input output : WithLp 2 (E × F)) :
    (input, output) ∈ (diagonalProductOperator first second).graph ↔
      (input.fst, output.fst) ∈ first.graph ∧ (input.snd, output.snd) ∈ second.graph := by
  rw [diagonalProductOperator_graph]
  rfl

theorem diagonalProductOperator_domain_iff (input : WithLp 2 (E × F)) :
    input ∈ (diagonalProductOperator first second).domain ↔
      input.fst ∈ first.domain ∧ input.snd ∈ second.domain := by
  constructor
  · intro hInput
    have h := (diagonalProductOperator_mem_graph_iff first second _ _).mp
      ((diagonalProductOperator first second).mem_graph ⟨input, hInput⟩)
    obtain ⟨x, hx, _⟩ := (first.mem_graph_iff).mp h.1
    obtain ⟨y, hy, _⟩ := (second.mem_graph_iff).mp h.2
    change (x : E) = input.fst at hx
    change (y : F) = input.snd at hy
    constructor
    · rw [← hx]; exact x.property
    · rw [← hy]; exact y.property
  · rintro ⟨hFirst, hSecond⟩
    exact ⟨(input, WithLp.toLp 2 (first ⟨input.fst, hFirst⟩, second ⟨input.snd, hSecond⟩)),
      ⟨first.mem_graph ⟨input.fst, hFirst⟩,
        second.mem_graph ⟨input.snd, hSecond⟩⟩, rfl⟩

theorem diagonalProductOperator_apply (input : (diagonalProductOperator first second).domain) :
    diagonalProductOperator first second input = WithLp.toLp 2
      (first ⟨input.val.fst, ((diagonalProductOperator_domain_iff first second _).mp input.property).1⟩,
       second ⟨input.val.snd, ((diagonalProductOperator_domain_iff first second _).mp input.property).2⟩) := by
  have h := (diagonalProductOperator_mem_graph_iff first second _ _).mp
    ((diagonalProductOperator first second).mem_graph input)
  obtain ⟨x, hx, hValue⟩ := (first.mem_graph_iff).mp h.1
  obtain ⟨y, hy, hOther⟩ := (second.mem_graph_iff).mp h.2
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact hValue.symm.trans (congrArg first (Subtype.ext hx))
  · exact hOther.symm.trans (congrArg second (Subtype.ext hy))

theorem diagonalProductOperator_dense_domain
    (hFirst : Dense (first.domain : Set E)) (hSecond : Dense (second.domain : Set F)) :
    Dense ((diagonalProductOperator first second).domain : Set (WithLp 2 (E × F))) := by
  have h := (hFirst.prod hSecond).preimage
    (WithLp.prodContinuousLinearEquiv 2 Real E F).toHomeomorph.isOpenMap
  convert h using 1
  ext input
  exact diagonalProductOperator_domain_iff first second input

theorem diagonalProductOperator_isClosed (hFirst : first.IsClosed) (hSecond : second.IsClosed) :
    (diagonalProductOperator first second).IsClosed := by
  rw [LinearPMap.IsClosed, diagonalProductOperator_graph]
  exact (hFirst.preimage (by fun_prop : Continuous
      (fun pair : WithLp 2 (E × F) × WithLp 2 (E × F) => (pair.1.fst, pair.2.fst)))).inter
    (hSecond.preimage (by fun_prop : Continuous
      (fun pair : WithLp 2 (E × F) × WithLp 2 (E × F) => (pair.1.snd, pair.2.snd))))

end
end JanusFormal.P0EFTJanusProgramPT12DiagonalProductPMap4D
