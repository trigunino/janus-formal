import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-! An off-diagonal unbounded operator on the Hilbert product. -/
namespace JanusFormal.P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
set_option autoImplicit false
noncomputable section
open Set Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
variable (first second : H →ₗ.[Real] H)

def offDiagonalGraph : Submodule Real (WithLp 2 (H × H) × WithLp 2 (H × H)) where
  carrier := {pair | (pair.1.snd, pair.2.fst) ∈ first.graph ∧
    (pair.1.fst, pair.2.snd) ∈ second.graph}
  zero_mem' := ⟨first.graph.zero_mem, second.graph.zero_mem⟩
  add_mem' hx hy := ⟨first.graph.add_mem hx.1 hy.1, second.graph.add_mem hx.2 hy.2⟩
  smul_mem' scalar _ hx := ⟨first.graph.smul_mem scalar hx.1, second.graph.smul_mem scalar hx.2⟩

def offDiagonalOperator : WithLp 2 (H × H) →ₗ.[Real] WithLp 2 (H × H) :=
  (offDiagonalGraph first second).toLinearPMap

theorem offDiagonalOperator_graph :
    (offDiagonalOperator first second).graph = offDiagonalGraph first second := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  apply WithLp.ofLp_injective 2
  exact Prod.ext
    (first.graph_fst_eq_zero_snd hPair.1 (congrArg WithLp.snd hZero))
    (second.graph_fst_eq_zero_snd hPair.2 (congrArg WithLp.fst hZero))

theorem offDiagonalOperator_mem_graph_iff (input output : WithLp 2 (H × H)) :
    (input, output) ∈ (offDiagonalOperator first second).graph ↔
      (input.snd, output.fst) ∈ first.graph ∧ (input.fst, output.snd) ∈ second.graph := by
  rw [offDiagonalOperator_graph]
  rfl

theorem offDiagonalOperator_domain_iff (input : WithLp 2 (H × H)) :
    input ∈ (offDiagonalOperator first second).domain ↔
      input.fst ∈ second.domain ∧ input.snd ∈ first.domain := by
  constructor
  · intro hInput
    have h := (offDiagonalOperator_mem_graph_iff first second _ _).mp
      ((offDiagonalOperator first second).mem_graph ⟨input, hInput⟩)
    obtain ⟨x, hx, _⟩ := (first.mem_graph_iff).mp h.1
    obtain ⟨y, hy, _⟩ := (second.mem_graph_iff).mp h.2
    change (x : H) = input.snd at hx
    change (y : H) = input.fst at hy
    constructor
    · rw [← hy]; exact y.property
    · rw [← hx]; exact x.property
  · rintro ⟨hFirst, hSecond⟩
    exact ⟨(input, WithLp.toLp 2 (first ⟨input.snd, hSecond⟩, second ⟨input.fst, hFirst⟩)),
      ⟨first.mem_graph ⟨input.snd, hSecond⟩,
        second.mem_graph ⟨input.fst, hFirst⟩⟩, rfl⟩

theorem offDiagonalOperator_apply (input : (offDiagonalOperator first second).domain) :
    offDiagonalOperator first second input = WithLp.toLp 2
      (first ⟨input.val.snd, ((offDiagonalOperator_domain_iff first second _).mp input.property).2⟩,
       second ⟨input.val.fst, ((offDiagonalOperator_domain_iff first second _).mp input.property).1⟩) := by
  have h := (offDiagonalOperator_mem_graph_iff first second _ _).mp
    ((offDiagonalOperator first second).mem_graph input)
  obtain ⟨x, hx, hValue⟩ := (first.mem_graph_iff).mp h.1
  obtain ⟨y, hy, hOther⟩ := (second.mem_graph_iff).mp h.2
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact hValue.symm.trans (congrArg first (Subtype.ext hx))
  · exact hOther.symm.trans (congrArg second (Subtype.ext hy))

theorem offDiagonalOperator_dense_domain
    (hFirst : Dense (first.domain : Set H)) (hSecond : Dense (second.domain : Set H)) :
    Dense ((offDiagonalOperator first second).domain : Set (WithLp 2 (H × H))) := by
  have h := (hSecond.prod hFirst).preimage
    (WithLp.prodContinuousLinearEquiv 2 Real H H).toHomeomorph.isOpenMap
  convert h using 1
  ext input
  exact offDiagonalOperator_domain_iff first second input

theorem offDiagonalOperator_isClosed (hFirst : first.IsClosed) (hSecond : second.IsClosed) :
    (offDiagonalOperator first second).IsClosed := by
  rw [LinearPMap.IsClosed, offDiagonalOperator_graph]
  exact (hFirst.preimage (by fun_prop : Continuous
      (fun pair : WithLp 2 (H × H) × WithLp 2 (H × H) => (pair.1.snd, pair.2.fst)))).inter
    (hSecond.preimage (by fun_prop : Continuous
      (fun pair : WithLp 2 (H × H) × WithLp 2 (H × H) => (pair.1.fst, pair.2.snd))))

end
end JanusFormal.P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
