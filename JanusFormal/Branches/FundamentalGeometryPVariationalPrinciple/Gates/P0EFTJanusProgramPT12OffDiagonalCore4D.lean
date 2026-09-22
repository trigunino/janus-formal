import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalClosure4D

/-! The off-diagonal core problem reduces exactly to its two component cores. -/
namespace JanusFormal.P0EFTJanusProgramPT12OffDiagonalCore4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
open P0EFTJanusProgramPT12OffDiagonalClosure4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]

def pairedCore (core : Submodule Real H) : Submodule Real (WithLp 2 (H × H)) :=
  (core.prod core).comap (WithLp.linearEquiv 2 Real (H × H)).toLinearMap

theorem restriction_mem_graph_iff (operator : H →ₗ.[Real] H) (core : Submodule Real H)
    (input output : H) :
    (input, output) ∈ (operator.domRestrict core).graph ↔
      input ∈ core ∧ (input, output) ∈ operator.graph := by
  constructor
  · intro h
    obtain ⟨vector, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp h
    change (vector : H) = input at hInput
    refine ⟨?_, (operator.mem_graph_iff).mpr ⟨⟨vector.val, vector.property.2⟩, hInput, hOutput⟩⟩
    rw [← hInput]
    exact vector.property.1
  · rintro ⟨hCore, hGraph⟩
    obtain ⟨vector, hInput, hOutput⟩ := operator.mem_graph_iff.mp hGraph
    change (vector : H) = input at hInput
    have hDomain : input ∈ operator.domain := by rw [← hInput]; exact vector.property
    exact (LinearPMap.mem_graph_iff _).mpr
      ⟨⟨input, hCore, hDomain⟩, rfl, (LinearPMap.domRestrict_apply hInput.symm).trans hOutput⟩

theorem offDiagonalOperator_restriction (first second : H →ₗ.[Real] H) (core : Submodule Real H) :
    (offDiagonalOperator first second).domRestrict (pairedCore core) =
      offDiagonalOperator (first.domRestrict core) (second.domRestrict core) := by
  apply LinearPMap.eq_of_eq_graph
  ext pair
  rw [restriction_mem_graph_iff, offDiagonalOperator_mem_graph_iff,
    offDiagonalOperator_mem_graph_iff, restriction_mem_graph_iff, restriction_mem_graph_iff]
  change ((pair.1.fst ∈ core ∧ pair.1.snd ∈ core) ∧
    (pair.1.snd, pair.2.fst) ∈ first.graph ∧ (pair.1.fst, pair.2.snd) ∈ second.graph) ↔ _
  tauto

theorem offDiagonalOperator_right_injective (first : H →ₗ.[Real] H) :
    Function.Injective (offDiagonalOperator first) := by
  intro second other hEqual
  apply LinearPMap.eq_of_eq_graph
  ext pair
  constructor
  · intro h
    have hBlock := (offDiagonalOperator_mem_graph_iff first second
      (WithLp.toLp 2 (pair.1, 0)) (WithLp.toLp 2 (0, pair.2))).mpr ⟨first.graph.zero_mem, h⟩
    rw [hEqual] at hBlock
    exact ((offDiagonalOperator_mem_graph_iff first other _ _).mp hBlock).2
  · intro h
    have hBlock := (offDiagonalOperator_mem_graph_iff first other
      (WithLp.toLp 2 (pair.1, 0)) (WithLp.toLp 2 (0, pair.2))).mpr ⟨first.graph.zero_mem, h⟩
    rw [← hEqual] at hBlock
    exact ((offDiagonalOperator_mem_graph_iff first second _ _).mp hBlock).2

theorem offDiagonalOperator_hasCore_iff (first second : H →ₗ.[Real] H)
    (hFirst : first.IsClosed) (hSecond : second.IsClosed)
    (core : Submodule Real H) (hFirstCore : first.HasCore core) (hSecondMem : core ≤ second.domain) :
    (offDiagonalOperator first second).HasCore (pairedCore core) ↔ second.HasCore core := by
  have hFirstRestrict : first.domRestrict core ≤ first := LinearPMap.domRestrict_le
  have hSecondRestrict : second.domRestrict core ≤ second := LinearPMap.domRestrict_le
  have hClosure : ((offDiagonalOperator first second).domRestrict (pairedCore core)).closure =
      offDiagonalOperator first (second.domRestrict core).closure := by
    rw [offDiagonalOperator_restriction, offDiagonalOperator_closure _ _
      (hFirst.isClosable.leIsClosable hFirstRestrict) (hSecond.isClosable.leIsClosable hSecondRestrict),
      hFirstCore.closure_eq]
  constructor
  · intro hCore
    exact ⟨hSecondMem, offDiagonalOperator_right_injective first
      (hClosure.symm.trans hCore.closure_eq)⟩
  · intro hCore
    refine ⟨?_, hClosure.trans (congrArg (offDiagonalOperator first) hCore.closure_eq)⟩
    intro input hInput
    exact (offDiagonalOperator_domain_iff first second input).mpr
      ⟨hSecondMem hInput.1, hFirstCore.le_domain hInput.2⟩

end
end JanusFormal.P0EFTJanusProgramPT12OffDiagonalCore4D
