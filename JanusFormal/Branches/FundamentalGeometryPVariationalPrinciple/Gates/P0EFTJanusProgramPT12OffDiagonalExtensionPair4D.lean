import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D

/-! Two self-adjoint extensions of a closed formal-adjoint pair and their common graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12OffDiagonalExtensionPair4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
open P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D
open P0EFTJanusProgramPT12ClosedDoubleAdjoint4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]

theorem adjoint_order_reverse (first second : H →ₗ.[Real] H)
    (hFirst : Dense (first.domain : Set H)) (hSecond : Dense (second.domain : Set H))
    (hLe : first ≤ second) : second.adjoint ≤ first.adjoint := by
  apply LinearPMap.le_of_le_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hFirst,
    LinearPMap.adjoint_graph_eq_graph_adjoint hSecond]
  intro pair hPair
  rw [Submodule.mem_adjoint_iff] at hPair ⊢
  exact fun input output hGraph => hPair input output (LinearPMap.le_graph_of_le hLe hGraph)

theorem closed_formal_pair_reverse (first second : H →ₗ.[Real] H)
    (hClosed : first.IsClosed) (hFirst : Dense (first.domain : Set H))
    (hAdjoint : Dense (first.adjoint.domain : Set H))
    (hSecond : Dense (second.domain : Set H)) (hLe : second ≤ first.adjoint) :
    first ≤ second.adjoint := by
  have h := adjoint_order_reverse second first.adjoint hSecond hAdjoint hLe
  rw [closedOperator_adjoint_adjoint first hClosed hFirst hAdjoint] at h
  exact h

omit [CompleteSpace H] in
theorem offDiagonalOperator_le_iff (first second third fourth : H →ₗ.[Real] H) :
    offDiagonalOperator first second ≤ offDiagonalOperator third fourth ↔
      first ≤ third ∧ second ≤ fourth := by
  constructor
  · intro hLe
    constructor
    · apply LinearPMap.le_of_le_graph
      intro pair hPair
      have h := LinearPMap.le_graph_of_le hLe
        ((offDiagonalOperator_mem_graph_iff first second
          (WithLp.toLp 2 (0, pair.1)) (WithLp.toLp 2 (pair.2, 0))).mpr
          ⟨hPair, second.graph.zero_mem⟩)
      exact ((offDiagonalOperator_mem_graph_iff third fourth _ _).mp h).1
    · apply LinearPMap.le_of_le_graph
      intro pair hPair
      have h := LinearPMap.le_graph_of_le hLe
        ((offDiagonalOperator_mem_graph_iff first second
          (WithLp.toLp 2 (pair.1, 0)) (WithLp.toLp 2 (0, pair.2))).mpr
          ⟨first.graph.zero_mem, hPair⟩)
      exact ((offDiagonalOperator_mem_graph_iff third fourth _ _).mp h).2
  · rintro ⟨hFirst, hSecond⟩
    apply LinearPMap.le_of_le_graph
    intro pair hPair
    have h := (offDiagonalOperator_mem_graph_iff first second _ _).mp hPair
    exact (offDiagonalOperator_mem_graph_iff third fourth _ _).mpr
      ⟨LinearPMap.le_graph_of_le hFirst h.1, LinearPMap.le_graph_of_le hSecond h.2⟩

omit [CompleteSpace H] in
theorem offDiagonalOperator_eq_iff (first second third fourth : H →ₗ.[Real] H) :
    offDiagonalOperator first second = offDiagonalOperator third fourth ↔
      first = third ∧ second = fourth := by
  constructor
  · intro h
    have hLe := (offDiagonalOperator_le_iff first second third fourth).mp h.le
    have hGe := (offDiagonalOperator_le_iff third fourth first second).mp h.ge
    exact ⟨le_antisymm hLe.1 hGe.1, le_antisymm hLe.2 hGe.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem formalPair_graph_intersection (first second : H →ₗ.[Real] H)
    (hForward : second ≤ first.adjoint) (hReverse : first ≤ second.adjoint) :
    (offDiagonalOperator first second).graph =
      (offDiagonalOperator first first.adjoint).graph ⊓
        (offDiagonalOperator second.adjoint second).graph := by
  ext pair
  rw [Submodule.mem_inf, offDiagonalOperator_mem_graph_iff,
    offDiagonalOperator_mem_graph_iff, offDiagonalOperator_mem_graph_iff]
  constructor
  · rintro ⟨hFirst, hSecond⟩
    exact ⟨⟨hFirst, LinearPMap.le_graph_of_le hForward hSecond⟩,
      ⟨LinearPMap.le_graph_of_le hReverse hFirst, hSecond⟩⟩
  · rintro ⟨hFirst, hSecond⟩; exact ⟨hFirst.1, hSecond.2⟩

theorem formalPair_dualBlock_selfAdjoint (first second : H →ₗ.[Real] H)
    (hClosed : second.IsClosed) (hFirst : Dense (first.domain : Set H))
    (hSecond : Dense (second.domain : Set H)) (hReverse : first ≤ second.adjoint) :
    IsSelfAdjoint (offDiagonalOperator second.adjoint second) := by
  have hAdjoint : Dense (second.adjoint.domain : Set H) := hFirst.mono hReverse.1
  rw [LinearPMap.isSelfAdjoint_def,
    offDiagonalOperator_adjoint second.adjoint second hAdjoint hSecond,
    closedOperator_adjoint_adjoint second hClosed hSecond hAdjoint]

theorem formalPair_extensions_eq_iff (first second : H →ₗ.[Real] H)
    (hClosed : first.IsClosed) (hFirst : Dense (first.domain : Set H))
    (hAdjoint : Dense (first.adjoint.domain : Set H)) :
    offDiagonalOperator first first.adjoint = offDiagonalOperator second.adjoint second ↔
      second = first.adjoint := by
  constructor
  · intro h; exact ((offDiagonalOperator_eq_iff _ _ _ _).mp h).2.symm
  · intro h
    rw [h, closedOperator_adjoint_adjoint first hClosed hFirst hAdjoint]

theorem formalPair_minimal_selfAdjoint_iff (first second : H →ₗ.[Real] H)
    (hClosed : first.IsClosed) (hFirst : Dense (first.domain : Set H))
    (hAdjoint : Dense (first.adjoint.domain : Set H))
    (hSecond : Dense (second.domain : Set H)) :
    IsSelfAdjoint (offDiagonalOperator first second) ↔ second = first.adjoint := by
  rw [LinearPMap.isSelfAdjoint_def, offDiagonalOperator_adjoint first second hFirst hSecond]
  constructor
  · intro h; exact ((offDiagonalOperator_eq_iff _ _ _ _).mp h).2.symm
  · intro h
    rw [h, closedOperator_adjoint_adjoint first hClosed hFirst hAdjoint]

theorem selfAdjoint_extension_eq (first second : H →ₗ.[Real] H)
    (hFirst : IsSelfAdjoint first) (hSecond : IsSelfAdjoint second) (hLe : first ≤ second) :
    first = second := by
  have hReverse := adjoint_order_reverse first second hFirst.dense_domain hSecond.dense_domain hLe
  rw [LinearPMap.isSelfAdjoint_def.mp hFirst, LinearPMap.isSelfAdjoint_def.mp hSecond] at hReverse
  exact le_antisymm hLe hReverse

/-- Uniqueness among all self-adjoint extensions is exactly the minimal/maximal equality. -/
theorem formalPair_unique_extension_iff (first second : H →ₗ.[Real] H)
    (hFirstClosed : first.IsClosed) (hSecondClosed : second.IsClosed)
    (hFirst : Dense (first.domain : Set H)) (hSecond : Dense (second.domain : Set H))
    (hAdjoint : Dense (first.adjoint.domain : Set H)) (hLe : second ≤ first.adjoint) :
    (∀ extension : WithLp 2 (H × H) →ₗ.[Real] WithLp 2 (H × H),
      IsSelfAdjoint extension → offDiagonalOperator first second ≤ extension →
        extension = offDiagonalOperator first first.adjoint) ↔ second = first.adjoint := by
  have hReverse := closed_formal_pair_reverse first second hFirstClosed hFirst hAdjoint hSecond hLe
  constructor
  · intro hUnique
    have hEqual := hUnique (offDiagonalOperator second.adjoint second)
      (formalPair_dualBlock_selfAdjoint first second hSecondClosed hFirst hSecond hReverse)
      ((offDiagonalOperator_le_iff _ _ _ _).mpr ⟨hReverse, le_rfl⟩)
    exact (formalPair_extensions_eq_iff first second hFirstClosed hFirst hAdjoint).mp hEqual.symm
  · intro hEqual extension hSelf hExtends
    rw [hEqual] at hExtends
    exact (selfAdjoint_extension_eq _ _
      (offDiagonalOperator_selfAdjoint first hFirstClosed hFirst hAdjoint) hSelf hExtends).symm

end
end JanusFormal.P0EFTJanusProgramPT12OffDiagonalExtensionPair4D
