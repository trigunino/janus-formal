import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedRangeAdjoint4D

/-! The off-diagonal Fredholm problem reduces to one closed range and two kernels. -/
namespace JanusFormal.P0EFTJanusProgramPT12OffDiagonalFredholm4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
open P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D
open P0EFTJanusProgramPT12ProductClosedOperator4D
open P0EFTJanusProgramPT12ProductFredholm4D
open P0EFTJanusProgramPT12ClosedRangeAdjoint4D
open P0EFTJanusProgramPT12NullQuotientFredholm4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem offDiagonalOperator_range_eq_product (A B : H →ₗ.[Real] H) :
    LinearMap.range (offDiagonalOperator A B).toFun = LinearMap.range (productOperator A B).toFun := by
  ext output
  rw [productOperator_range_iff]
  change output ∈ Set.range (offDiagonalOperator A B) ↔ output.fst ∈ Set.range A ∧ output.snd ∈ Set.range B
  rw [LinearPMap.mem_range_iff, LinearPMap.mem_range_iff, LinearPMap.mem_range_iff]
  constructor
  · rintro ⟨input, hGraph⟩
    have h := (offDiagonalOperator_mem_graph_iff A B input output).mp hGraph
    exact ⟨⟨input.snd, h.1⟩, ⟨input.fst, h.2⟩⟩
  · rintro ⟨⟨first, hFirst⟩, ⟨second, hSecond⟩⟩
    exact ⟨WithLp.toLp 2 (second, first),
      (offDiagonalOperator_mem_graph_iff A B _ _).mpr ⟨hFirst, hSecond⟩⟩

def offDiagonalProductKernelEquiv (A B : H →ₗ.[Real] H) :
    LinearMap.ker (offDiagonalOperator A B).toFun ≃ₗ[Real]
      LinearMap.ker (productOperator B A).toFun where
  toFun x := ⟨⟨x.val.val,
    (productOperator_domain_iff B A _).mpr ((offDiagonalOperator_domain_iff A B _).mp x.val.property)⟩, by
      have h := (offDiagonalOperator_mem_graph_iff A B _ _).mp
        ((offDiagonalOperator A B).mem_graph x.val)
      have hz : offDiagonalOperator A B x.val = 0 := x.property
      rw [hz] at h
      exact (productOperator B A).mem_graph_snd_inj ((productOperator B A).mem_graph _)
        ((productOperator_mem_graph_iff B A _ _).mpr ⟨h.2, h.1⟩) rfl⟩
  invFun x := ⟨⟨x.val.val,
    (offDiagonalOperator_domain_iff A B _).mpr ((productOperator_domain_iff B A _).mp x.val.property)⟩, by
      have h := (productOperator_mem_graph_iff B A _ _).mp
        ((productOperator B A).mem_graph x.val)
      have hz : productOperator B A x.val = 0 := x.property
      rw [hz] at h
      exact (offDiagonalOperator A B).mem_graph_snd_inj ((offDiagonalOperator A B).mem_graph _)
        ((offDiagonalOperator_mem_graph_iff A B _ _).mpr ⟨h.2, h.1⟩) rfl⟩
  left_inv _ := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl

omit [CompleteSpace H] in
theorem offDiagonalOperator_kernel_finite_iff (A B : H →ₗ.[Real] H) :
    FiniteDimensional Real (LinearMap.ker (offDiagonalOperator A B).toFun) ↔
      FiniteDimensional Real (LinearMap.ker A.toFun) ∧ FiniteDimensional Real (LinearMap.ker B.toFun) := by
  have heq : FiniteDimensional Real (LinearMap.ker (offDiagonalOperator A B).toFun) ↔
      FiniteDimensional Real (LinearMap.ker (productOperator B A).toFun) := by
    constructor
    · intro h; letI := h; exact (offDiagonalProductKernelEquiv A B).finiteDimensional
    · intro h; letI := h; exact (offDiagonalProductKernelEquiv A B).symm.finiteDimensional
  rw [heq, productOperator_kernel_finite_iff, and_comm]

theorem offDiagonalAdjoint_range_isClosed_iff (A : H →ₗ.[Real] H)
    (hClosed : A.IsClosed) (hDense : Dense (A.domain : Set H))
    (hAdjointDense : Dense (A.adjoint.domain : Set H)) :
    IsClosed (LinearMap.range (offDiagonalOperator A A.adjoint).toFun : Set (WithLp 2 (H × H))) ↔
      IsClosed (LinearMap.range A.toFun : Set H) := by
  rw [offDiagonalOperator_range_eq_product, productOperator_range_isClosed_iff,
    adjoint_range_isClosed_iff A hClosed hDense hAdjointDense, and_self]

theorem offDiagonalAdjoint_fredholm_iff (A : H →ₗ.[Real] H)
    (hClosed : A.IsClosed) (hDense : Dense (A.domain : Set H))
    (hAdjointDense : Dense (A.adjoint.domain : Set H)) :
    (IsClosed (LinearMap.range (offDiagonalOperator A A.adjoint).toFun : Set (WithLp 2 (H × H))) ∧
      FiniteDimensional Real (LinearMap.ker (offDiagonalOperator A A.adjoint).toFun) ∧
      FiniteDimensional Real ((WithLp 2 (H × H)) ⧸ LinearMap.range (offDiagonalOperator A A.adjoint).toFun)) ↔
    (IsClosed (LinearMap.range A.toFun : Set H) ∧
      FiniteDimensional Real (LinearMap.ker A.toFun) ∧ FiniteDimensional Real (LinearMap.ker A.adjoint.toFun)) := by
  rw [selfAdjoint_fredholm_iff _ (offDiagonalOperator_selfAdjoint A hClosed hDense hAdjointDense),
    offDiagonalAdjoint_range_isClosed_iff A hClosed hDense hAdjointDense,
    offDiagonalOperator_kernel_finite_iff]

end
end JanusFormal.P0EFTJanusProgramPT12OffDiagonalFredholm4D
