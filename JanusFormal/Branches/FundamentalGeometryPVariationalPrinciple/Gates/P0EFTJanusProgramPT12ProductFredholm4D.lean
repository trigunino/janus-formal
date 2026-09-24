import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NullQuotientFredholm4D

/-! Exact Fredholm criterion for a product of actual self-adjoint operators. -/
namespace JanusFormal.P0EFTJanusProgramPT12ProductFredholm4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12ProductClosedOperator4D
open P0EFTJanusProgramPT12ProductSelfAdjoint4D
open P0EFTJanusProgramPT12NullQuotientFredholm4D
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace Real K] [CompleteSpace K]
variable (A : H →ₗ.[Real] H) (B : K →ₗ.[Real] K)

omit [CompleteSpace H] [CompleteSpace K] in
theorem productOperator_range_iff (output : WithLp 2 (H × K)) :
    output ∈ LinearMap.range (productOperator A B).toFun ↔
      output.fst ∈ LinearMap.range A.toFun ∧ output.snd ∈ LinearMap.range B.toFun := by
  change output ∈ Set.range (productOperator A B) ↔ output.fst ∈ Set.range A ∧ output.snd ∈ Set.range B
  rw [LinearPMap.mem_range_iff, LinearPMap.mem_range_iff, LinearPMap.mem_range_iff]
  constructor
  · rintro ⟨input, hGraph⟩
    have h := (productOperator_mem_graph_iff A B input output).mp hGraph
    exact ⟨⟨input.fst, h.1⟩, ⟨input.snd, h.2⟩⟩
  · rintro ⟨⟨first, hFirst⟩, ⟨second, hSecond⟩⟩
    exact ⟨WithLp.toLp 2 (first, second), (productOperator_mem_graph_iff A B _ _).mpr ⟨hFirst, hSecond⟩⟩

omit [CompleteSpace H] [CompleteSpace K] in
theorem productOperator_range_isClosed_iff :
    IsClosed (LinearMap.range (productOperator A B).toFun : Set (WithLp 2 (H × K))) ↔
      IsClosed (LinearMap.range A.toFun : Set H) ∧ IsClosed (LinearMap.range B.toFun : Set K) := by
  constructor
  · intro hClosed
    constructor
    · have hSet : (LinearMap.range A.toFun : Set H) =
          (fun x : H => WithLp.toLp 2 (x, (0 : K))) ⁻¹' (LinearMap.range (productOperator A B).toFun : Set (WithLp 2 (H × K))) := by
        ext x
        change x ∈ LinearMap.range A.toFun ↔ WithLp.toLp 2 (x, (0 : K)) ∈ LinearMap.range (productOperator A B).toFun
        exact ⟨fun h => (productOperator_range_iff A B _).mpr ⟨h, Submodule.zero_mem _⟩,
          fun h => ((productOperator_range_iff A B _).mp h).1⟩
      rw [hSet]
      exact hClosed.preimage (by fun_prop)
    · have hSet : (LinearMap.range B.toFun : Set K) =
          (fun x : K => WithLp.toLp 2 ((0 : H), x)) ⁻¹' (LinearMap.range (productOperator A B).toFun : Set (WithLp 2 (H × K))) := by
        ext x
        change x ∈ LinearMap.range B.toFun ↔ WithLp.toLp 2 ((0 : H), x) ∈ LinearMap.range (productOperator A B).toFun
        exact ⟨fun h => (productOperator_range_iff A B _).mpr ⟨Submodule.zero_mem _, h⟩,
          fun h => ((productOperator_range_iff A B _).mp h).2⟩
      rw [hSet]
      exact hClosed.preimage (by fun_prop)
  · rintro ⟨hA, hB⟩
    have hSet : (LinearMap.range (productOperator A B).toFun : Set (WithLp 2 (H × K))) =
        WithLp.fst ⁻¹' (LinearMap.range A.toFun : Set H) ∩ WithLp.snd ⁻¹' (LinearMap.range B.toFun : Set K) := by
      ext output
      exact productOperator_range_iff A B output
    rw [hSet]
    exact (hA.preimage (WithLp.fstL 2 Real H K).continuous).inter
      (hB.preimage (WithLp.sndL 2 Real H K).continuous)

def productKernelEquiv : LinearMap.ker (productOperator A B).toFun ≃ₗ[Real]
    LinearMap.ker A.toFun × LinearMap.ker B.toFun where
  toFun x :=
    (⟨⟨x.val.val.fst, ((productOperator_domain_iff A B _).mp x.val.property).1⟩, by
      have h := productOperator_apply A B x.val
      have hZero : productOperator A B x.val = 0 := x.property
      rw [hZero] at h
      exact (congrArg WithLp.fst h).symm⟩,
     ⟨⟨x.val.val.snd, ((productOperator_domain_iff A B _).mp x.val.property).2⟩, by
      have h := productOperator_apply A B x.val
      have hZero : productOperator A B x.val = 0 := x.property
      rw [hZero] at h
      exact (congrArg WithLp.snd h).symm⟩)
  invFun x := ⟨⟨WithLp.toLp 2 (x.1.val.val, x.2.val.val),
    (productOperator_domain_iff A B _).mpr ⟨x.1.val.property, x.2.val.property⟩⟩, by
      change productOperator A B _ = 0
      rw [productOperator_apply]
      apply WithLp.ofLp_injective 2
      exact Prod.ext x.1.property x.2.property⟩
  left_inv _ := by apply Subtype.ext; apply Subtype.ext; apply WithLp.ofLp_injective 2; rfl
  right_inv _ := by apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext <;> rfl
  map_add' _ _ := by apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext <;> rfl
  map_smul' _ _ := by apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext <;> rfl

omit [CompleteSpace H] [CompleteSpace K] in
theorem productOperator_kernel_finite_iff :
    FiniteDimensional Real (LinearMap.ker (productOperator A B).toFun) ↔
      FiniteDimensional Real (LinearMap.ker A.toFun) ∧ FiniteDimensional Real (LinearMap.ker B.toFun) := by
  constructor
  · intro hFinite
    letI := hFinite
    letI := (productKernelEquiv A B).finiteDimensional
    exact ⟨FiniteDimensional.of_surjective (LinearMap.fst Real (LinearMap.ker A.toFun) (LinearMap.ker B.toFun)) (fun x => ⟨(x, 0), rfl⟩),
      FiniteDimensional.of_surjective (LinearMap.snd Real (LinearMap.ker A.toFun) (LinearMap.ker B.toFun)) (fun x => ⟨(0, x), rfl⟩)⟩
  · rintro ⟨hA, hB⟩
    letI := hA
    letI := hB
    exact (productKernelEquiv A B).symm.finiteDimensional

theorem productOperator_fredholm_iff (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    (IsClosed (LinearMap.range (productOperator A B).toFun : Set (WithLp 2 (H × K))) ∧
      FiniteDimensional Real (LinearMap.ker (productOperator A B).toFun) ∧
      FiniteDimensional Real (WithLp 2 (H × K) ⧸ LinearMap.range (productOperator A B).toFun)) ↔
    ((IsClosed (LinearMap.range A.toFun : Set H) ∧ FiniteDimensional Real (LinearMap.ker A.toFun)) ∧
      (IsClosed (LinearMap.range B.toFun : Set K) ∧ FiniteDimensional Real (LinearMap.ker B.toFun))) := by
  rw [selfAdjoint_fredholm_iff _ (productOperator_selfAdjoint A B hA hB),
    productOperator_range_isClosed_iff, productOperator_kernel_finite_iff]
  tauto

end
end JanusFormal.P0EFTJanusProgramPT12ProductFredholm4D
