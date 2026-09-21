import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Fredholm alternative for identity plus compact operators

This file packages the closed-range and finite-defect consequences needed by
the Program P physical Friedrichs family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCompactIdentityFredholm4D

open scoped ComplexConjugate
open Module End
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem antilipschitz_of_injective_isometry_add_compact
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (J K : X →L[ℝ] Y) (hJ : Isometry J) (hK : IsCompactOperator K)
    (hinj : Function.Injective (J + K)) :
    ∃ c, AntilipschitzWith c (J + K) := by
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  by_contra hanti
  push Not at hanti
  have hsmall : ∃ c > 0, ∀ ε > 0, ∃ x : X,
      ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖(J + K) x‖ < ε := by
    obtain ⟨C, hC⟩ := NormedField.exists_one_lt_norm ℝ
    refine ⟨‖C‖⁻¹, by positivity, fun ε hε ↦ ?_⟩
    obtain ⟨x, hx⟩ := hanti ε hε
    have hx0 : x ≠ 0 := by aesop
    obtain ⟨η, hη, h₁, h₂, h₃⟩ := rescale_to_shell hC (ε := 1) (by simp) hx0
    refine ⟨η • x, h₁.le, by simpa using h₂, ?_⟩
    grw [map_smul, norm_smul, hx, mul_left_comm, ← norm_smul]
    linear_combination ε * h₁
  obtain ⟨c, hc0, hc⟩ := hsmall
  obtain ⟨φ, hφanti, hφpos, hφlim⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  have (n : ℕ) : ∃ x : X,
      ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖(J + K) x‖ < φ n := hc (φ n) (hφpos n)
  choose x hxupper hxlower hxsmall using this
  have hSlim : Tendsto (fun n ↦ (J + K) (x n)) atTop (nhds 0) :=
    squeeze_zero_norm (by grind) hφlim
  obtain ⟨A, hA, hKA⟩ := hK.image_closedBall_subset_compact 1
  obtain ⟨y, hyA, ψ, hψ, hKlim⟩ := hA.tendsto_subseq
    (x := fun n ↦ K (x n)) (fun n ↦ hKA ⟨x n, by simp [hxupper n], rfl⟩)
  have hJlim : Tendsto (fun n ↦ J (x (ψ n))) atTop (nhds (-y)) := by
    simpa using (hSlim.comp hψ.tendsto_atTop).sub hKlim
  have hyRange : -y ∈ Set.range J :=
    hJ.isClosedEmbedding.isClosed_range.mem_of_tendsto hJlim (.of_forall fun n ↦ ⟨x (ψ n), rfl⟩)
  obtain ⟨x0, hx0⟩ := hyRange
  have hxlim : Tendsto (fun n ↦ x (ψ n)) atTop (nhds x0) := by
    apply hJ.tendsto_nhds_iff.mpr
    simpa [Function.comp_def, hx0] using hJlim
  have hSx0 : (J + K) x0 = 0 := by
    exact (tendsto_nhds_unique (hSlim.comp hψ.tendsto_atTop)
      ((J + K).continuous.continuousAt.tendsto.comp hxlim)).symm
  have hx0zero : x0 = 0 := hinj (by simpa using hSx0)
  have hclower : c ≤ ‖x0‖ :=
    ge_of_tendsto (tendsto_norm.comp hxlim) (.of_forall fun n ↦ hxlower (ψ n))
  simpa [hx0zero] using (lt_of_lt_of_le hc0 hclower)

theorem compact_identity_add_isClosed_range
    (K : E →L[ℝ] E) (hK : IsCompactOperator K) :
    IsClosed (Set.range (ContinuousLinearMap.id ℝ E + K)) := by
  let T : E →L[ℝ] E := ContinuousLinearMap.id ℝ E + K
  let U : Submodule ℝ E := T.ker.orthogonal
  let J : U →L[ℝ] E := U.subtypeL
  let K' : U →L[ℝ] E := K ∘L U.subtypeL
  have hcompact : IsCompactOperator K' := hK.comp_clm U.subtypeL
  have hJ : Isometry J := by
    intro x y
    rfl
  have hoperator : J + K' = T ∘L U.subtypeL := by
    ext x
    simp [J, K', T]
  have hinj : Function.Injective (J + K') := by
    intro x y hxy
    have hTxy : T ((x : E) - (y : E)) = 0 := by
      have : (T ∘L U.subtypeL) x = (T ∘L U.subtypeL) y := by
        simpa [hoperator] using hxy
      simpa using sub_eq_zero.mpr this
    have hker : (x : E) - (y : E) ∈ T.ker := hTxy
    have horth : (x : E) - (y : E) ∈ T.ker.orthogonal := U.sub_mem x.property y.property
    have hbot : (x : E) - (y : E) ∈ (⊥ : Submodule ℝ E) := by
      rw [← T.ker.orthogonal_disjoint.eq_bot]
      exact ⟨hker, horth⟩
    exact Subtype.ext (sub_eq_zero.mp (by simpa using hbot))
  obtain ⟨c, hc⟩ :=
    antilipschitz_of_injective_isometry_add_compact J K' hJ hcompact hinj
  have hclosedS : IsClosed (Set.range (J + K')) :=
    hc.isClosed_range (J + K').uniformContinuous
  have hrange : Set.range (J + K') = Set.range T := by
    apply Set.Subset.antisymm
    · rintro z ⟨u, rfl⟩
      exact ⟨(u : E), by simp [hoperator]⟩
    · rintro z ⟨x, rfl⟩
      obtain ⟨y, hy, z, hz, hx⟩ := T.ker.exists_add_mem_mem_orthogonal x
      refine ⟨⟨z, hz⟩, ?_⟩
      rw [hoperator]
      change T z = T x
      rw [hx, map_add, show T y = 0 from hy, zero_add]
  rw [← hrange]
  exact hclosedS

theorem compact_identity_add_finite_kernel
    (K : E →L[ℝ] E) (hK : IsCompactOperator K) :
    FiniteDimensional ℝ (ContinuousLinearMap.id ℝ E + K).ker := by
  letI : FiniteDimensional ℝ (eigenspace K.toLinearMap (-1 : ℝ)) :=
    K.finite_dimensional_eigenspace hK (-1) (by norm_num)
  let e : (ContinuousLinearMap.id ℝ E + K).ker ≃ₗ[ℝ]
      eigenspace K.toLinearMap (-1 : ℝ) :=
    LinearEquiv.ofEq _ _ (by
      ext x
      rw [mem_eigenspace_iff]
      change (ContinuousLinearMap.id ℝ E + K) x = 0 ↔ K x = (-1 : ℝ) • x
      simp only [add_apply, ContinuousLinearMap.id_apply, neg_one_smul]
      constructor
      · intro h
        exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h)
      · intro h
        rw [h]
        exact add_neg_cancel x)
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

theorem compact_identity_add_finite_orthogonal_cokernel_of_closed_range
    (K : E →L[ℝ] E) (hK : IsCompactOperator K)
    (hrange : IsClosed (Set.range (ContinuousLinearMap.id ℝ E + K))) :
    FiniteDimensional ℝ (ContinuousLinearMap.id ℝ E + K).range.orthogonal := by
  let T : E →L[ℝ] E := ContinuousLinearMap.id ℝ E + K
  have hrangeT : IsClosed (Set.range (T : E → E)) := by
    simpa only [T] using hrange
  have hset : (T.range : Set E) = Set.range (T : E → E) := by
    ext x
    constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, rfl⟩
  have hrange' : IsClosed (T.range : Set E) := by
    rw [hset]
    exact hrangeT
  letI : CompleteSpace T.range := hrange'.completeSpace_coe
  let C : Submodule ℝ E := T.range.orthogonal
  have hcompact : IsCompactOperator
      (C.orthogonalProjectionOnto ∘L K ∘L C.subtypeL) :=
    (hK.comp_clm C.subtypeL).clm_comp C.orthogonalProjectionOnto
  have hop : C.orthogonalProjectionOnto ∘L K ∘L C.subtypeL =
      -(ContinuousLinearMap.id ℝ C) := by
    ext z
    have hzero : C.orthogonalProjectionOnto (T (z : E)) = 0 := by
      apply C.orthogonalProjectionOnto_eq_zero_iff.mpr
      exact T.range.le_orthogonal_orthogonal ⟨z, rfl⟩
    change (C.orthogonalProjectionOnto (K (z : E)) : E) = ((-z : C) : E)
    have hsum : z + C.orthogonalProjectionOnto (K (z : E)) = 0 := by
      simpa [T] using hzero
    exact congrArg Subtype.val
      (eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hsum))
  have hid : IsCompactOperator (ContinuousLinearMap.id ℝ C) := by
    have hneg : IsCompactOperator (fun z : C ↦
        -((C.orthogonalProjectionOnto ∘L K ∘L C.subtypeL) z)) := hcompact.neg
    have heq : (fun z : C ↦
        -((C.orthogonalProjectionOnto ∘L K ∘L C.subtypeL) z)) = fun z ↦ z := by
      funext z
      have hz := DFunLike.congr_fun hop z
      simpa using congrArg Neg.neg hz
    rw [heq] at hneg
    change IsCompactOperator (fun z : C ↦ z)
    exact hneg
  exact isCompactOperator_id_iff_finiteDimensional.mp hid

theorem compact_identity_add_fredholm
    (K : E →L[ℝ] E) (hK : IsCompactOperator K) :
    IsClosed (Set.range (ContinuousLinearMap.id ℝ E + K)) ∧
      FiniteDimensional ℝ (ContinuousLinearMap.id ℝ E + K).ker ∧
      FiniteDimensional ℝ
        (ContinuousLinearMap.id ℝ E + K).range.orthogonal := by
  have hrange := compact_identity_add_isClosed_range K hK
  exact ⟨hrange, compact_identity_add_finite_kernel K hK,
    compact_identity_add_finite_orthogonal_cokernel_of_closed_range K hK hrange⟩

end P0EFTJanusProgramPCompactIdentityFredholm4D
end JanusFormal
