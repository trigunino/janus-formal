import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusObservableBulkReduction

/-!
# Reconstruction from the tail of injective resolvent moments

For an injective bounded self-adjoint operator, shifting a cyclic marking by the
operator preserves cyclicity. Consequently moments of orders at least two already
reconstruct the original marking and operator. This is the algebraic input needed
when a local resolvent response hides its first moment inside a direct boundary term.
Injectivity is essential; no bounded inverse or spectral gap is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusShiftedCyclicReconstruction

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusCyclicMomentReconstruction P0EFTJanusObservableBulkReduction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] {Boundary : Type*}

/-- Injectivity and self-adjointness prevent the shift from losing a cyclic sector. -/
theorem shifted_isCyclic (R : H →L[ℝ] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) (B : Boundary → H) (hcyclic : IsCyclic R B) :
    IsCyclic R (fun q => R (B q)) := by
  have htop : visibleSubspace R B = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hcyclic
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  change visibleSubspace R (fun q => R (B q)) = ⊤
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hRx : R x ∈ (visibleSubspace R B)ᗮ := by
    rw [invisible_iff_krylov]
    intro n q
    have heq : R ((R ^ n) (B q)) = (R ^ n) (R (B q)) := by
      rw [← mul_apply_eq_comp, ← pow_succ', pow_succ, mul_apply_eq_comp]
    calc
      ⟪(R ^ n) (B q), R x⟫_ℝ = ⟪R ((R ^ n) (B q)), x⟫_ℝ :=
        (hR.isSymmetric _ _).symm
      _ = ⟪(R ^ n) (R (B q)), x⟫_ℝ := by rw [heq]
      _ = 0 := (invisible_iff_krylov R (fun q => R (B q)) x).mp hx n q
  have hz : R x = 0 := by
    simpa only [htop, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] using hRx
  exact hinj (hz.trans (map_zero R).symm)

/-- A shift of the marking moves its moments forward by two orders. -/
theorem shifted_boundaryMoment (R : H →L[ℝ] H) (hR : IsSelfAdjoint R)
    (B : Boundary → H) (n : ℕ) (q r : Boundary) :
    boundaryMoment R (fun p => R (B p)) n q r =
      boundaryMoment R B (n + 2) q r := by
  dsimp only [boundaryMoment]
  calc
    ⟪R (B q), (R ^ n) (R (B r))⟫_ℝ =
        ⟪B q, R ((R ^ n) (R (B r)))⟫_ℝ := hR.isSymmetric _ _
    _ = ⟪B q, (R ^ (n + 2)) (B r)⟫_ℝ := by
      congr 1
      rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← pow_succ', ← pow_succ]

omit [CompleteSpace H] in
/-- Restricting an injective operator to the observable sector preserves injectivity. -/
theorem visibleOperator_injective (R : H →L[ℝ] H) (hinj : Function.Injective R)
    (B : Boundary → H) : Function.Injective (visibleOperator R B) := by
  intro x y hxy
  apply Subtype.ext
  apply hinj
  exact congrArg (fun z : visibleSubspace R B => (z : H)) hxy

variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [CompleteSpace H₂]

/-- Equal moments of orders at least two reconstruct both original cyclic markings.
The zeroth and first moments are conclusions, not extra hypotheses. -/
theorem tail_moments_determine_cyclic_realization
    (R₁ : H →L[ℝ] H) (R₂ : H₂ →L[ℝ] H₂)
    (hR₁ : IsSelfAdjoint R₁) (hR₂ : IsSelfAdjoint R₂)
    (hinj₁ : Function.Injective R₁) (hinj₂ : Function.Injective R₂)
    (B₁ : Boundary → H) (B₂ : Boundary → H₂)
    (hcyclic₁ : IsCyclic R₁ B₁) (hcyclic₂ : IsCyclic R₂ B₂)
    (hmom : ∀ n q r, boundaryMoment R₁ B₁ (n + 2) q r =
      boundaryMoment R₂ B₂ (n + 2) q r) :
    ∃! U : H ≃ₗᵢ[ℝ] H₂,
      (∀ q, U (B₁ q) = B₂ q) ∧ (∀ x, U (R₁ x) = R₂ (U x)) := by
  obtain ⟨U, hU, huniq⟩ := moments_determine_cyclic_realization R₁ R₂ hR₁ hR₂
    (fun q => R₁ (B₁ q)) (fun q => R₂ (B₂ q))
    (shifted_isCyclic R₁ hR₁ hinj₁ B₁ hcyclic₁)
    (shifted_isCyclic R₂ hR₂ hinj₂ B₂ hcyclic₂)
    (fun n q r => by simpa only [shifted_boundaryMoment _ hR₁,
      shifted_boundaryMoment _ hR₂] using hmom n q r)
  refine ⟨U, ⟨?_, hU.2⟩, ?_⟩
  · intro q
    apply hinj₂
    rw [← hU.2, hU.1]
  · intro V hV
    apply huniq V
    refine ⟨?_, hV.2⟩
    intro q
    rw [hV.2, hV.1]

/-- In particular, the invisible constant and Gram moments can be recovered. -/
theorem tail_moments_determine_all_moments
    (R₁ : H →L[ℝ] H) (R₂ : H₂ →L[ℝ] H₂)
    (hR₁ : IsSelfAdjoint R₁) (hR₂ : IsSelfAdjoint R₂)
    (hinj₁ : Function.Injective R₁) (hinj₂ : Function.Injective R₂)
    (B₁ : Boundary → H) (B₂ : Boundary → H₂)
    (hcyclic₁ : IsCyclic R₁ B₁) (hcyclic₂ : IsCyclic R₂ B₂)
    (hmom : ∀ n q r, boundaryMoment R₁ B₁ (n + 2) q r =
      boundaryMoment R₂ B₂ (n + 2) q r) :
    ∀ n q r, boundaryMoment R₁ B₁ n q r = boundaryMoment R₂ B₂ n q r := by
  obtain ⟨U, hU, _⟩ := tail_moments_determine_cyclic_realization
    R₁ R₂ hR₁ hR₂ hinj₁ hinj₂ B₁ B₂ hcyclic₁ hcyclic₂ hmom
  exact intertwiner_preserves_moments R₁ R₂ B₁ B₂ U hU.1 hU.2

/-- A tail of moments reconstructs the observable sectors without assuming that
the original realizations are cyclic. Unobserved sectors remain unrestricted. -/
theorem tail_moments_determine_visible_realization
    (R₁ : H →L[ℝ] H) (R₂ : H₂ →L[ℝ] H₂)
    (hR₁ : IsSelfAdjoint R₁) (hR₂ : IsSelfAdjoint R₂)
    (hinj₁ : Function.Injective R₁) (hinj₂ : Function.Injective R₂)
    (B₁ : Boundary → H) (B₂ : Boundary → H₂)
    (hmom : ∀ n q r, boundaryMoment R₁ B₁ (n + 2) q r =
      boundaryMoment R₂ B₂ (n + 2) q r) :
    ∃! U : visibleSubspace R₁ B₁ ≃ₗᵢ[ℝ] visibleSubspace R₂ B₂,
      (∀ q, U (visibleMarking R₁ B₁ q) = visibleMarking R₂ B₂ q) ∧
      (∀ x, U (visibleOperator R₁ B₁ x) = visibleOperator R₂ B₂ (U x)) := by
  apply tail_moments_determine_cyclic_realization
    (visibleOperator R₁ B₁) (visibleOperator R₂ B₂)
    (visible_isSelfAdjoint R₁ hR₁ B₁) (visible_isSelfAdjoint R₂ hR₂ B₂)
    (visibleOperator_injective R₁ hinj₁ B₁) (visibleOperator_injective R₂ hinj₂ B₂)
    (visibleMarking R₁ B₁) (visibleMarking R₂ B₂)
    (visible_isCyclic R₁ B₁) (visible_isCyclic R₂ B₂)
  intro n q r
  simpa only [visible_boundaryMoment] using hmom n q r

/-- The omitted first two moments are recovered even before a cyclic reduction. -/
theorem tail_moments_determine_all_moments_without_cyclicity
    (R₁ : H →L[ℝ] H) (R₂ : H₂ →L[ℝ] H₂)
    (hR₁ : IsSelfAdjoint R₁) (hR₂ : IsSelfAdjoint R₂)
    (hinj₁ : Function.Injective R₁) (hinj₂ : Function.Injective R₂)
    (B₁ : Boundary → H) (B₂ : Boundary → H₂)
    (hmom : ∀ n q r, boundaryMoment R₁ B₁ (n + 2) q r =
      boundaryMoment R₂ B₂ (n + 2) q r) :
    ∀ n q r, boundaryMoment R₁ B₁ n q r = boundaryMoment R₂ B₂ n q r := by
  obtain ⟨U, hU, _⟩ := tail_moments_determine_visible_realization
    R₁ R₂ hR₁ hR₂ hinj₁ hinj₂ B₁ B₂ hmom
  intro n q r
  simpa only [visible_boundaryMoment] using
    intertwiner_preserves_moments _ _ _ _ U hU.1 hU.2 n q r

end
end P0EFTJanusShiftedCyclicReconstruction
end JanusFormal
