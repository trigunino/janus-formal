import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic.Abel

/-!
# A bounded resolvent reconstructs an actual unbounded operator domain

An actual two-sided inverse of `μ I - A`, where `A` is a partially defined
linear operator, determines its domain as its range. An isometry intertwining
two such resolvents therefore transports the domains and the operator actions.
No existence of a PDE resolvent or self-adjoint boundary realization is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusUnboundedResolventDomainReconstruction

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace

variable {H H₁ H₂ : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

/-- A genuine bounded resolvent at a real shift, with both inverse identities
on the specified `LinearPMap` domain. -/
structure ResolventAt (A : H →ₗ.[ℝ] H) (μ : ℝ) where
  R : H →L[ℝ] H
  range_mem : ∀ y, R y ∈ A.domain
  left_inv : ∀ x : A.domain, R (μ • (x : H) - A x) = x
  right_inv : ∀ y, μ • R y - A ⟨R y, range_mem y⟩ = y

namespace ResolventAt

variable {A : H →ₗ.[ℝ] H} {μ : ℝ} (r : ResolventAt A μ)

theorem injective : Function.Injective r.R := by
  intro x y h
  have hd : (⟨r.R x, r.range_mem x⟩ : A.domain) =
      ⟨r.R y, r.range_mem y⟩ := Subtype.ext h
  calc
    x = μ • r.R x - A ⟨r.R x, r.range_mem x⟩ := (r.right_inv x).symm
    _ = μ • r.R y - A ⟨r.R y, r.range_mem y⟩ := by rw [hd, h]
    _ = y := r.right_inv y

/-- Resolvent data recover the exact domain, including any boundary conditions
encoded by that domain. -/
theorem mem_domain_iff (x : H) : x ∈ A.domain ↔ ∃ y, r.R y = x := by
  constructor
  · intro hx
    exact ⟨μ • x - A ⟨x, hx⟩, r.left_inv ⟨x, hx⟩⟩
  · rintro ⟨y, rfl⟩
    exact r.range_mem y

theorem range_eq_domain : LinearMap.range r.R.toLinearMap = A.domain := by
  ext x
  exact (r.mem_domain_iff x).symm

theorem action_resolvent (x : H) :
    A ⟨r.R x, r.range_mem x⟩ = μ • r.R x - x := by
  have h := r.right_inv x
  apply eq_sub_iff_add_eq.mpr
  simpa [add_comm] using (sub_eq_iff_eq_add.mp h).symm

/-- Symmetry of the actual unbounded operator makes its real resolvent symmetric.
Density and completeness are unnecessary for this implication. -/
theorem isSymmetric (hA : A.IsFormalAdjoint A) : r.R.IsSymmetric := by
  intro x y
  have h := hA ⟨r.R x, r.range_mem x⟩ ⟨r.R y, r.range_mem y⟩
  rw [r.action_resolvent, r.action_resolvent] at h
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    inner_smul_right] at h
  exact (sub_right_inj.mp h).symm

/-- The usual local resolvent formula is an actual inverse on the same domain,
not merely a formal bounded response. -/
def shift (t : ℝ) (ht : IsUnit (1 - t • r.R)) : ResolventAt A (μ - t) where
  R := r.R * Ring.inverse (1 - t • r.R)
  range_mem y := r.range_mem _
  left_inv x := by
    have hi := congrArg (fun T : H →L[ℝ] H => T (μ • (x : H) - A x))
      (Ring.inverse_mul_cancel (1 - t • r.R) ht)
    have hx : (μ - t) • (x : H) - A x =
        (1 - t • r.R) (μ • (x : H) - A x) := by
      simp only [sub_apply, one_apply_eq_self, smul_apply, r.left_inv, sub_smul]
      abel
    simp only [mul_apply_eq_comp, one_apply_eq_self] at hi ⊢
    rw [hx, hi, r.left_inv]
  right_inv y := by
    have hi := congrArg (fun T : H →L[ℝ] H => T y)
      (Ring.mul_inverse_cancel (1 - t • r.R) ht)
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply] at hi ⊢
    rw [r.action_resolvent, sub_smul]
    calc
      _ = (Ring.inverse (1 - t • r.R)) y -
          t • r.R ((Ring.inverse (1 - t • r.R)) y) := by abel
      _ = y := hi

@[simp] theorem shift_R (t : ℝ) (ht : IsUnit (1 - t • r.R)) :
    (r.shift t ht).R = r.R * Ring.inverse (1 - t • r.R) := rfl

variable {A₁ : H₁ →ₗ.[ℝ] H₁} {A₂ : H₂ →ₗ.[ℝ] H₂}
  (r₁ : ResolventAt A₁ μ) (r₂ : ResolventAt A₂ μ)
  (U : H₁ ≃ₗᵢ[ℝ] H₂)
  (hU : ∀ x, U (r₁.R x) = r₂.R (U x))

include r₁ r₂ hU in
theorem domain_mem_iff (x : H₁) : x ∈ A₁.domain ↔ U x ∈ A₂.domain := by
  rw [r₁.mem_domain_iff, r₂.mem_domain_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨U y, (hU y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨U.symm y, U.injective ?_⟩
    rw [hU, U.apply_symm_apply, hy]

/-- The domain equivalence is constructed from bounded resolvent intertwining;
domain preservation is a conclusion, not an assumption. -/
def domainEquiv : A₁.domain ≃ₗ[ℝ] A₂.domain where
  toFun x := ⟨U x, (domain_mem_iff r₁ r₂ U hU x).mp x.property⟩
  invFun y := ⟨U.symm y, (domain_mem_iff r₁ r₂ U hU (U.symm y)).mpr
    (by simp only [U.apply_symm_apply]; exact y.property)⟩
  left_inv x := Subtype.ext (U.symm_apply_apply x)
  right_inv y := Subtype.ext (U.apply_symm_apply y)
  map_add' x y := Subtype.ext (U.map_add x y)
  map_smul' c x := Subtype.ext (U.map_smul c x)

@[simp] theorem domainEquiv_coe (x : A₁.domain) :
    (domainEquiv r₁ r₂ U hU x : H₂) = U x := rfl

theorem action_intertwining (x : A₁.domain) :
    U (A₁ x) = A₂ (domainEquiv r₁ r₂ U hU x) := by
  have h : r₂.R (U (μ • (x : H₁) - A₁ x)) = U x := by
    rw [← hU, r₁.left_inv]
  have hd : (⟨r₂.R (U (μ • (x : H₁) - A₁ x)), r₂.range_mem _⟩ : A₂.domain) =
      domainEquiv r₁ r₂ U hU x := Subtype.ext h
  have hr := r₂.right_inv (U (μ • (x : H₁) - A₁ x))
  rw [hd, h, map_sub, map_smul] at hr
  exact (sub_right_inj.mp hr).symm

end ResolventAt

end
end P0EFTJanusUnboundedResolventDomainReconstruction
end JanusFormal
