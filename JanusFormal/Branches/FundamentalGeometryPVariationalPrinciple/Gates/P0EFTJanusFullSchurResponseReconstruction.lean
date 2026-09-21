import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCyclicMomentReconstruction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusResolventMomentIdentification
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusObservableBulkReduction

/-!
# Direct boundary term and full quadratic action from a Schur response

At inverse spectral parameter `t = 1/z`, the Schur response takes the form
`C + t G(t)`, where `G(t)` is the normalized bulk resolvent response. Its
punctured germ determines both the direct term and the continuous germ `G`.
This is reconstruction from supplied response data, not physical selection.
-/

namespace JanusFormal
namespace P0EFTJanusFullSchurResponseReconstruction

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped InnerProductSpace
open P0EFTJanusCyclicMomentReconstruction
open P0EFTJanusResolventMomentIdentification
open P0EFTJanusObservableBulkReduction

/-- Recover the direct term by continuity, then cancel the inverse spectral
parameter. No value of the measured response at infinity is assumed. -/
theorem punctured_schur_germ_identifies_direct_and_response
    (c₁ c₂ : ℝ) (g₁ g₂ : ℝ → ℝ)
    (hg₁ : ContinuousAt g₁ 0) (hg₂ : ContinuousAt g₂ 0)
    (h : (fun t => c₁ + t * g₁ t) =ᶠ[𝓝[≠] 0] (fun t => c₂ + t * g₂ t)) :
    c₁ = c₂ ∧ g₁ =ᶠ[𝓝 0] g₂ := by
  have hfull := (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (continuousAt_const.add (continuousAt_id.mul hg₁))
    (continuousAt_const.add (continuousAt_id.mul hg₂))).1 h
  have hc : c₁ = c₂ := by simpa using hfull.eq_of_nhds
  refine ⟨hc, (hg₁.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg₂).1 ?_⟩
  filter_upwards [h, self_mem_nhdsWithin] with t ht hne
  have ht0 : t ≠ 0 := hne
  rw [hc] at ht
  exact mul_left_cancel₀ ht0 (add_left_cancel ht)

variable {H₁ H₂ Boundary : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

/-- The actual resolvent `(z I-A)⁻¹` in inverse spectral coordinates.
The identity is algebraic; physical resolvent use still requires invertibility. -/
theorem resolvent_inverse_parameter (A : H₁ →L[ℝ] H₁) (t : ℝ) (ht : t ≠ 0) :
    resolvent A t⁻¹ = t • Ring.inverse (1 - t • A) := by
  let u : ℝˣ := Units.mk0 t⁻¹ (inv_ne_zero ht)
  have h := @spectrum.units_smul_resolvent_self ℝ (H₁ →L[ℝ] H₁) _ _ _ u A
  have h' := congrArg (fun T : H₁ →L[ℝ] H₁ => t • T) h
  simpa [u, Units.smul_def, smul_smul, ht, resolvent,
    Algebra.algebraMap_eq_smul_one] using h'

/-- Quadratic expression for a bounded parent with a marked coupling and
direct boundary pairing. In the linear physical subclass, B is a continuous
linear map and C a symmetric continuous bilinear form. -/
def boundedParentAction (A : H₁ →L[ℝ] H₁) (B : Boundary → H₁)
    (C : Boundary → Boundary → ℝ) (x : H₁) (q : Boundary) : ℝ :=
  ⟪x, A x⟫_ℝ / 2 + ⟪x, B q⟫_ℝ + C q q / 2

theorem intertwiner_preserves_parent_action
    (A₁ : H₁ →L[ℝ] H₁) (A₂ : H₂ →L[ℝ] H₂)
    (B₁ : Boundary → H₁) (B₂ : Boundary → H₂)
    (C₁ C₂ : Boundary → Boundary → ℝ)
    (U : H₁ ≃ₗᵢ[ℝ] H₂)
    (hB : ∀ q, U (B₁ q) = B₂ q) (hA : ∀ x, U (A₁ x) = A₂ (U x))
    (hC : ∀ q r, C₁ q r = C₂ q r) (x : H₁) (q : Boundary) :
    boundedParentAction A₁ B₁ C₁ x q = boundedParentAction A₂ B₂ C₂ (U x) q := by
  unfold boundedParentAction
  rw [← U.inner_map_map x (A₁ x), ← U.inner_map_map x (B₁ q), hA, hB, hC]

/-- `C-B*(A-zI)⁻¹B`, written with the standard `(zI-A)⁻¹` resolvent. -/
def fullSchurResponse (A : H₁ →L[ℝ] H₁) (B : Boundary → H₁)
    (C : Boundary → Boundary → ℝ) (z : ℝ) (q r : Boundary) : ℝ :=
  C q r + ⟪B q, resolvent A z (B r)⟫_ℝ

/-- Algebraic identification with the actual spectral response, not just a
formal generating function. -/
theorem full_schur_inverse_parameter
    [CompleteSpace H₁] (A : H₁ →L[ℝ] H₁) (B : Boundary → H₁)
    (C : Boundary → Boundary → ℝ) (t : ℝ) (ht : t ≠ 0) (q r : Boundary) :
    fullSchurResponse A B C t⁻¹ q r = C q r + t * normalizedResponse A B t q r := by
  rw [fullSchurResponse, resolvent_inverse_parameter A t ht]
  simp [normalizedResponse, real_inner_smul_right]

variable [CompleteSpace H₁] [CompleteSpace H₂]

/-- The totalized ring inverse is a genuine resolvent throughout a sufficiently
large spectral region. Thus the asymptotic comparisons avoid the spectrum. -/
theorem full_schur_eventually_regular (A : H₁ →L[ℝ] H₁) :
    ∀ᶠ z in Bornology.cobounded ℝ, z ∈ resolventSet ℝ A := by
  exact (spectrum.eventually_isUnit_resolvent A).mono
    (fun _ hz => spectrum.isUnit_resolvent.mpr hz)

/-- The measured full response recovers the direct boundary pairing as well
as every bulk moment. No equality of C is supplied as an input. -/
theorem full_schur_germ_identifies_direct_and_moments
    (A₁ : H₁ →L[ℝ] H₁) (A₂ : H₂ →L[ℝ] H₂)
    (B₁ : Boundary → H₁) (B₂ : Boundary → H₂)
    (C₁ C₂ : Boundary → Boundary → ℝ)
    (hresponse : ∀ q r, ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      fullSchurResponse A₁ B₁ C₁ t⁻¹ q r = fullSchurResponse A₂ B₂ C₂ t⁻¹ q r) :
    (∀ q r, C₁ q r = C₂ q r) ∧
      (∀ n q r, boundaryMoment A₁ B₁ n q r = boundaryMoment A₂ B₂ n q r) := by
  have hg : ∀ q r, C₁ q r = C₂ q r ∧
      (fun t => normalizedResponse A₁ B₁ t q r) =ᶠ[𝓝 0]
        (fun t => normalizedResponse A₂ B₂ t q r) := by
    intro q r
    apply punctured_schur_germ_identifies_direct_and_response
      (C₁ q r) (C₂ q r) _ _
      (normalizedResponse_continuousAt_zero A₁ B₁ q r)
      (normalizedResponse_continuousAt_zero A₂ B₂ q r)
    filter_upwards [hresponse q r, self_mem_nhdsWithin] with t ht ht0
    simpa only [full_schur_inverse_parameter _ _ _ t ht0] using ht
  exact ⟨fun q r => (hg q r).1,
    response_eq_eventually_implies_moments A₁ A₂ B₁ B₂ (fun q r => (hg q r).2)⟩

/-- Complete cyclic bounded parent reconstruction, including C and the full
quadratic action. Uniqueness is for the marked isometric intertwiner. -/
theorem full_schur_germ_reconstructs_cyclic_parent
    (A₁ : H₁ →L[ℝ] H₁) (A₂ : H₂ →L[ℝ] H₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂)
    (B₁ : Boundary → H₁) (B₂ : Boundary → H₂)
    (C₁ C₂ : Boundary → Boundary → ℝ)
    (hcyclic₁ : IsCyclic A₁ B₁) (hcyclic₂ : IsCyclic A₂ B₂)
    (hresponse : ∀ q r, ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      fullSchurResponse A₁ B₁ C₁ t⁻¹ q r = fullSchurResponse A₂ B₂ C₂ t⁻¹ q r) :
    (∀ q r, C₁ q r = C₂ q r) ∧
    ∃! U : H₁ ≃ₗᵢ[ℝ] H₂,
      (∀ q, U (B₁ q) = B₂ q) ∧ (∀ x, U (A₁ x) = A₂ (U x)) ∧
      (∀ x q, boundedParentAction A₁ B₁ C₁ x q =
        boundedParentAction A₂ B₂ C₂ (U x) q) := by
  rcases full_schur_germ_identifies_direct_and_moments A₁ A₂ B₁ B₂ C₁ C₂ hresponse
    with ⟨hC, hmom⟩
  rcases moments_determine_cyclic_realization A₁ A₂ hA₁ hA₂ B₁ B₂
    hcyclic₁ hcyclic₂ hmom with ⟨U, hU, hUnique⟩
  refine ⟨hC, U, ⟨hU.1, hU.2, ?_⟩, ?_⟩
  · exact intertwiner_preserves_parent_action A₁ A₂ B₁ B₂ C₁ C₂ U hU.1 hU.2 hC
  · intro V hV
    exact hUnique V ⟨hV.1, hV.2.1⟩

/-- Passing to the constructed observable bulk preserves the complete measured
Schur germ, not just its formal moments. -/
theorem visible_full_schur_response_germ
    (A : H₁ →L[ℝ] H₁) (B : Boundary → H₁) (C : Boundary → Boundary → ℝ)
    (q r : Boundary) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      fullSchurResponse (visibleOperator A B) (visibleMarking A B) C t⁻¹ q r =
        fullSchurResponse A B C t⁻¹ q r := by
  have hg := moments_imply_response_eq_eventually
    (visibleOperator A B) A (visibleMarking A B) B (visible_boundaryMoment A B) q r
  filter_upwards [hg.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
  rw [full_schur_inverse_parameter _ _ _ t ht0,
    full_schur_inverse_parameter _ _ _ t ht0, ht]

/-- No original cyclicity assumption: the full response determines the direct
boundary term and the unique equivalence of the constructed observable actions. -/
theorem full_schur_germ_reconstructs_visible_parent
    (A₁ : H₁ →L[ℝ] H₁) (A₂ : H₂ →L[ℝ] H₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂)
    (B₁ : Boundary → H₁) (B₂ : Boundary → H₂)
    (C₁ C₂ : Boundary → Boundary → ℝ)
    (hresponse : ∀ q r, ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      fullSchurResponse A₁ B₁ C₁ t⁻¹ q r = fullSchurResponse A₂ B₂ C₂ t⁻¹ q r) :
    (∀ q r, C₁ q r = C₂ q r) ∧
    ∃! U : visibleSubspace A₁ B₁ ≃ₗᵢ[ℝ] visibleSubspace A₂ B₂,
      (∀ q, U (visibleMarking A₁ B₁ q) = visibleMarking A₂ B₂ q) ∧
      (∀ x, U (visibleOperator A₁ B₁ x) = visibleOperator A₂ B₂ (U x)) ∧
      (∀ x q,
        boundedParentAction (visibleOperator A₁ B₁) (visibleMarking A₁ B₁) C₁ x q =
        boundedParentAction (visibleOperator A₂ B₂) (visibleMarking A₂ B₂) C₂ (U x) q) := by
  rcases full_schur_germ_identifies_direct_and_moments A₁ A₂ B₁ B₂ C₁ C₂ hresponse
    with ⟨hC, hmom⟩
  rcases moments_determine_visible_realization A₁ A₂ hA₁ hA₂ B₁ B₂ hmom
    with ⟨U, hU, hUnique⟩
  refine ⟨hC, U, ⟨hU.1, hU.2, ?_⟩, ?_⟩
  · exact intertwiner_preserves_parent_action _ _ _ _ C₁ C₂ U hU.1 hU.2 hC
  · intro V hV
    exact hUnique V ⟨hV.1, hV.2.1⟩

/-- The invisible bulk retains its own quadratic action. Reconstruction does
not silently identify it with zero or discard its physical energy. -/
theorem parent_action_visible_invisible_split
    (A : H₁ →L[ℝ] H₁) (hA : IsSelfAdjoint A)
    (B : Boundary → H₁) (C : Boundary → Boundary → ℝ)
    (y : visibleSubspace A B) (z : H₁) (hz : z ∈ (visibleSubspace A B)ᗮ)
    (q : Boundary) :
    boundedParentAction A B C ((y : H₁) + z) q =
      boundedParentAction (visibleOperator A B) (visibleMarking A B) C y q +
        ⟪z, A z⟫_ℝ / 2 := by
  have horth := (Submodule.mem_orthogonal _ _).mp hz
  have hyAz : ⟪(y : H₁), A z⟫_ℝ = 0 := by
    exact (hA.isSymmetric (y : H₁) z).symm.trans
      (horth _ (visible_invariant A B y y.property))
  have hzAy : ⟪z, A (y : H₁)⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact horth _ (visible_invariant A B y y.property)
  have hzB : ⟪z, B q⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact horth _ (marking_mem_visible A B q)
  change (⟪(y : H₁) + z, A ((y : H₁) + z)⟫_ℝ / 2 +
      ⟪(y : H₁) + z, B q⟫_ℝ + C q q / 2) =
    (⟪(y : H₁), A (y : H₁)⟫_ℝ / 2 + ⟪(y : H₁), B q⟫_ℝ + C q q / 2) +
      ⟪z, A z⟫_ℝ / 2
  simp only [map_add, inner_add_left, inner_add_right, hyAz, hzAy, hzB]
  ring

end
end P0EFTJanusFullSchurResponseReconstruction
end JanusFormal
