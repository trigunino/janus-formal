import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusResolventMomentIdentification
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedCyclicReconstruction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusUnboundedResolventDomainReconstruction

/-!
# Local response at a regular spectral parameter

For a real resolvent `R=(λI-A)⁻¹`, the response at `λ-t` is
`C + <Bq, R (I-tR)⁻¹ Br>`. Its Taylor coefficients of positive order determine
the moments of R of orders at least two. The constant boundary term hides the
first moment, so equality of all moments must not be assumed at this stage.
The expansion uses bounded R, without supposing the physical A bounded.
-/

namespace JanusFormal
namespace P0EFTJanusLocalResolventResponseReconstruction

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped InnerProductSpace
open P0EFTJanusCyclicMomentReconstruction
open P0EFTJanusShiftedCyclicReconstruction
open P0EFTJanusUnboundedResolventDomainReconstruction

variable {H H₁ H₂ Boundary : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]

def localSchurResponse (R : H →L[ℝ] H) (B : Boundary → H)
    (C : Boundary → Boundary → ℝ) (t : ℝ) (q r : Boundary) : ℝ :=
  C q r + ⟪B q, R (Ring.inverse (1 - t • R) (B r))⟫_ℝ

def shiftedMomentSeries (R : H →L[ℝ] H) (B : Boundary → H) (q r : Boundary) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (boundaryMoment R B (n + 1) q r)

def localSchurSeries (R : H →L[ℝ] H) (B : Boundary → H)
    (C : Boundary → Boundary → ℝ) (q r : Boundary) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  constFormalMultilinearSeries ℝ ℝ (C q r) + shiftedMomentSeries R B q r

theorem localSchurResponse_hasFPowerSeriesAt
    (R : H →L[ℝ] H) (B : Boundary → H)
    (C : Boundary → Boundary → ℝ) (q r : Boundary) :
    HasFPowerSeriesAt (fun t => localSchurResponse R B C t q r)
      (localSchurSeries R B C q r) 0 := by
  let L : (H →L[ℝ] H) →L[ℝ] ℝ :=
    ((innerSL ℝ (B q)).comp R).comp (ContinuousLinearMap.apply ℝ H (B r))
  have hseries : shiftedMomentSeries R B q r = L.compFormalMultilinearSeries
      (fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (R ^ n)) := by
    ext n
    simp [L, shiftedMomentSeries, boundaryMoment, pow_succ',
      ContinuousLinearMap.compFormalMultilinearSeries_apply, mul_apply_eq_comp]
  have hbulk : HasFPowerSeriesAt
      (fun t : ℝ => ⟪B q, R (Ring.inverse (1 - t • R) (B r))⟫_ℝ)
      (shiftedMomentSeries R B q r) 0 := by
    rw [hseries]
    exact (L.comp_hasFPowerSeriesOnBall
      (spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℝ R)).hasFPowerSeriesAt
  exact hasFPowerSeriesAt_const.add hbulk

/-- Positive Taylor orders recover exactly the unmasked tail of moments. -/
theorem local_response_germ_identifies_tail_moments
    (R₁ : H₁ →L[ℝ] H₁) (R₂ : H₂ →L[ℝ] H₂)
    (B₁ : Boundary → H₁) (B₂ : Boundary → H₂)
    (C₁ C₂ : Boundary → Boundary → ℝ)
    (hresponse : ∀ q r, ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      localSchurResponse R₁ B₁ C₁ t q r = localSchurResponse R₂ B₂ C₂ t q r) :
    ∀ n q r, boundaryMoment R₁ B₁ (n + 2) q r =
      boundaryMoment R₂ B₂ (n + 2) q r := by
  intro n q r
  have h₁ := localSchurResponse_hasFPowerSeriesAt R₁ B₁ C₁ q r
  have h₂ := localSchurResponse_hasFPowerSeriesAt R₂ B₂ C₂ q r
  have heq := (h₁.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    h₂.continuousAt).1 (hresponse q r)
  have hseries := h₁.eq_formalMultilinearSeries_of_eventually h₂ heq
  have hn := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ =>
    p (n + 1) (fun _ => 1)) hseries
  simpa [localSchurSeries, shiftedMomentSeries, Nat.add_assoc] using hn

omit [CompleteSpace H] in
theorem localSchurResponse_at_zero (R : H →L[ℝ] H) (B : Boundary → H)
    (C : Boundary → Boundary → ℝ) (q r : Boundary) :
    localSchurResponse R B C 0 q r = C q r + boundaryMoment R B 1 q r := by
  simp [localSchurResponse, boundaryMoment]

/-- The missing first moment and the independent boundary term are recovered
after reconstructing the injective cyclic resolvent. -/
theorem local_response_reconstructs_resolvent
    (R₁ : H₁ →L[ℝ] H₁) (R₂ : H₂ →L[ℝ] H₂)
    (hR₁ : IsSelfAdjoint R₁) (hR₂ : IsSelfAdjoint R₂)
    (hinj₁ : Function.Injective R₁) (hinj₂ : Function.Injective R₂)
    (B₁ : Boundary → H₁) (B₂ : Boundary → H₂)
    (C₁ C₂ : Boundary → Boundary → ℝ)
    (hcyclic₁ : IsCyclic R₁ B₁) (hcyclic₂ : IsCyclic R₂ B₂)
    (hresponse : ∀ q r, ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      localSchurResponse R₁ B₁ C₁ t q r = localSchurResponse R₂ B₂ C₂ t q r) :
    (∀ q r, C₁ q r = C₂ q r) ∧
    ∃! U : H₁ ≃ₗᵢ[ℝ] H₂,
      (∀ q, U (B₁ q) = B₂ q) ∧ (∀ x, U (R₁ x) = R₂ (U x)) := by
  have htail := local_response_germ_identifies_tail_moments
    R₁ R₂ B₁ B₂ C₁ C₂ hresponse
  obtain ⟨U, hU, hUnique⟩ := tail_moments_determine_cyclic_realization
    R₁ R₂ hR₁ hR₂ hinj₁ hinj₂ B₁ B₂ hcyclic₁ hcyclic₂ htail
  refine ⟨?_, U, hU, hUnique⟩
  intro q r
  have h₁ := (localSchurResponse_hasFPowerSeriesAt R₁ B₁ C₁ q r).continuousAt
  have h₂ := (localSchurResponse_hasFPowerSeriesAt R₂ B₂ C₂ q r).continuousAt
  have hzero := ((h₁.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₂).1
    (hresponse q r)).eq_of_nhds
  rw [localSchurResponse_at_zero, localSchurResponse_at_zero,
    intertwiner_preserves_moments R₁ R₂ B₁ B₂ U hU.1 hU.2 1 q r] at hzero
  exact add_right_cancel hzero

/-- Even without cyclicity of the original bulk, all its boundary moments and
the direct boundary term are recovered. Invisible sectors remain unrestricted. -/
theorem local_response_identifies_direct_and_all_moments
    (R₁ : H₁ →L[ℝ] H₁) (R₂ : H₂ →L[ℝ] H₂)
    (hR₁ : IsSelfAdjoint R₁) (hR₂ : IsSelfAdjoint R₂)
    (hinj₁ : Function.Injective R₁) (hinj₂ : Function.Injective R₂)
    (B₁ : Boundary → H₁) (B₂ : Boundary → H₂)
    (C₁ C₂ : Boundary → Boundary → ℝ)
    (hresponse : ∀ q r, ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      localSchurResponse R₁ B₁ C₁ t q r = localSchurResponse R₂ B₂ C₂ t q r) :
    (∀ q r, C₁ q r = C₂ q r) ∧
    (∀ n q r, boundaryMoment R₁ B₁ n q r = boundaryMoment R₂ B₂ n q r) := by
  have hmom := tail_moments_determine_all_moments_without_cyclicity
    R₁ R₂ hR₁ hR₂ hinj₁ hinj₂ B₁ B₂
    (local_response_germ_identifies_tail_moments R₁ R₂ B₁ B₂ C₁ C₂ hresponse)
  refine ⟨?_, hmom⟩
  intro q r
  have h₁ := (localSchurResponse_hasFPowerSeriesAt R₁ B₁ C₁ q r).continuousAt
  have h₂ := (localSchurResponse_hasFPowerSeriesAt R₂ B₂ C₂ q r).continuousAt
  have hzero := ((h₁.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₂).1
    (hresponse q r)).eq_of_nhds
  rw [localSchurResponse_at_zero, localSchurResponse_at_zero, hmom] at hzero
  exact add_right_cancel hzero

/-- The spectral shifts used by the local expansion are genuine resolvents
on a neighborhood of the supplied regular parameter. -/
theorem local_shifts_eventually_regular (R : H →L[ℝ] H) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (1 - t • R) := by
  have hc : ContinuousAt (fun t : ℝ => 1 - t • R) 0 :=
    continuousAt_const.sub (continuousAt_id.smul continuousAt_const)
  exact hc (by simpa using (Units.isOpen.mem_nhds (isUnit_one : IsUnit (1 : H →L[ℝ] H))))

omit [CompleteSpace H] in
/-- The analytic response is exactly the response of the shifted unbounded
operator on its original domain. -/
theorem local_response_is_actual_shifted_resolvent
    {A : H →ₗ.[ℝ] H} {μ : ℝ} (rA : ResolventAt A μ)
    (B : Boundary → H) (C : Boundary → Boundary → ℝ)
    (t : ℝ) (ht : IsUnit (1 - t • rA.R)) (q r : Boundary) :
    localSchurResponse rA.R B C t q r =
      C q r + ⟪B q, (rA.shift t ht).R (B r)⟫_ℝ := rfl

/-- Local response identifies a cyclic, possibly unbounded symmetric parent,
including its actual domain. Only one real bounded resolvent is supplied;
neither the domain equivalence nor the intertwining of A is assumed. -/
theorem local_response_reconstructs_unbounded_parent
    (A₁ : H₁ →ₗ.[ℝ] H₁) (A₂ : H₂ →ₗ.[ℝ] H₂) (μ : ℝ)
    (r₁ : ResolventAt A₁ μ) (r₂ : ResolventAt A₂ μ)
    (hA₁ : A₁.IsFormalAdjoint A₁) (hA₂ : A₂.IsFormalAdjoint A₂)
    (B₁ : Boundary → H₁) (B₂ : Boundary → H₂)
    (C₁ C₂ : Boundary → Boundary → ℝ)
    (hcyclic₁ : IsCyclic r₁.R B₁) (hcyclic₂ : IsCyclic r₂.R B₂)
    (hresponse : ∀ q r, ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      localSchurResponse r₁.R B₁ C₁ t q r = localSchurResponse r₂.R B₂ C₂ t q r) :
    (∀ q r, C₁ q r = C₂ q r) ∧
    ∃! U : H₁ ≃ₗᵢ[ℝ] H₂,
      (∀ q, U (B₁ q) = B₂ q) ∧ (∀ x, U (r₁.R x) = r₂.R (U x)) ∧
      ∃ e : A₁.domain ≃ₗ[ℝ] A₂.domain,
        ∀ x, (e x : H₂) = U x ∧ U (A₁ x) = A₂ (e x) := by
  obtain ⟨hC, U, hU, hUnique⟩ := local_response_reconstructs_resolvent
    r₁.R r₂.R (r₁.isSymmetric hA₁).isSelfAdjoint (r₂.isSymmetric hA₂).isSelfAdjoint
    r₁.injective r₂.injective B₁ B₂ C₁ C₂ hcyclic₁ hcyclic₂ hresponse
  refine ⟨hC, U, ⟨hU.1, hU.2, r₁.domainEquiv r₂ U hU.2, ?_⟩, ?_⟩
  · intro x
    exact ⟨rfl, r₁.action_intertwining r₂ U hU.2 x⟩
  · intro V hV
    exact hUnique V ⟨hV.1, hV.2.1⟩

end
end P0EFTJanusLocalResolventResponseReconstruction
end JanusFormal
