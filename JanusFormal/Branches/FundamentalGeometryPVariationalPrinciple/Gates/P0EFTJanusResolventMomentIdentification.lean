import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCyclicMomentReconstruction

/-!
# Resolvent response identifies cyclic bounded realizations

The analytic germ of the actual normalized resolvent determines all boundary
moments by uniqueness of its Neumann series. Together with cyclic reconstruction,
this identifies a bounded self-adjoint realization up to its unique marked
Hilbert-space isometry. Neither moments nor an isometry are assumed as input.
-/

namespace JanusFormal
namespace P0EFTJanusResolventMomentIdentification

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace Topology
open Filter
open P0EFTJanusCyclicMomentReconstruction

variable {H H₁ H₂ Boundary : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]

/-- The resolvent normalized at infinite spectral parameter, with `t = 1/z`.
Ring inverse agrees with the genuine inverse throughout its neighborhood of zero. -/
def normalizedResponse (A : H →L[ℝ] H) (B : Boundary → H)
    (t : ℝ) (q r : Boundary) : ℝ :=
  ⟪B q, (Ring.inverse (1 - t • A)) (B r)⟫_ℝ

/-- The Neumann coefficients are exactly the measured boundary moments. -/
def momentSeries (A : H →L[ℝ] H) (B : Boundary → H) (q r : Boundary) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (boundaryMoment A B n q r)

/-- An explicit convergent Neumann expansion, valid on the operator-norm disk. -/
theorem normalizedResponse_hasFPowerSeriesOnBall
    (A : H →L[ℝ] H) (B : Boundary → H) (q r : Boundary) :
    HasFPowerSeriesOnBall (fun t => normalizedResponse A B t q r)
      (momentSeries A B q r) 0 ‖A‖₊⁻¹ := by
  let L : (H →L[ℝ] H) →L[ℝ] ℝ :=
    (innerSL ℝ (B q)).comp (ContinuousLinearMap.apply ℝ H (B r))
  have hseries : momentSeries A B q r = L.compFormalMultilinearSeries
      (fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (A ^ n)) := by
    ext n
    simp [L, momentSeries, boundaryMoment,
      ContinuousLinearMap.compFormalMultilinearSeries_apply]
  rw [hseries]
  exact L.comp_hasFPowerSeriesOnBall
    (spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℝ A)

theorem normalizedResponse_hasFPowerSeriesAt
    (A : H →L[ℝ] H) (B : Boundary → H) (q r : Boundary) :
    HasFPowerSeriesAt (fun t => normalizedResponse A B t q r)
      (momentSeries A B q r) 0 :=
  (normalizedResponse_hasFPowerSeriesOnBall A B q r).hasFPowerSeriesAt

theorem normalizedResponse_continuousAt_zero
    (A : H →L[ℝ] H) (B : Boundary → H) (q r : Boundary) :
    ContinuousAt (fun t => normalizedResponse A B t q r) 0 :=
  (normalizedResponse_hasFPowerSeriesAt A B q r).continuousAt

/-- Equality on any neighborhood of zero recovers every boundary moment. -/
theorem response_eq_eventually_implies_moments
    (A₁ : H₁ →L[ℝ] H₁) (A₂ : H₂ →L[ℝ] H₂)
    (B₁ : Boundary → H₁) (B₂ : Boundary → H₂)
    (hresponse : ∀ q r, ∀ᶠ t in 𝓝 (0 : ℝ),
      normalizedResponse A₁ B₁ t q r = normalizedResponse A₂ B₂ t q r) :
    ∀ n q r, boundaryMoment A₁ B₁ n q r = boundaryMoment A₂ B₂ n q r := by
  intro n q r
  have hseries := (normalizedResponse_hasFPowerSeriesAt A₁ B₁ q r).eq_formalMultilinearSeries_of_eventually
      (normalizedResponse_hasFPowerSeriesAt A₂ B₂ q r) (hresponse q r)
  have heq := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p n (fun _ => 1)) hseries
  simpa [momentSeries] using heq

/-- Conversely, all moments determine the resolvent response near zero. -/
theorem moments_imply_response_eq_eventually
    (A₁ : H₁ →L[ℝ] H₁) (A₂ : H₂ →L[ℝ] H₂)
    (B₁ : Boundary → H₁) (B₂ : Boundary → H₂)
    (hmom : ∀ n q r, boundaryMoment A₁ B₁ n q r = boundaryMoment A₂ B₂ n q r) :
    ∀ q r, ∀ᶠ t in 𝓝 (0 : ℝ),
      normalizedResponse A₁ B₁ t q r = normalizedResponse A₂ B₂ t q r := by
  intro q r
  have hseries : momentSeries A₁ B₁ q r = momentSeries A₂ B₂ q r := by
    funext n
    simp only [momentSeries, hmom]
  filter_upwards [(normalizedResponse_hasFPowerSeriesAt A₁ B₁ q r).eventually_hasSum,
    (normalizedResponse_hasFPowerSeriesAt A₂ B₂ q r).eventually_hasSum] with t h₁ h₂
  rw [hseries] at h₁
  simpa only [zero_add] using h₁.unique h₂

/-- Actual resolvent-response data reconstruct the full cyclic realization. -/
theorem response_determine_cyclic_realization
    (A₁ : H₁ →L[ℝ] H₁) (A₂ : H₂ →L[ℝ] H₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂)
    (B₁ : Boundary → H₁) (B₂ : Boundary → H₂)
    (hcyclic₁ : IsCyclic A₁ B₁) (hcyclic₂ : IsCyclic A₂ B₂)
    (hresponse : ∀ q r, ∀ᶠ t in 𝓝 (0 : ℝ),
      normalizedResponse A₁ B₁ t q r = normalizedResponse A₂ B₂ t q r) :
    ∃! U : H₁ ≃ₗᵢ[ℝ] H₂,
      (∀ q, U (B₁ q) = B₂ q) ∧ (∀ x, U (A₁ x) = A₂ (U x)) :=
  moments_determine_cyclic_realization A₁ A₂ hA₁ hA₂ B₁ B₂ hcyclic₁ hcyclic₂
    (response_eq_eventually_implies_moments A₁ A₂ B₁ B₂ hresponse)

/-- Complete classification by the germ of the measured resolvent response. -/
theorem cyclic_equivalence_iff_response
    (A₁ : H₁ →L[ℝ] H₁) (A₂ : H₂ →L[ℝ] H₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂)
    (B₁ : Boundary → H₁) (B₂ : Boundary → H₂)
    (hcyclic₁ : IsCyclic A₁ B₁) (hcyclic₂ : IsCyclic A₂ B₂) :
    (∃ U : H₁ ≃ₗᵢ[ℝ] H₂,
      (∀ q, U (B₁ q) = B₂ q) ∧ (∀ x, U (A₁ x) = A₂ (U x))) ↔
      ∀ q r, ∀ᶠ t in 𝓝 (0 : ℝ),
        normalizedResponse A₁ B₁ t q r = normalizedResponse A₂ B₂ t q r := by
  rw [cyclic_equivalence_iff_moments A₁ A₂ hA₁ hA₂ B₁ B₂ hcyclic₁ hcyclic₂]
  exact ⟨moments_imply_response_eq_eventually A₁ A₂ B₁ B₂,
    response_eq_eventually_implies_moments A₁ A₂ B₁ B₂⟩

end
end P0EFTJanusResolventMomentIdentification
end JanusFormal
