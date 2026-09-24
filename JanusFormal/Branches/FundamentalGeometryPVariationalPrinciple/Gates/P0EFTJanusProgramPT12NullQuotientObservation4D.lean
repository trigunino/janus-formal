import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapQuotient4D

/-! Quantitative observations of a closed null space and its orthogonal quotient. -/
namespace JanusFormal.P0EFTJanusProgramPT12NullQuotientObservation4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable (K : Submodule Real H) [IsClosed (K : Set H)]

theorem quotientLift_norm (u : H ⧸ K) : ‖quotientLift K u‖ = ‖u‖ :=
  K.quotientEquivOrthogonal.norm_map u

theorem quotientLift_mk_eq_sub_projection (u : H) :
    quotientLift K (K.mkQ u) = u - K.starProjection u := by
  have hMk : K.mkQ (u - K.starProjection u) = K.mkQ u := by
    rw [map_sub, show K.mkQ (K.starProjection u) = 0 from
      (Submodule.Quotient.mk_eq_zero K).mpr (K.starProjection_apply_mem u), sub_zero]
  rw [← hMk]
  exact quotientLift_mk K _ (K.sub_starProjection_mem_orthogonal u)

theorem norm_sq_eq_quotient_add_observation (u : H) :
    ‖u‖ ^ 2 = ‖K.mkQ u‖ ^ 2 + ‖K.orthogonalProjectionOnto u‖ ^ 2 := by
  rw [← quotientLift_norm K (K.mkQ u), quotientLift_mk_eq_sub_projection]
  change ‖u‖ ^ 2 = ‖u - K.starProjection u‖ ^ 2 + ‖K.starProjection u‖ ^ 2
  rw [add_comm]
  simpa only [Submodule.starProjection_orthogonal_val] using K.norm_sq_eq_add_norm_sq_starProjection u

theorem norm_le_quotient_add_observation (u : H) :
    ‖u‖ ≤ ‖K.mkQ u‖ + ‖K.orthogonalProjectionOnto u‖ := by
  rw [← quotientLift_norm K (K.mkQ u), quotientLift_mk_eq_sub_projection]
  calc
    ‖u‖ = ‖(u - K.starProjection u) + K.starProjection u‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _

theorem observation_quotientLift_zero (u : H ⧸ K) :
    K.orthogonalProjectionOnto (quotientLift K u) = 0 :=
  K.orthogonalProjectionOnto_eq_zero_iff.mpr (K.quotientEquivOrthogonal u).property

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]

/-- Keep the known null observation and append any observations of the residual quotient. -/
def liftedObservation (observation : (H ⧸ K) →L[Real] F) : H →L[Real] K × F :=
  K.orthogonalProjectionOnto.prod (observation.comp K.mkQL)

theorem liftedObservation_quotientLift (observation : (H ⧸ K) →L[Real] F) (u : H ⧸ K) :
    liftedObservation K observation (quotientLift K u) = (0, observation u) := by
  change (K.orthogonalProjectionOnto (quotientLift K u), observation (K.mkQ (quotientLift K u))) = _
  rw [observation_quotientLift_zero, mk_quotientLift]

theorem liftedObservation_norm_le (observation : (H ⧸ K) →L[Real] F) (u : H) :
    ‖liftedObservation K observation u‖ ≤ max 1 ‖observation‖ * ‖u‖ := by
  change max ‖K.orthogonalProjectionOnto u‖ ‖observation (K.mkQ u)‖ ≤ _
  apply max_le
  · exact (K.norm_orthogonalProjectionOnto_apply_le u).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 ‖observation‖) (norm_nonneg u))
  · calc
      ‖observation (K.mkQ u)‖ ≤ ‖observation‖ * ‖K.mkQ u‖ := observation.le_opNorm _
      _ ≤ ‖observation‖ * ‖u‖ := mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le K u) observation.opNorm_nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right 1 ‖observation‖) (norm_nonneg u)

theorem quotient_estimate_lifts (A : H →ₗ.[Real] H)
    (hSym : A.IsFormalAdjoint A) (hNull : ∀ u ∈ K, (u, (0 : H)) ∈ A.graph)
    (observation : (H ⧸ K) →L[Real] F) (C : NNReal)
    (hEstimate : ∀ u : (quotientPMap A K).domain,
      ‖u.val‖ ≤ C * (‖quotientPMap A K u‖ + ‖observation u.val‖))
    (u : A.domain) :
    ‖u.val‖ ≤ (C + 1 : NNReal) * (‖A u‖ + ‖liftedObservation K observation u.val‖) := by
  have hGraph := quotientPMap_graph_project A K hSym hNull u
  let q : (quotientPMap A K).domain := ⟨K.mkQ u.val, LinearPMap.mem_domain_of_mem_graph hGraph⟩
  have hApply : quotientPMap A K q = K.mkQ (A u) :=
    (quotientPMap A K).mem_graph_snd_inj ((quotientPMap A K).mem_graph q) hGraph rfl
  have h := hEstimate q
  rw [hApply] at h
  have hNorm := Submodule.Quotient.norm_mk_le K (A u)
  change ‖K.mkQ (A u)‖ ≤ ‖A u‖ at hNorm
  have hSplit := norm_le_quotient_add_observation K u.val
  have hFirst : ‖K.orthogonalProjectionOnto u.val‖ ≤ ‖liftedObservation K observation u.val‖ :=
    le_max_left _ _
  have hSecond : ‖observation (K.mkQ u.val)‖ ≤ ‖liftedObservation K observation u.val‖ :=
    le_max_right _ _
  change ‖K.mkQ u.val‖ ≤ (C : Real) * (‖K.mkQ (A u)‖ + ‖observation (K.mkQ u.val)‖) at h
  simp only [NNReal.coe_add, NNReal.coe_one]
  have hC := C.coe_nonneg
  have hA := norm_nonneg (A u)
  nlinarith

end
end JanusFormal.P0EFTJanusProgramPT12NullQuotientObservation4D
