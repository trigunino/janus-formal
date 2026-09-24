import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProjectedGraphCore4D

/-! The normal resolvent (1 + A† A)⁻¹ constructed from the actual closed graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12NormalGraphResolvent4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12ProjectedGraphCore4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable (A : H →ₗ.[Real] H) (hClosed : A.IsClosed)

def normalGraphSolution : H →L[Real] H × H :=
  (closedGraphProjection A hClosed).comp
    ((WithLp.prodContinuousLinearEquiv 2 Real H H).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl Real H H))

def normalResolvent : H →L[Real] H :=
  (ContinuousLinearMap.fst Real H H).comp (normalGraphSolution A hClosed)

def normalResolventImage : H →L[Real] H :=
  (ContinuousLinearMap.snd Real H H).comp (normalGraphSolution A hClosed)

theorem normalResolvent_graph (f : H) :
    (normalResolvent A hClosed f, normalResolventImage A hClosed f) ∈ A.graph :=
  closedGraphProjection_mem A hClosed (WithLp.toLp 2 (f, 0))

theorem normalResolvent_mem_domain (f : H) : normalResolvent A hClosed f ∈ A.domain :=
  LinearPMap.mem_domain_of_mem_graph (normalResolvent_graph A hClosed f)

theorem normalResolvent_apply (f : H) :
    A ⟨normalResolvent A hClosed f, normalResolvent_mem_domain A hClosed f⟩ =
      normalResolventImage A hClosed f :=
  A.mem_graph_snd_inj (A.mem_graph _) (normalResolvent_graph A hClosed f) rfl

theorem normalResolvent_weak (f : H) (u : A.domain) :
    inner Real (f - normalResolvent A hClosed f) u.val =
      inner Real (normalResolventImage A hClosed f) (A u) := by
  have h := closedGraphProjection_orthogonality A hClosed
    (WithLp.toLp 2 (f, 0)) (u.val, A u) (A.mem_graph u)
  change inner Real (f - normalResolvent A hClosed f) u.val +
    inner Real (0 - normalResolventImage A hClosed f) (A u) = 0 at h
  simpa only [zero_sub, inner_neg_left, ← sub_eq_add_neg, sub_eq_zero] using h

theorem normalResolvent_energy (f : H) :
    ‖normalResolvent A hClosed f‖ ^ 2 + ‖normalResolventImage A hClosed f‖ ^ 2 =
      inner Real f (normalResolvent A hClosed f) := by
  have h := normalResolvent_weak A hClosed f
    ⟨normalResolvent A hClosed f, normalResolvent_mem_domain A hClosed f⟩
  rw [normalResolvent_apply] at h
  simp only [inner_sub_left, real_inner_self_eq_norm_sq] at h
  linarith

/-- Uniform control of the solution, proved without a gap for A. -/
theorem normalResolvent_norm_le (f : H) : ‖normalResolvent A hClosed f‖ ≤ ‖f‖ := by
  have h := normalResolvent_energy A hClosed f
  have hCS := real_inner_le_norm f (normalResolvent A hClosed f)
  have h0 := norm_nonneg (normalResolvent A hClosed f)
  have h1 := norm_nonneg f
  nlinarith [sq_nonneg ‖normalResolventImage A hClosed f‖]

theorem normalResolventImage_norm_le_half (f : H) :
    2 * ‖normalResolventImage A hClosed f‖ ≤ ‖f‖ := by
  have h := normalResolvent_energy A hClosed f
  have hCS := real_inner_le_norm f (normalResolvent A hClosed f)
  have h0 := norm_nonneg (normalResolventImage A hClosed f)
  have h1 := norm_nonneg f
  nlinarith [sq_nonneg (2 * ‖normalResolvent A hClosed f‖ - ‖f‖)]

theorem normalResolvent_opNorm_le : ‖normalResolvent A hClosed‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using normalResolvent_norm_le A hClosed f

theorem normalResolvent_nonnegative (f : H) :
    0 ≤ inner Real f (normalResolvent A hClosed f) := by
  rw [← normalResolvent_energy]
  positivity

theorem normalResolvent_selfAdjoint : IsSelfAdjoint (normalResolvent A hClosed) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro f g
  have h1 := normalResolvent_weak A hClosed f
    ⟨normalResolvent A hClosed g, normalResolvent_mem_domain A hClosed g⟩
  have h2 := normalResolvent_weak A hClosed g
    ⟨normalResolvent A hClosed f, normalResolvent_mem_domain A hClosed f⟩
  rw [normalResolvent_apply, inner_sub_left] at h1 h2
  have hc1 := real_inner_comm g (normalResolvent A hClosed f)
  have hc2 := real_inner_comm (normalResolvent A hClosed g) (normalResolvent A hClosed f)
  have hc3 := real_inner_comm (normalResolventImage A hClosed g) (normalResolventImage A hClosed f)
  change inner Real (normalResolvent A hClosed f) g = inner Real f (normalResolvent A hClosed g)
  linarith

theorem normalResolventImage_mem_adjoint_domain (f : H) :
    normalResolventImage A hClosed f ∈ A.adjoint.domain :=
  A.mem_adjoint_domain_of_exists _ ⟨f - normalResolvent A hClosed f, normalResolvent_weak A hClosed f⟩

theorem normalResolvent_equation (hDense : Dense (A.domain : Set H)) (f : H) :
    normalResolvent A hClosed f +
      A.adjoint ⟨normalResolventImage A hClosed f, normalResolventImage_mem_adjoint_domain A hClosed f⟩ = f := by
  rw [LinearPMap.adjoint_apply_eq hDense _ (normalResolvent_weak A hClosed f)]
  exact add_sub_cancel _ _

theorem normalResolvent_unique (hDense : Dense (A.domain : Set H)) (f : H)
    (u : A.domain) (hImage : A u ∈ A.adjoint.domain)
    (hEquation : u.val + A.adjoint ⟨A u, hImage⟩ = f) :
    u.val = normalResolvent A hClosed f := by
  let v : A.domain := ⟨normalResolvent A hClosed f, normalResolvent_mem_domain A hClosed f⟩
  have hu : A.adjoint ⟨A u, hImage⟩ = f - u.val := by rw [← hEquation]; abel
  have h1 := LinearPMap.adjoint_isFormalAdjoint hDense ⟨A u, hImage⟩ (u - v)
  rw [hu] at h1
  have h2 := normalResolvent_weak A hClosed f (u - v)
  have hDiff : A (u - v) = A u - normalResolventImage A hClosed f := by
    change A.toFun (u - v) = _
    rw [map_sub]
    exact congrArg (fun y => A u - y) (normalResolvent_apply A hClosed f)
  have hZero : inner Real ((u - v : A.domain) : H) ((u - v : A.domain) : H) +
      inner Real (A u - normalResolventImage A hClosed f) (A (u - v)) = 0 := by
    change inner Real (u.val - normalResolvent A hClosed f) ((u - v : A.domain) : H) + _ = 0
    simp only [inner_sub_left] at h1 h2 ⊢
    linarith
  rw [← hDiff, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hZero
  have hz : ((u - v : A.domain) : H) = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖A (u - v)‖])
  exact sub_eq_zero.mp hz

/-- The auxiliary resolvent retains every true zero mode of A. -/
theorem normalResolvent_fixed_of_null (u : H) (hNull : (u, 0) ∈ A.graph) :
    normalResolvent A hClosed u = u :=
  congrArg Prod.fst (closedGraphProjection_fixed A hClosed (u, 0) hNull)

theorem normalResolvent_fixed_iff_null (u : H) :
    normalResolvent A hClosed u = u ↔ (u, 0) ∈ A.graph := by
  constructor
  · intro h
    have hEnergy := normalResolvent_energy A hClosed u
    rw [h, real_inner_self_eq_norm_sq] at hEnergy
    have hz : normalResolventImage A hClosed u = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖u‖])
    simpa only [h, hz] using normalResolvent_graph A hClosed u
  · exact normalResolvent_fixed_of_null A hClosed u

end
end JanusFormal.P0EFTJanusProgramPT12NormalGraphResolvent4D
