import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NormalGraphResolvent4D

/-! A bounded positive encoding of the zero-frequency problem of the actual closed operator. -/
namespace JanusFormal.P0EFTJanusProgramPT12NormalResolventDefect4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12NormalGraphResolvent4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable (A : H →ₗ.[Real] H) (hClosed : A.IsClosed)

def normalDefect : H →L[Real] H := ContinuousLinearMap.id Real H - normalResolvent A hClosed

theorem normalDefect_selfAdjoint : IsSelfAdjoint (normalDefect A hClosed) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro x y
  have h := (normalResolvent_selfAdjoint A hClosed).isSymmetric x y
  change inner Real (x - normalResolvent A hClosed x) y = inner Real x (y - normalResolvent A hClosed y)
  simp only [inner_sub_left, inner_sub_right]
  exact congrArg (fun z => inner Real x y - z) h

theorem normalDefect_energy (f : H) :
    ‖normalDefect A hClosed f‖ ^ 2 + ‖normalResolventImage A hClosed f‖ ^ 2 =
      inner Real f (normalDefect A hClosed f) := by
  have h := normalResolvent_energy A hClosed f
  change ‖f - normalResolvent A hClosed f‖ ^ 2 + _ = inner Real f (f - normalResolvent A hClosed f)
  rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq]
  linarith

theorem normalDefect_nonnegative (f : H) : 0 ≤ inner Real f (normalDefect A hClosed f) := by
  rw [← normalDefect_energy]
  positivity

theorem normalDefect_norm_le (f : H) : ‖normalDefect A hClosed f‖ ≤ ‖f‖ := by
  have h := normalDefect_energy A hClosed f
  have hCS := real_inner_le_norm f (normalDefect A hClosed f)
  have h0 := norm_nonneg (normalDefect A hClosed f)
  have h1 := norm_nonneg f
  nlinarith [sq_nonneg ‖normalResolventImage A hClosed f‖]

theorem normalDefect_zero_iff (u : H) : normalDefect A hClosed u = 0 ↔ (u, 0) ∈ A.graph := by
  change u - normalResolvent A hClosed u = 0 ↔ _
  rw [sub_eq_zero, eq_comm, normalResolvent_fixed_iff_null]

def normalDefectKernelEquiv : LinearMap.ker A.toFun ≃ₗ[Real]
    LinearMap.ker (normalDefect A hClosed).toLinearMap where
  toFun u := ⟨u.val.val, (normalDefect_zero_iff A hClosed u.val.val).mpr (by
    have h := A.mem_graph u.val
    have hz : A u.val = 0 := u.property
    rwa [hz] at h)⟩
  invFun u := by
    have h := (normalDefect_zero_iff A hClosed u.val).mp u.property
    exact ⟨⟨u.val, LinearPMap.mem_domain_of_mem_graph h⟩,
      A.mem_graph_snd_inj (A.mem_graph _) h rfl⟩
  left_inv _ := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

/-- This identity retains the unbounded domain on its left-hand input. -/
theorem normalDefect_on_domain (u : A.domain) :
    normalDefect A hClosed u.val = (normalResolventImage A hClosed).adjoint (A u) := by
  apply ext_inner_right Real
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left]
  have h := normalResolvent_weak A hClosed f u
  have hSym := (normalResolvent_selfAdjoint A hClosed).isSymmetric u.val f
  change inner Real (normalResolvent A hClosed u.val) f = inner Real u.val (normalResolvent A hClosed f) at hSym
  have hComm1 := real_inner_comm f u.val
  have hComm2 := real_inner_comm (normalResolvent A hClosed f) u.val
  have hComm3 := real_inner_comm (normalResolventImage A hClosed f) (A u)
  change inner Real (u.val - normalResolvent A hClosed u.val) f = _
  simp only [inner_sub_left] at h ⊢
  linarith

theorem normalDefect_domain_bound (u : A.domain) :
    2 * ‖normalDefect A hClosed u.val‖ ≤ ‖A u‖ := by
  have hNorm : ‖normalResolventImage A hClosed‖ ≤ (1 / 2 : Real) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro f
    have h := normalResolventImage_norm_le_half A hClosed f
    linarith
  rw [normalDefect_on_domain]
  have h := (normalResolventImage A hClosed).adjoint.le_opNorm (A u)
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  have hn := norm_nonneg (A u)
  nlinarith

theorem normalDefect_range_iff (hDense : Dense (A.domain : Set H)) (y : H) :
    y ∈ LinearMap.range (normalDefect A hClosed).toLinearMap ↔
      ∃ (u : A.domain) (hImage : A u ∈ A.adjoint.domain), A.adjoint ⟨A u, hImage⟩ = y := by
  constructor
  · rintro ⟨f, rfl⟩
    let u : A.domain := ⟨normalResolvent A hClosed f, normalResolvent_mem_domain A hClosed f⟩
    have hImage : A u ∈ A.adjoint.domain := by
      rw [normalResolvent_apply]
      exact normalResolventImage_mem_adjoint_domain A hClosed f
    refine ⟨u, hImage, ?_⟩
    have h := normalResolvent_equation A hClosed hDense f
    change A.adjoint ⟨A u, hImage⟩ = f - normalResolvent A hClosed f
    simpa only [u, normalResolvent_apply] using (show
      A.adjoint ⟨normalResolventImage A hClosed f, normalResolventImage_mem_adjoint_domain A hClosed f⟩ =
        f - normalResolvent A hClosed f from eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h))
  · rintro ⟨u, hImage, hy⟩
    have hu := normalResolvent_unique A hClosed hDense (u.val + y) u hImage (by rw [hy])
    refine ⟨u.val + y, ?_⟩
    change u.val + y - normalResolvent A hClosed (u.val + y) = y
    rw [← hu]
    abel

end
end JanusFormal.P0EFTJanusProgramPT12NormalResolventDefect4D
