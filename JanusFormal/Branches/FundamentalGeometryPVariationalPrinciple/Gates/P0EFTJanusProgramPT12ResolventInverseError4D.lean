import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ResolventInverseApproximation4D

/-! A quantitative residual estimate, without replacing a preimage norm by the RHS norm. -/
namespace JanusFormal.P0EFTJanusProgramPT12ResolventInverseError4D
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open P0EFTJanusProgramPT12NormalGraphResolvent4D
open P0EFTJanusProgramPT12ResolventInverseApproximation4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable (A : H →ₗ.[Real] H) (hClosed : A.IsClosed)

theorem normalResolvent_energy_decay (u : H) :
    ‖normalResolvent A hClosed u‖ ^ 2 + 2 * ‖normalResolventImage A hClosed u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  have h := normalResolvent_energy A hClosed u
  have hCS := real_inner_le_norm u (normalResolvent A hClosed u)
  nlinarith [sq_nonneg (‖u‖ - ‖normalResolvent A hClosed u‖)]

theorem normalResolvent_iterate_energy (n : Nat) (u : H) :
    ‖(normalResolvent A hClosed)^[n] u‖ ^ 2 +
      2 * ∑ k ∈ Finset.range n, ‖normalResolventImage A hClosed ((normalResolvent A hClosed)^[k] u)‖ ^ 2 ≤
        ‖u‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := normalResolvent_energy_decay A hClosed ((normalResolvent A hClosed)^[n] u)
    rw [Finset.sum_range_succ, Function.iterate_succ_apply']
    linarith

omit [InnerProductSpace Real H] [CompleteSpace H] in
private theorem norm_sum_sq_le_card {ι : Type*} (s : Finset ι) (v : ι → H) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ (s.card : Real) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have hTriangle := norm_sum_le s v
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : Real)) (fun i => ‖v i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  have hNorm := norm_nonneg (∑ i ∈ s, v i)
  nlinarith

theorem resolventMean_residual_bound (n : Nat) (u : H) :
    2 * ((n + 1 : Nat) : Real) *
      ‖normalResolventImage A hClosed (resolventMean A hClosed n u)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  have hN : 0 < ((n + 1 : Nat) : Real) := by positivity
  have hScale : ((n + 1 : Nat) : Real) •
      normalResolventImage A hClosed (resolventMean A hClosed n u) =
      ∑ k ∈ Finset.range (n + 1), normalResolventImage A hClosed ((normalResolvent A hClosed)^[k] u) := by
    simp only [resolventMean, birkhoffAverage, birkhoffSum, id_eq, map_smul, map_sum, smul_smul]
    rw [mul_inv_cancel₀ hN.ne', one_smul]
  have hNorm := congrArg (fun v : H => ‖v‖ ^ 2) hScale
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hN, mul_pow] at hNorm
  have hCS := norm_sum_sq_le_card (Finset.range (n + 1))
    (fun k => normalResolventImage A hClosed ((normalResolvent A hClosed)^[k] u))
  rw [Finset.card_range] at hCS
  have hEnergy := normalResolvent_iterate_energy A hClosed (n + 1) u
  have hSum : 2 * ∑ k ∈ Finset.range (n + 1),
      ‖normalResolventImage A hClosed ((normalResolvent A hClosed)^[k] u)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(normalResolvent A hClosed)^[n + 1] u‖]
  apply (mul_le_mul_iff_right₀ hN).mp
  nlinarith [mul_le_mul_of_nonneg_left hSum hN.le]

/-- The error is controlled by a genuine preimage; this is not a bounded-inverse estimate. -/
theorem resolventInverseAverage_error_bound (n : Nat) (u : A.domain) :
    ∃ v : A.domain, v.val = resolventInverseAverage A hClosed n (A u) ∧
      2 * ((n + 1 : Nat) : Real) * ‖A v - A u‖ ^ 2 ≤ ‖u.val‖ ^ 2 := by
  have hGraph := resolventInverseAverage_graph A hClosed n u
  let v : A.domain := ⟨_, LinearPMap.mem_domain_of_mem_graph hGraph⟩
  refine ⟨v, rfl, ?_⟩
  have hValue := A.mem_graph_snd_inj (A.mem_graph v) hGraph rfl
  have hError : A v - A u = -normalResolventImage A hClosed (resolventMean A hClosed n u.val) := by
    rw [hValue]
    abel
  rw [hError, norm_neg]
  exact resolventMean_residual_bound A hClosed n u.val

end
end JanusFormal.P0EFTJanusProgramPT12ResolventInverseError4D
