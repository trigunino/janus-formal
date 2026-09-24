import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NormalResolventDefect4D
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-! Bounded approximations to the unshifted inverse, retaining the true operator graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12ResolventInverseApproximation4D
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open P0EFTJanusProgramPT12NormalGraphResolvent4D
open P0EFTJanusProgramPT12NormalResolventDefect4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable (A : H →ₗ.[Real] H) (hClosed : A.IsClosed)

def resolventInverseStep : Nat → H →L[Real] H
  | 0 => (normalResolventImage A hClosed).adjoint
  | n + 1 => (normalResolvent A hClosed).comp (resolventInverseStep n) +
      (normalResolventImage A hClosed).adjoint

def resolventInverseAverage (n : Nat) : H →L[Real] H :=
  ((n + 1 : Nat) : Real)⁻¹ • ∑ k ∈ Finset.range (n + 1), resolventInverseStep A hClosed k

def resolventMean (n : Nat) (u : H) : H :=
  birkhoffAverage Real (normalResolvent A hClosed) id (n + 1) u

theorem resolventInverseStep_on_domain (n : Nat) (u : A.domain) :
    resolventInverseStep A hClosed n (A u) =
      u.val - (normalResolvent A hClosed)^[n + 1] u.val := by
  have h := (normalDefect_on_domain A hClosed u).symm
  change (normalResolventImage A hClosed).adjoint (A u) =
    u.val - normalResolvent A hClosed u.val at h
  induction n with
  | zero => simpa [resolventInverseStep] using h
  | succ n ih =>
    simp only [resolventInverseStep, add_apply,
      ContinuousLinearMap.comp_apply, ih, map_sub, h, Function.iterate_succ_apply']
    abel

theorem resolventInverseAverage_on_domain (n : Nat) (u : A.domain) :
    resolventInverseAverage A hClosed n (A u) =
      u.val - normalResolvent A hClosed (resolventMean A hClosed n u.val) := by
  simp only [resolventInverseAverage, smul_apply,
    sum_apply, resolventInverseStep_on_domain,
    Function.iterate_succ_apply', Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, resolventMean, birkhoffAverage, birkhoffSum, id_eq,
    map_smul, map_sum, smul_sub]
  rw [← Nat.cast_smul_eq_nsmul Real, smul_smul,
    inv_mul_cancel₀ (by positivity : ((n + 1 : Nat) : Real) ≠ 0), one_smul]

theorem resolventInverseAverage_graph (n : Nat) (u : A.domain) :
    (resolventInverseAverage A hClosed n (A u),
      A u - normalResolventImage A hClosed (resolventMean A hClosed n u.val)) ∈ A.graph := by
  rw [resolventInverseAverage_on_domain]
  exact A.graph.sub_mem (A.mem_graph u)
    (normalResolvent_graph A hClosed (resolventMean A hClosed n u.val))

end
end JanusFormal.P0EFTJanusProgramPT12ResolventInverseApproximation4D
