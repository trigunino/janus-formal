import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-! Sum/difference ghost coordinates retain the skew-adjoint defect. -/
namespace JanusFormal.P0EFTJanusProgramPT12GhostRotationDefect4D

set_option autoImplicit false
noncomputable section

variable {E V : Type*} [AddCommGroup E] [Module Real E]
  [NormedAddCommGroup V] [InnerProductSpace Real V]

def fpSymmetricPairing (inclusion operator : E →ₗ[Real] V) (x y : E) : Real :=
  (inner Real (inclusion x) (operator y) + inner Real (operator x) (inclusion y)) / 2

def fpPairingDefect (inclusion operator : E →ₗ[Real] V) (x y : E) : Real :=
  inner Real (operator x) (inclusion y) - inner Real (inclusion x) (operator y)

def ghostCrossPairing (inclusion operator : E →ₗ[Real] V) (a c b d : E) : Real :=
  inner Real (inclusion a) (operator d) + inner Real (operator c) (inclusion b)

/-- The mixed terms disappear only after the actual FP symmetry defect vanishes. -/
theorem ghostCrossPairing_signed_coordinates (inclusion operator : E →ₗ[Real] V)
    (u v x y : E) :
    ghostCrossPairing inclusion operator
        ((1 / 2 : Real) • (u + v)) ((1 / 2 : Real) • (u - v))
        ((1 / 2 : Real) • (x + y)) ((1 / 2 : Real) • (x - y)) =
      (fpSymmetricPairing inclusion operator u x -
        fpSymmetricPairing inclusion operator v y) / 2 +
      (fpPairingDefect inclusion operator u y +
        fpPairingDefect inclusion operator x v) / 4 := by
  simp only [ghostCrossPairing, fpSymmetricPairing, fpPairingDefect,
    map_smul, map_add, map_sub, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [real_inner_comm (operator v) (inclusion x),
    real_inner_comm (inclusion v) (operator x)]
  ring

/-- A plus/minus off-diagonal test reads exactly one quarter of the defect. -/
theorem ghostCrossPairing_mixed_signed (inclusion operator : E →ₗ[Real] V) (u v : E) :
    ghostCrossPairing inclusion operator
        ((1 / 2 : Real) • u) ((1 / 2 : Real) • u)
        ((1 / 2 : Real) • v) (-(1 / 2 : Real) • v) =
      fpPairingDefect inclusion operator u v / 4 := by
  simp only [ghostCrossPairing, fpPairingDefect, map_smul,
    real_inner_smul_left, real_inner_smul_right]
  ring

theorem ghostCrossPairing_mixed_signed_zero_iff
    (inclusion operator : E →ₗ[Real] V) (u v : E) :
    ghostCrossPairing inclusion operator
        ((1 / 2 : Real) • u) ((1 / 2 : Real) • u)
        ((1 / 2 : Real) • v) (-(1 / 2 : Real) • v) = 0 ↔
      inner Real (operator u) (inclusion v) = inner Real (inclusion u) (operator v) := by
  rw [ghostCrossPairing_mixed_signed, div_eq_zero_iff]
  simp [fpPairingDefect, sub_eq_zero]

end
end JanusFormal.P0EFTJanusProgramPT12GhostRotationDefect4D
