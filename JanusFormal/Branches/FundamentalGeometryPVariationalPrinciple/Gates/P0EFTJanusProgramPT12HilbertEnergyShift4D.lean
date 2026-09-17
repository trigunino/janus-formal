import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Tactic.Linarith

/-!
# Shifted weak solutions for a Hilbert energy embedding

For a bounded map `I : V →L[ℝ] H`, the form
`⟪u,v⟫_V + shift * ⟪I u,I v⟫_H` is coercive when `0 ≤ shift`.
Lax--Milgram therefore supplies a bounded solution map `H →L[ℝ] V`.

These are energy-space solutions. No assertion that their L² values belong
to the domain of a separately defined closed differential operator is made.
Compactness statements below explicitly retain the compactness of `I`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12HilbertEnergyShift4D

set_option autoImplicit false
noncomputable section

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]

/-- The energy form with a nonnegative L² shift. -/
def energyShiftForm (I : V →L[Real] H) (shift : Real) :
    V →L[Real] V →L[Real] Real :=
  (innerSL Real).comp
    (ContinuousLinearMap.id Real V + shift • I.adjoint.comp I)

theorem energyShiftForm_apply (I : V →L[Real] H) (shift : Real) (u v : V) :
    energyShiftForm I shift u v =
      inner Real u v + shift * inner Real (I u) (I v) := by
  change inner Real (u + shift • I.adjoint (I u)) v = _
  rw [inner_add_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]

theorem energyShiftForm_coercive (I : V →L[Real] H) (shift : Real)
    (hShift : 0 ≤ shift) : IsCoercive (energyShiftForm I shift) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u
  rw [energyShiftForm_apply, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  nlinarith [mul_nonneg hShift (sq_nonneg ‖I u‖)]

/-- The unique energy solution, not an inverse of an unidentified graph closure. -/
def energyShiftSolution (I : V →L[Real] H) (shift : Real)
    (hShift : 0 ≤ shift) : H →L[Real] V :=
  let e := (energyShiftForm_coercive I shift hShift).continuousLinearEquivOfBilin
  e.symm.toContinuousLinearMap.comp I.adjoint

theorem energyShiftSolution_pairing (I : V →L[Real] H) (shift : Real)
    (hShift : 0 ≤ shift) (f : H) (v : V) :
    inner Real (energyShiftSolution I shift hShift f) v +
        shift * inner Real (I (energyShiftSolution I shift hShift f)) (I v) =
      inner Real f (I v) := by
  let e := (energyShiftForm_coercive I shift hShift).continuousLinearEquivOfBilin
  change inner Real (e.symm (I.adjoint f)) v +
      shift * inner Real (I (e.symm (I.adjoint f))) (I v) = _
  calc
    _ = energyShiftForm I shift (e.symm (I.adjoint f)) v :=
      (energyShiftForm_apply I shift _ v).symm
    _ = inner Real (e (e.symm (I.adjoint f))) v :=
      (IsCoercive.continuousLinearEquivOfBilin_apply
        (energyShiftForm_coercive I shift hShift)
        (e.symm (I.adjoint f)) v).symm
    _ = inner Real f (I v) := by
      rw [e.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

theorem energyShiftSolution_unique (I : V →L[Real] H) (shift : Real)
    (hShift : 0 ≤ shift) (f : H) (u : V)
    (hu : ∀ v : V, inner Real u v + shift * inner Real (I u) (I v) =
      inner Real f (I v)) :
    u = energyShiftSolution I shift hShift f := by
  let e := (energyShiftForm_coercive I shift hShift).continuousLinearEquivOfBilin
  have he : e u = I.adjoint f := by
    apply ext_inner_right Real
    intro v
    calc
      inner Real (e u) v = energyShiftForm I shift u v :=
        (energyShiftForm_coercive I shift hShift).continuousLinearEquivOfBilin_apply u v
      _ = inner Real f (I v) := by
        rw [energyShiftForm_apply]
        exact hu v
      _ = inner Real (I.adjoint f) v :=
        (ContinuousLinearMap.adjoint_inner_left I v f).symm
  apply e.injective
  change e u = e (e.symm (I.adjoint f))
  rw [e.apply_symm_apply]
  exact he

/-- At zero shift, the energy solution map is precisely the adjoint embedding. -/
theorem energyShiftSolution_zero (I : V →L[Real] H) :
    energyShiftSolution I 0 (le_refl 0) = I.adjoint := by
  ext f
  symm
  apply energyShiftSolution_unique I 0 (le_refl 0) f (I.adjoint f)
  intro v
  simpa only [zero_mul, add_zero] using
    (ContinuousLinearMap.adjoint_inner_left I v f)

/-- The corresponding bounded L² solution map. -/
def energyShiftL2Solution (I : V →L[Real] H) (shift : Real)
    (hShift : 0 ≤ shift) : H →L[Real] H :=
  I.comp (energyShiftSolution I shift hShift)

/-- Faithfulness and density of the energy embedding make the weak L² solution
map injective. This does not assert that its range is a prescribed operator domain. -/
theorem energyShiftL2Solution_injective (I : V →L[Real] H)
    (hInjective : Function.Injective I) (hDense : DenseRange I)
    (shift : Real) (hShift : 0 ≤ shift) :
    Function.Injective (energyShiftL2Solution I shift hShift) := by
  let W := energyShiftSolution I shift hShift
  intro f g hfg
  change I (W f) = I (W g) at hfg
  have hW : W f = W g := hInjective hfg
  apply sub_eq_zero.mp
  refine hDense.eq_zero_of_inner_right (𝕜 := Real) ?_
  intro v
  have hf := energyShiftSolution_pairing I shift hShift f v
  have hg := energyShiftSolution_pairing I shift hShift g v
  change inner Real (W f) v + shift * inner Real (I (W f)) (I v) = _ at hf
  change inner Real (W g) v + shift * inner Real (I (W g)) (I v) = _ at hg
  rw [hW] at hf
  calc
    inner Real (I v) (f - g) =
        inner Real f (I v) - inner Real g (I v) := by
      rw [inner_sub_right, real_inner_comm (I v) f, real_inner_comm (I v) g]
    _ = 0 := sub_eq_zero.mpr (hf.symm.trans hg)

/-- Rellich compactness, when established for the actual embedding, propagates
through the weak solution map. It is not assumed implicitly. -/
theorem energyShiftL2Solution_compact (I : V →L[Real] H)
    (hCompact : IsCompactOperator I) (shift : Real) (hShift : 0 ≤ shift) :
    IsCompactOperator (energyShiftL2Solution I shift hShift) := by
  exact hCompact.comp_clm (energyShiftSolution I shift hShift)

end
end P0EFTJanusProgramPT12HilbertEnergyShift4D
end JanusFormal
