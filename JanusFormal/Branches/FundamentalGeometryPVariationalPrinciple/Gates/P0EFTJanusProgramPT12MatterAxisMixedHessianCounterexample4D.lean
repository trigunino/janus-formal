import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! A first-order chart match and a constant matter slice do not kill mixed Hessian terms. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MatterAxisMixedHessianCounterexample4D

def physicalAction (point : Real × Real) : Real :=
  point.2 + point.1 * point.2

theorem physicalAction_matter_axis_constant (matter : Real) :
    physicalAction (matter, 0) = 0 := by
  simp [physicalAction]

private theorem physicalAction_normal_derivative (point : Real × Real) :
    fderiv Real physicalAction point (0, 1) = 1 + point.1 := by
  have hFirst : HasFDerivAt (fun point : Real × Real => point.1)
      (ContinuousLinearMap.fst Real Real Real) point := hasFDerivAt_fst
  have hSecond : HasFDerivAt (fun point : Real × Real => point.2)
      (ContinuousLinearMap.snd Real Real Real) point := hasFDerivAt_snd
  have hAction := (hSecond.add (hFirst.mul hSecond)).fderiv
  change fderiv Real physicalAction point = _ at hAction
  rw [hAction]
  simp

/-- The mixed Fréchet second derivative is nonzero at the origin. -/
theorem physicalAction_mixed_hessian_nonzero :
    fderiv Real
        (fun point : Real × Real => fderiv Real physicalAction point (0, 1))
        (0, 0) (1, 0) = 1 := by
  have hFunction :
      (fun point : Real × Real => fderiv Real physicalAction point (0, 1)) =
        fun point => 1 + point.1 := by
    funext point
    exact physicalAction_normal_derivative point
  rw [hFunction]
  have hFirst : HasFDerivAt (fun point : Real × Real => point.1)
      (ContinuousLinearMap.fst Real Real Real) (0, 0) := hasFDerivAt_fst
  rw [(hFirst.const_add 1).fderiv]
  simp

end P0EFTJanusProgramPT12MatterAxisMixedHessianCounterexample4D
end JanusFormal
