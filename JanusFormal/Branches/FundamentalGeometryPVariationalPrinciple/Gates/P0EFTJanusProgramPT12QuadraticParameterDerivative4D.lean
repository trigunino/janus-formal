import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! Polarization of a parameter derivative, with no norm required on the quadratic variable. -/
namespace JanusFormal.P0EFTJanusProgramPT12QuadraticParameterDerivative4D
set_option autoImplicit false
noncomputable section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [AddCommGroup V] [Module Real V]

theorem quadratic_affine_expansion (Q : QuadraticForm Real V) (a b : V) (t : Real) :
    Q (a + t • b) = Q a + t * (Q (a + b) - Q a - Q b) + t * t * Q b := by
  rw [QuadraticMap.map_add (Q : V → Real) a (t • b), Q.map_smul, Q.polar_smul_right]
  simp only [QuadraticMap.polar, smul_eq_mul]
  ring

variable (Q : E → QuadraticForm Real V) (x h : E)

def quadraticParameterDerivative (v : V) : Real := fderiv Real (fun y => Q y v) x h

theorem quadraticParameterDerivative_affine
    (a b : V) (hA : DifferentiableAt Real (fun y => Q y a) x)
    (hB : DifferentiableAt Real (fun y => Q y b) x)
    (hAB : DifferentiableAt Real (fun y => Q y (a + b)) x) (t : Real) :
    quadraticParameterDerivative Q x h (a + t • b) =
      quadraticParameterDerivative Q x h a +
        t * (quadraticParameterDerivative Q x h (a + b) -
          quadraticParameterDerivative Q x h a - quadraticParameterDerivative Q x h b) +
        t * t * quadraticParameterDerivative Q x h b := by
  have hEq : (fun y => Q y (a + t • b)) =
      (fun y => Q y a + t * (Q y (a + b) - Q y a - Q y b) + t * t * Q y b) :=
    funext (fun y => quadratic_affine_expansion (Q y) a b t)
  have hDerivative := (hA.hasFDerivAt.add
    (((hAB.hasFDerivAt.sub hA.hasFDerivAt).sub hB.hasFDerivAt).const_mul t)).add
      (hB.hasFDerivAt.const_mul (t * t))
  simp only [Pi.add_def, Pi.sub_def] at hDerivative
  unfold quadraticParameterDerivative
  rw [hEq, hDerivative.fderiv]
  rfl

/-- The potential derivative of the parameter derivative is its exact polarization. -/
theorem quadraticParameterDerivative_hasDerivAt
    (a b : V) (hA : DifferentiableAt Real (fun y => Q y a) x)
    (hB : DifferentiableAt Real (fun y => Q y b) x)
    (hAB : DifferentiableAt Real (fun y => Q y (a + b)) x) :
    HasDerivAt (fun t : Real => quadraticParameterDerivative Q x h (a + t • b))
      (quadraticParameterDerivative Q x h (a + b) - quadraticParameterDerivative Q x h a -
        quadraticParameterDerivative Q x h b) 0 := by
  simp_rw [quadraticParameterDerivative_affine Q x h a b hA hB hAB]
  have hDerivative := (hasDerivAt_const (0 : Real) (quadraticParameterDerivative Q x h a)).add
    ((hasDerivAt_id (0 : Real)).mul_const
      (quadraticParameterDerivative Q x h (a + b) - quadraticParameterDerivative Q x h a -
        quadraticParameterDerivative Q x h b)) |>.add
    (((hasDerivAt_id (0 : Real)).mul (hasDerivAt_id (0 : Real))).mul_const
      (quadraticParameterDerivative Q x h b))
  simpa only [Pi.add_def, Pi.mul_def, id_eq, zero_mul, mul_zero, zero_add, add_zero, one_mul] using hDerivative

end
end JanusFormal.P0EFTJanusProgramPT12QuadraticParameterDerivative4D
