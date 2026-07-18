import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzJordanRelativeRoot4D

/-!
# Lorentz admissibility of the four-dimensional Jordan family

The null-coordinate metrics used by the 4D Jordan-root gate are genuinely
Lorentzian.  An explicit invertible frame puts every member into congruence
with `diag(-1,1,1,1)`.  This proves inertia, rather than merely symmetry or
nondegeneracy, for the entire one-parameter family.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzJordanAdmissibleSignature4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusLorentzJordanRelativeRoot4D

abbrev Matrix4 := P0EFTJanusLorentzJordanRelativeRoot4D.Matrix4

def minkowskiMetric4 : Matrix4 :=
  ![![-1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1]]

/-- Null frame whose second null-coordinate vector has squared norm
`parameter`. -/
def nullLorentzFrame4 (parameter : Real) : Matrix4 :=
  ![![1, (parameter - 1) / 2, 0, 0],
    ![1, (parameter + 1) / 2, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1]]

def nullLorentzFrameInverse4 (parameter : Real) : Matrix4 :=
  ![![(parameter + 1) / 2, (1 - parameter) / 2, 0, 0],
    ![-1, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1]]

theorem nullLorentzFrameInverse4_mul (parameter : Real) :
    nullLorentzFrameInverse4 parameter * nullLorentzFrame4 parameter = 1 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [nullLorentzFrameInverse4, nullLorentzFrame4, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring

theorem nullLorentzFrame4_mul_inverse (parameter : Real) :
    nullLorentzFrame4 parameter * nullLorentzFrameInverse4 parameter = 1 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [nullLorentzFrameInverse4, nullLorentzFrame4, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring

theorem nullLorentzFrame4_congruence (parameter : Real) :
    (nullLorentzFrame4 parameter).transpose * minkowskiMetric4 *
        nullLorentzFrame4 parameter = minusMetric4 parameter := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [nullLorentzFrame4, minkowskiMetric4, minusMetric4,
      Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

/-- Concrete congruence-based Lorentz signature witness. -/
structure LorentzSignatureWitness4 (metric : Matrix4) where
  frame : Matrix4
  inverseFrame : Matrix4
  inverse_mul_frame : inverseFrame * frame = 1
  frame_mul_inverse : frame * inverseFrame = 1
  congruence : frame.transpose * minkowskiMetric4 * frame = metric

def minusMetric4LorentzSignatureWitness (parameter : Real) :
    LorentzSignatureWitness4 (minusMetric4 parameter) where
  frame := nullLorentzFrame4 parameter
  inverseFrame := nullLorentzFrameInverse4 parameter
  inverse_mul_frame := nullLorentzFrameInverse4_mul parameter
  frame_mul_inverse := nullLorentzFrame4_mul_inverse parameter
  congruence := nullLorentzFrame4_congruence parameter

def plusMetric4LorentzSignatureWitness :
    LorentzSignatureWitness4 plusMetric4 := by
  simpa [minusMetric4, plusMetric4] using
    minusMetric4LorentzSignatureWitness 0

theorem plusMetric4_lorentzian :
    Nonempty (LorentzSignatureWitness4 plusMetric4) :=
  ⟨plusMetric4LorentzSignatureWitness⟩

theorem minusMetric4_lorentzian (parameter : Real) :
    Nonempty (LorentzSignatureWitness4 (minusMetric4 parameter)) :=
  ⟨minusMetric4LorentzSignatureWitness parameter⟩

theorem lorentz_jordan_admissible_signature4D_closure (parameter : Real) :
    Nonempty (LorentzSignatureWitness4 plusMetric4) ∧
      Nonempty (LorentzSignatureWitness4 (minusMetric4 parameter)) :=
  ⟨plusMetric4_lorentzian, minusMetric4_lorentzian parameter⟩

end

end P0EFTJanusLorentzJordanAdmissibleSignature4D
end JanusFormal
