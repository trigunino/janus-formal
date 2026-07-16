import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzJordanAdmissibleSignature4D

/-!
# Sylvester regularity on the four-dimensional Lorentz Jordan stratum

For `X = I + (t/2)N` with `N² = 0`, the Sylvester map
`H ↦ XH + HX` has a finite explicit inverse.  Hence the genuine Lorentz
Jordan family is Sylvester regular for every real parameter, including its
non-diagonalizable members.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzJordanSylvesterRegular4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusLorentzJordanRelativeRoot4D

abbrev Matrix4 := P0EFTJanusLorentzJordanRelativeRoot4D.Matrix4

def jordanSylvester4 (parameter : Real) (variation : Matrix4) : Matrix4 :=
  jordanRoot4 parameter * variation + variation * jordanRoot4 parameter

/-- Finite inverse of `2I + (parameter/2)(N· + ·N)`. -/
def jordanSylvesterInverse4 (parameter : Real) (target : Matrix4) : Matrix4 :=
  (1 / 2 : Real) • target -
    (parameter / 8) • (jordanNilpotent4 * target + target * jordanNilpotent4) +
    (parameter ^ 2 / 16) •
      (jordanNilpotent4 * target * jordanNilpotent4)

theorem jordanSylvester4_inverse_apply (parameter : Real) (target : Matrix4) :
    jordanSylvester4 parameter (jordanSylvesterInverse4 parameter target) =
      target := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [jordanSylvester4, jordanSylvesterInverse4, jordanRoot4,
      jordanNilpotent4, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply] <;>
    ring

theorem jordanSylvesterInverse4_apply (parameter : Real) (variation : Matrix4) :
    jordanSylvesterInverse4 parameter (jordanSylvester4 parameter variation) =
      variation := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [jordanSylvester4, jordanSylvesterInverse4, jordanRoot4,
      jordanNilpotent4, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply] <;>
    ring

theorem jordanSylvester4_bijective (parameter : Real) :
    Function.Bijective (jordanSylvester4 parameter) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨jordanSylvesterInverse4 parameter,
      jordanSylvesterInverse4_apply parameter,
      jordanSylvester4_inverse_apply parameter⟩

def jordanRootTangent4 : Matrix4 :=
  (1 / 2 : Real) • jordanNilpotent4

theorem jordanRoot4_increment (parameter increment : Real) :
    jordanRoot4 (parameter + increment) - jordanRoot4 parameter =
      increment • jordanRootTangent4 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [jordanRoot4, jordanRootTangent4, jordanNilpotent4]
  all_goals ring

theorem jordanRelative4_increment (parameter increment : Real) :
    jordanRelative4 (parameter + increment) - jordanRelative4 parameter =
      increment • jordanNilpotent4 := by
  simp [jordanRelative4, add_smul]

theorem jordanSylvester4_rootTangent (parameter : Real) :
    jordanSylvester4 parameter jordanRootTangent4 = jordanNilpotent4 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [jordanSylvester4, jordanRoot4, jordanRootTangent4,
      jordanNilpotent4, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply]
  all_goals ring

theorem jordanRootTangent4_unique (parameter : Real) (variation : Matrix4)
    (hVariation : jordanSylvester4 parameter variation = jordanNilpotent4) :
    variation = jordanRootTangent4 := by
  rw [← jordanSylvesterInverse4_apply parameter variation, hVariation]
  rw [← jordanSylvester4_rootTangent parameter]
  exact jordanSylvesterInverse4_apply parameter jordanRootTangent4

theorem lorentz_jordan_sylvester_regular4D_closure (parameter : Real) :
    Function.Bijective (jordanSylvester4 parameter) ∧
      jordanSylvester4 parameter jordanRootTangent4 = jordanNilpotent4 ∧
      ∀ variation,
        jordanSylvester4 parameter variation = jordanNilpotent4 →
          variation = jordanRootTangent4 :=
  ⟨jordanSylvester4_bijective parameter,
    jordanSylvester4_rootTangent parameter,
    jordanRootTangent4_unique parameter⟩

end

end P0EFTJanusLorentzJordanSylvesterRegular4D
end JanusFormal
