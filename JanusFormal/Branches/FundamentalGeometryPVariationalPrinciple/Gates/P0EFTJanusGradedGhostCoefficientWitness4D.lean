import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusOrdinaryGhostNonlinearBRSTNoGo4D

/-!
# A nontrivial odd-coefficient witness for nonlinear ghost BRST

The ordinary real tangent ghost has zero self-bracket.  This gate constructs
an explicit faithful four-dimensional matrix model of two Grassmann-odd
coefficients.  Their squares vanish, they anticommute, and the graded cross
self-bracket coefficient is nonzero.  Thus odd coefficients genuinely evade
the ordinary-ghost no-go; no global diffeomorphism BRST or BV action is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusGradedGhostCoefficientWitness4D

set_option autoImplicit false

noncomputable section

abbrev OddCoefficientMatrix := Matrix (Fin 4) (Fin 4) Real

/-- Left multiplication by the first exterior generator on
`(1, θ₁, θ₂, θ₁θ₂)`. -/
def oddGeneratorOne : OddCoefficientMatrix :=
  ![![0, 0, 0, 0],
    ![1, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 1, 0]]

/-- Left multiplication by the second exterior generator. -/
def oddGeneratorTwo : OddCoefficientMatrix :=
  ![![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![1, 0, 0, 0],
    ![0, -1, 0, 0]]

theorem oddGeneratorOne_square :
    oddGeneratorOne * oddGeneratorOne = 0 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    norm_num [oddGeneratorOne, Matrix.mul_apply, Fin.sum_univ_succ]

theorem oddGeneratorTwo_square :
    oddGeneratorTwo * oddGeneratorTwo = 0 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    norm_num [oddGeneratorTwo, Matrix.mul_apply, Fin.sum_univ_succ]

theorem oddGenerators_anticommute :
    oddGeneratorOne * oddGeneratorTwo =
      -(oddGeneratorTwo * oddGeneratorOne) := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    norm_num [oddGeneratorOne, oddGeneratorTwo, Matrix.mul_apply,
      Fin.sum_univ_succ]

def oddVolumeCoefficient : OddCoefficientMatrix :=
  oddGeneratorOne * oddGeneratorTwo

theorem oddVolumeCoefficient_ne_zero : oddVolumeCoefficient ≠ 0 := by
  intro hZero
  have hEntry := congrArg
    (fun matrix : OddCoefficientMatrix => matrix 3 0) hZero
  norm_num [oddVolumeCoefficient, oddGeneratorOne, oddGeneratorTwo,
    Matrix.mul_apply, Fin.sum_univ_succ] at hEntry
  change (1 : Real) = 0 at hEntry
  norm_num at hEntry

/-- Coefficient multiplying `[X,Y]` in the graded expansion of
`[θ₁X + θ₂Y, θ₁X + θ₂Y]`. -/
def gradedCrossSelfBracketCoefficient : OddCoefficientMatrix :=
  oddGeneratorOne * oddGeneratorTwo - oddGeneratorTwo * oddGeneratorOne

theorem gradedCrossSelfBracketCoefficient_eq :
    gradedCrossSelfBracketCoefficient =
      (2 : Real) • oddVolumeCoefficient := by
  rw [gradedCrossSelfBracketCoefficient, oddVolumeCoefficient,
    oddGenerators_anticommute]
  module

theorem gradedCrossSelfBracketCoefficient_ne_zero :
    gradedCrossSelfBracketCoefficient ≠ 0 := by
  rw [gradedCrossSelfBracketCoefficient_eq]
  exact smul_ne_zero (by norm_num) oddVolumeCoefficient_ne_zero

/-- The conventional `-1/2` BRST factor leaves a nonzero odd quadratic
coefficient. -/
def gradedQuadraticGhostBRSTCoefficient : OddCoefficientMatrix :=
  (-((2 : Real)⁻¹)) • gradedCrossSelfBracketCoefficient

theorem gradedQuadraticGhostBRSTCoefficient_eq :
    gradedQuadraticGhostBRSTCoefficient = -oddVolumeCoefficient := by
  rw [gradedQuadraticGhostBRSTCoefficient,
    gradedCrossSelfBracketCoefficient_eq]
  module

theorem gradedQuadraticGhostBRSTCoefficient_ne_zero :
    gradedQuadraticGhostBRSTCoefficient ≠ 0 := by
  rw [gradedQuadraticGhostBRSTCoefficient_eq]
  exact neg_ne_zero.mpr oddVolumeCoefficient_ne_zero

theorem graded_ghost_coefficient_witness4D_closure :
    oddGeneratorOne * oddGeneratorOne = 0 ∧
      oddGeneratorTwo * oddGeneratorTwo = 0 ∧
      oddGeneratorOne * oddGeneratorTwo =
        -(oddGeneratorTwo * oddGeneratorOne) ∧
      gradedQuadraticGhostBRSTCoefficient ≠ 0 :=
  ⟨oddGeneratorOne_square, oddGeneratorTwo_square,
    oddGenerators_anticommute, gradedQuadraticGhostBRSTCoefficient_ne_zero⟩

end

end P0EFTJanusGradedGhostCoefficientWitness4D
end JanusFormal
