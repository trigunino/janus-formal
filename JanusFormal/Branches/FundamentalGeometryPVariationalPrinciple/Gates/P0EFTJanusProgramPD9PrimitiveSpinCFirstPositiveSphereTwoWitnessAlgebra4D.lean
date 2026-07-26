import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexLinearity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexRadial4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereWitnessFiber4D
import Mathlib.Tactic

/-!
# Two-witness algebra for complex first-sphere multiplicity

The existing equatorial witness sees the two tangential complex coefficients
through one combination `c₁ + i c₂`.  The opposite Hopf fiber constructed in
the imported geometric gate carries the reversed Clifford sign and therefore
selects `c₁ - i c₂`.  Together with the already available radial coefficient
`c₀`, these three observables form an injective complex-linear transform

`(c₀,c₁,c₂) ↦ (c₀,c₁+i c₂,c₁-i c₂)`.

This gate isolates and proves that finite-dimensional algebra.  The remaining
geometric task is to identify the antipodal quotient evaluation with the
opposite Hopf fiber already constructed at the fiber level.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereTwoWitnessAlgebra4D

set_option autoImplicit false
noncomputable section

/-- Three complex multiplicity coordinates at the first spherical level. -/
abbrev PrimitiveSpinCFirstSphereComplexTriple := Fin 3 → Complex

/-- Radial observation followed by the two opposite tangential witness
combinations. -/
def primitiveSpinCFirstSphereTwoWitnessTransform :
    PrimitiveSpinCFirstSphereComplexTriple →ₗ[Complex]
      PrimitiveSpinCFirstSphereComplexTriple where
  toFun coefficients :=
    ![coefficients 0,
      coefficients 1 + Complex.I * coefficients 2,
      coefficients 1 - Complex.I * coefficients 2]
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp <;> ring
  map_smul' scalar coefficients := by
    ext coordinate
    fin_cases coordinate <;> simp <;> ring

@[simp]
theorem primitiveSpinCFirstSphereTwoWitnessTransform_zero
    (coefficients : PrimitiveSpinCFirstSphereComplexTriple) :
    primitiveSpinCFirstSphereTwoWitnessTransform coefficients 0 =
      coefficients 0 :=
  rfl

@[simp]
theorem primitiveSpinCFirstSphereTwoWitnessTransform_plus
    (coefficients : PrimitiveSpinCFirstSphereComplexTriple) :
    primitiveSpinCFirstSphereTwoWitnessTransform coefficients 1 =
      coefficients 1 + Complex.I * coefficients 2 :=
  rfl

@[simp]
theorem primitiveSpinCFirstSphereTwoWitnessTransform_minus
    (coefficients : PrimitiveSpinCFirstSphereComplexTriple) :
    primitiveSpinCFirstSphereTwoWitnessTransform coefficients 2 =
      coefficients 1 - Complex.I * coefficients 2 :=
  rfl

/-- Equality of the two opposite tangential observations recovers the first
tangential coefficient. -/
theorem primitiveSpinCFirstSphereTwoWitness_recover_one
    (first second : PrimitiveSpinCFirstSphereComplexTriple)
    (hPlus :
      first 1 + Complex.I * first 2 =
        second 1 + Complex.I * second 2)
    (hMinus :
      first 1 - Complex.I * first 2 =
        second 1 - Complex.I * second 2) :
    first 1 = second 1 := by
  calc
    first 1 =
        ((first 1 + Complex.I * first 2) +
          (first 1 - Complex.I * first 2)) / 2 := by ring
    _ =
        ((second 1 + Complex.I * second 2) +
          (second 1 - Complex.I * second 2)) / 2 := by
      rw [hPlus, hMinus]
    _ = second 1 := by ring

/-- Equality of the two opposite tangential observations also recovers the
second tangential coefficient. -/
theorem primitiveSpinCFirstSphereTwoWitness_recover_two
    (first second : PrimitiveSpinCFirstSphereComplexTriple)
    (hPlus :
      first 1 + Complex.I * first 2 =
        second 1 + Complex.I * second 2)
    (hMinus :
      first 1 - Complex.I * first 2 =
        second 1 - Complex.I * second 2) :
    first 2 = second 2 := by
  have hImaginary :
      Complex.I * first 2 = Complex.I * second 2 := by
    calc
      Complex.I * first 2 =
          ((first 1 + Complex.I * first 2) -
            (first 1 - Complex.I * first 2)) / 2 := by ring
      _ =
          ((second 1 + Complex.I * second 2) -
            (second 1 - Complex.I * second 2)) / 2 := by
        rw [hPlus, hMinus]
      _ = Complex.I * second 2 := by ring
  have hProduct : Complex.I * (first 2 - second 2) = 0 := by
    rw [mul_sub, hImaginary, sub_self]
  have hDifference : first 2 - second 2 = 0 :=
    (mul_eq_zero.mp hProduct).resolve_left Complex.I_ne_zero
  exact sub_eq_zero.mp hDifference

/-- The two-witness transform is injective over `ℂ`. -/
theorem primitiveSpinCFirstSphereTwoWitnessTransform_injective :
    Function.Injective primitiveSpinCFirstSphereTwoWitnessTransform := by
  intro first second hEqual
  have hZero := congrArg
    (fun observations : PrimitiveSpinCFirstSphereComplexTriple =>
      observations 0) hEqual
  have hPlus := congrArg
    (fun observations : PrimitiveSpinCFirstSphereComplexTriple =>
      observations 1) hEqual
  have hMinus := congrArg
    (fun observations : PrimitiveSpinCFirstSphereComplexTriple =>
      observations 2) hEqual
  apply funext
  intro coordinate
  fin_cases coordinate
  · simpa using hZero
  · exact primitiveSpinCFirstSphereTwoWitness_recover_one
      first second (by simpa using hPlus) (by simpa using hMinus)
  · exact primitiveSpinCFirstSphereTwoWitness_recover_two
      first second (by simpa using hPlus) (by simpa using hMinus)

/-- Vanishing of the radial and two opposite tangential observations forces
all three complex coefficients to vanish. -/
theorem primitiveSpinCFirstSphereTwoWitness_vanishing
    (coefficients : PrimitiveSpinCFirstSphereComplexTriple)
    (hZero : coefficients 0 = 0)
    (hPlus : coefficients 1 + Complex.I * coefficients 2 = 0)
    (hMinus : coefficients 1 - Complex.I * coefficients 2 = 0) :
    coefficients = 0 := by
  apply primitiveSpinCFirstSphereTwoWitnessTransform_injective
  apply funext
  intro coordinate
  fin_cases coordinate
  · simpa using hZero
  · simpa using hPlus
  · simpa using hMinus

/-- Consolidated algebraic closure of the two-witness coefficient problem. -/
theorem primitiveSpinCFirstSphereTwoWitnessAlgebra_closed :
    Function.Injective primitiveSpinCFirstSphereTwoWitnessTransform ∧
      (∀ coefficients : PrimitiveSpinCFirstSphereComplexTriple,
        coefficients 0 = 0 →
        coefficients 1 + Complex.I * coefficients 2 = 0 →
        coefficients 1 - Complex.I * coefficients 2 = 0 →
        coefficients = 0) :=
  ⟨primitiveSpinCFirstSphereTwoWitnessTransform_injective,
    primitiveSpinCFirstSphereTwoWitness_vanishing⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereTwoWitnessAlgebra4D
end JanusFormal
