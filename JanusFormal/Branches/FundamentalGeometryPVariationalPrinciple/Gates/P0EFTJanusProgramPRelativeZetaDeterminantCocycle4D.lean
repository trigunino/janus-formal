import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Transition cocycle of local relative zeta determinants

Local zeta derivatives `z_i(a) = zeta'_i(0,a)` determine local nonzero
determinant coordinates `D_i = exp(-z_i)`.  Their ratios define transition
functions

`g_ij = D_j / D_i = exp(z_i - z_j)`.

The transitions are nonzero, satisfy the exact cocycle law and carry the local
zeta connections by the usual gauge-transformation identity.  This is the
algebraic gluing datum needed for a determinant line on a general parameter
cover, independently of the special circle presentation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D

set_option autoImplicit false
noncomputable section

variable {Index : Type*}

/-- Local zeta derivatives and their parameter derivatives on one common real
parameter chart. -/
structure RelativeZetaLocalFamilyAtlasData (Index : Type*) where
  zetaPrimeAtZero : Index → Real → Complex
  parameterDerivative : Index → Real → Complex
  hasDerivAt_zetaPrime : ∀ index parameter,
    HasDerivAt (zetaPrimeAtZero index)
      (parameterDerivative index parameter) parameter

/-- Local nonzero determinant coordinate. -/
def relativeZetaLocalDeterminant
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real) : Complex :=
  Complex.exp (-atlas.zetaPrimeAtZero index parameter)

/-- Local determinants never vanish. -/
theorem relativeZetaLocalDeterminant_ne_zero
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real) :
    relativeZetaLocalDeterminant atlas index parameter ≠ 0 :=
  Complex.exp_ne_zero _

/-- Transition from local determinant coordinate `i` to `j`. -/
def relativeZetaTransition
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real) : Complex :=
  relativeZetaLocalDeterminant atlas second parameter /
    relativeZetaLocalDeterminant atlas first parameter

/-- Equivalent exponential formula for the transition. -/
theorem relativeZetaTransition_eq_exp
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real) :
    relativeZetaTransition atlas first second parameter =
      Complex.exp
        (atlas.zetaPrimeAtZero first parameter -
          atlas.zetaPrimeAtZero second parameter) := by
  unfold relativeZetaTransition relativeZetaLocalDeterminant
  rw [div_eq_mul_inv, ← Complex.exp_neg]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Every transition is nonzero. -/
theorem relativeZetaTransition_ne_zero
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real) :
    relativeZetaTransition atlas first second parameter ≠ 0 := by
  exact div_ne_zero
    (relativeZetaLocalDeterminant_ne_zero atlas second parameter)
    (relativeZetaLocalDeterminant_ne_zero atlas first parameter)

/-- Identity transition. -/
@[simp]
theorem relativeZetaTransition_self
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real) :
    relativeZetaTransition atlas index index parameter = 1 := by
  unfold relativeZetaTransition
  exact div_self (relativeZetaLocalDeterminant_ne_zero atlas index parameter)

/-- Inverse transition. -/
theorem relativeZetaTransition_inverse
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real) :
    relativeZetaTransition atlas first second parameter *
        relativeZetaTransition atlas second first parameter = 1 := by
  unfold relativeZetaTransition
  field_simp [relativeZetaLocalDeterminant_ne_zero]

/-- Exact Čech cocycle law. -/
theorem relativeZetaTransition_cocycle
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second third : Index) (parameter : Real) :
    relativeZetaTransition atlas second third parameter *
        relativeZetaTransition atlas first second parameter =
      relativeZetaTransition atlas first third parameter := by
  unfold relativeZetaTransition
  field_simp [relativeZetaLocalDeterminant_ne_zero]

/-- Derivative of a local determinant coordinate. -/
def relativeZetaLocalDeterminantDerivative
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real) : Complex :=
  -atlas.parameterDerivative index parameter *
    relativeZetaLocalDeterminant atlas index parameter

/-- Chain rule for each local determinant. -/
theorem relativeZetaLocalDeterminant_hasDerivAt
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real) :
    HasDerivAt (relativeZetaLocalDeterminant atlas index)
      (relativeZetaLocalDeterminantDerivative atlas index parameter)
      parameter := by
  have hNegative : HasDerivAt
      (fun current => -atlas.zetaPrimeAtZero index current)
      (-atlas.parameterDerivative index parameter) parameter :=
    (atlas.hasDerivAt_zetaPrime index parameter).neg
  have hExp :=
    (Complex.hasDerivAt_exp
      (-atlas.zetaPrimeAtZero index parameter)).comp parameter hNegative
  apply hExp.congr_deriv
  unfold relativeZetaLocalDeterminantDerivative
    relativeZetaLocalDeterminant
  ring

/-- Derivative of a transition function. -/
def relativeZetaTransitionDerivative
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real) : Complex :=
  (atlas.parameterDerivative first parameter -
      atlas.parameterDerivative second parameter) *
    relativeZetaTransition atlas first second parameter

/-- Transition derivative from the exponential formula. -/
theorem relativeZetaTransition_hasDerivAt
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real) :
    HasDerivAt (relativeZetaTransition atlas first second)
      (relativeZetaTransitionDerivative atlas first second parameter)
      parameter := by
  rw [show relativeZetaTransition atlas first second =
      fun current => Complex.exp
        (atlas.zetaPrimeAtZero first current -
          atlas.zetaPrimeAtZero second current) by
    funext current
    exact relativeZetaTransition_eq_exp atlas first second current]
  have hDifference : HasDerivAt
      (fun current => atlas.zetaPrimeAtZero first current -
        atlas.zetaPrimeAtZero second current)
      (atlas.parameterDerivative first parameter -
        atlas.parameterDerivative second parameter) parameter :=
    (atlas.hasDerivAt_zetaPrime first parameter).sub
      (atlas.hasDerivAt_zetaPrime second parameter)
  have hExp :=
    (Complex.hasDerivAt_exp
      (atlas.zetaPrimeAtZero first parameter -
        atlas.zetaPrimeAtZero second parameter)).comp parameter hDifference
  apply hExp.congr_deriv
  unfold relativeZetaTransitionDerivative
  rw [relativeZetaTransition_eq_exp]
  ring

/-- Local connection coefficient. -/
def relativeZetaLocalConnectionCoefficient
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real) : Complex :=
  atlas.parameterDerivative index parameter

/-- Gauge-transformation identity
`g'_ij + A_j g_ij = g_ij A_i`. -/
theorem relativeZetaTransition_connection_gauge
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real) :
    relativeZetaTransitionDerivative atlas first second parameter +
        relativeZetaLocalConnectionCoefficient atlas second parameter *
          relativeZetaTransition atlas first second parameter =
      relativeZetaTransition atlas first second parameter *
        relativeZetaLocalConnectionCoefficient atlas first parameter := by
  unfold relativeZetaTransitionDerivative
    relativeZetaLocalConnectionCoefficient
  ring

/-- Public determinant-line cocycle checkpoint. -/
theorem relative_zeta_determinant_cocycle_gate
    (atlas : RelativeZetaLocalFamilyAtlasData Index) :
    (∀ index parameter,
      relativeZetaTransition atlas index index parameter = 1) ∧
      (∀ first second third parameter,
        relativeZetaTransition atlas second third parameter *
            relativeZetaTransition atlas first second parameter =
          relativeZetaTransition atlas first third parameter) ∧
      (∀ first second parameter,
        relativeZetaTransitionDerivative atlas first second parameter +
            relativeZetaLocalConnectionCoefficient atlas second parameter *
              relativeZetaTransition atlas first second parameter =
          relativeZetaTransition atlas first second parameter *
            relativeZetaLocalConnectionCoefficient atlas first parameter) :=
  ⟨relativeZetaTransition_self atlas,
    relativeZetaTransition_cocycle atlas,
    relativeZetaTransition_connection_gauge atlas⟩

end
end P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D
end JanusFormal
