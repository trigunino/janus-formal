import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientPinCActualPrincipalBundle4D

/-! # Determinant sector of the canonical ambient PinC extension

The determinant character is the square of the circle phase and therefore
descends through the diagonal quotient.  On the canonical extension obtained
from `(pin, 1)`, every determinant transition is trivial.  A nontrivial Janus
determinant/monopole sector thus requires an additional global `U(1)` twist.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientPinCDeterminantTriviality4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPAmbientPinCCechExtension4D
open P0EFTJanusProgramPAmbientPinCActualPrincipalBundle4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Product-level determinant character before dividing by `(-1,-1)`. -/
def ambientPinCProductDeterminantCharacter :
    AmbientCoordinatePinMinusGroup × Circle →* Circle where
  toFun element := element.2 ^ 2
  map_one' := by simp
  map_mul' first second := by
    simp only [Prod.snd_mul]
    exact mul_pow first.2 second.2 2

private theorem ambientPinCDiagonalSubgroup_le_determinantKernel :
    ambientPinCDiagonalSubgroup ≤ ambientPinCProductDeterminantCharacter.ker := by
  apply Subgroup.normalClosure_le_normal
  intro element hElement
  rw [Set.mem_singleton_iff.mp hElement]
  simp [ambientPinCDiagonalMinusOne,
    ambientPinCProductDeterminantCharacter]

/-- Determinant character of the actual algebraic `PinC(4)` quotient. -/
def ambientPinCDeterminantCharacter : AmbientPinC4 →* Circle :=
  QuotientGroup.lift ambientPinCDiagonalSubgroup
    ambientPinCProductDeterminantCharacter
    ambientPinCDiagonalSubgroup_le_determinantKernel

theorem continuous_ambientPinCDeterminantCharacter :
    Continuous ambientPinCDeterminantCharacter := by
  apply (QuotientGroup.isQuotientMap_mk
    ambientPinCDiagonalSubgroup).continuous_iff.mpr
  change Continuous (fun element : AmbientCoordinatePinMinusGroup × Circle ↦
    element.2 ^ 2)
  fun_prop

@[simp] theorem ambientPinCDeterminantCharacter_mk
    (pin : AmbientCoordinatePinMinusGroup) (phase : Circle) :
    ambientPinCDeterminantCharacter
        (QuotientGroup.mk' ambientPinCDiagonalSubgroup (pin, phase)) =
      phase ^ 2 := by
  exact QuotientGroup.lift_mk' _ _ (pin, phase)

/-- The canonical inclusion `(pin,1)` has trivial determinant. -/
@[simp] theorem ambientPinCDeterminantCharacter_pinMinusToPinC
    (pin : AmbientCoordinatePinMinusGroup) :
    ambientPinCDeterminantCharacter (ambientPinMinusToPinC pin) = 1 := by
  change ambientPinCDeterminantCharacter
      (QuotientGroup.mk' ambientPinCDiagonalSubgroup (pin, 1)) = 1
  rw [ambientPinCDeterminantCharacter_mk]
  simp

/-- Consequently every transition of the actual canonical ambient PinC bundle
has trivial determinant. -/
theorem canonicalAmbientPinCPrincipalBundle_determinantTransition_trivial
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) :
    ambientPinCDeterminantCharacter
        ((canonicalAmbientPinCPrincipalBundleCore period hPeriod).coordChange
          first second base 1) = 1 := by
  rw [show
    (canonicalAmbientPinCPrincipalBundleCore period hPeriod).coordChange
        first second base 1 =
      canonicalAmbientPinCPrincipalCoordChange period hPeriod
        first second base 1 by rfl]
  simp [canonicalAmbientPinCPrincipalCoordChange]

/-- This canonical extension cannot by itself supply a nontrivial determinant
transition. -/
theorem canonicalAmbientPinCPrincipalBundle_no_nontrivialDeterminantTransition :
    ¬ ∃ (first second : AmbientCover period hPeriod)
        (base : AmbientBase period hPeriod),
      ambientPinCDeterminantCharacter
          ((canonicalAmbientPinCPrincipalBundleCore period hPeriod).coordChange
            first second base 1) ≠ 1 := by
  rintro ⟨first, second, base, hNontrivial⟩
  exact hNontrivial
    (canonicalAmbientPinCPrincipalBundle_determinantTransition_trivial
      period hPeriod first second base)

structure ProgramPAmbientPinCDeterminantTrivialityCertificate4D where
  principalBundle :
    ProgramPAmbientPinCActualPrincipalBundleCertificate4D period hPeriod
  determinantCharacter : AmbientPinC4 →* Circle
  determinantCharacterCanonical :
    determinantCharacter = ambientPinCDeterminantCharacter
  allTransitionsTrivial : ∀ first second base,
    determinantCharacter
        ((principalBundle.core).coordChange first second base 1) = 1

def programPAmbientPinCDeterminantTrivialityCertificate4D :
    ProgramPAmbientPinCDeterminantTrivialityCertificate4D period hPeriod where
  principalBundle :=
    programPAmbientPinCActualPrincipalBundleCertificate4D period hPeriod
  determinantCharacter := ambientPinCDeterminantCharacter
  determinantCharacterCanonical := rfl
  allTransitionsTrivial :=
    canonicalAmbientPinCPrincipalBundle_determinantTransition_trivial
      period hPeriod

theorem programPAmbientPinCDeterminantTrivialityCertificate4D_nonempty :
    Nonempty
      (ProgramPAmbientPinCDeterminantTrivialityCertificate4D period hPeriod) :=
  ⟨programPAmbientPinCDeterminantTrivialityCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPAmbientPinCDeterminantTriviality4D
end JanusFormal
