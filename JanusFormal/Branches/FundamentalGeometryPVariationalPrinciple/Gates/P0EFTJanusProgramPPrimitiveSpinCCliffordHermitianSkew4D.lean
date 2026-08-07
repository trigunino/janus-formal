import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D

/-!
# Skew-Hermitian primitive SpinC Clifford generators

The three doubled D9 Clifford generators are explicit complex matrices.  This
file proves directly, without an analytic or boundary hypothesis, that they
are skew-Hermitian for the positive fiber pairing used by the intrinsic
geometric `L²` completion.  The result is first checked in half-spinor
coordinates and then transported through the canonical real-linear matter
fiber equivalence.

This is the algebraic Clifford ingredient of the first-order Dirac Green
identity.  No action, field, frame, completion or D10 direction is added.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCCliffordHermitianSkew4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open scoped BigOperators Matrix
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D

/-- Standard positive doubled half-spinor pairing before transport to the
real matter fiber. -/
def d9DoubledHalfSpinorHermitianPairing
    (first second : D9DoubledMatterSpinor) : Complex :=
  ambientHalfSpinorHermitianPairing first.1 second.1 +
    ambientHalfSpinorHermitianPairing first.2 second.2

/-- The geometric doubled matter pairing is exactly the pullback of the
standard doubled half-spinor pairing. -/
theorem d9DoubledMatterSpinorHermitianPairing_eq_halfSpinor
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing first second =
      d9DoubledHalfSpinorHermitianPairing
        (d9DoubledMatterFiberHalfSpinorLinearEquiv first)
        (d9DoubledMatterFiberHalfSpinorLinearEquiv second) :=
  rfl

/-- Each explicit doubled Clifford matrix is skew-Hermitian in half-spinor
coordinates. -/
theorem d9DoubledHalfSpinorHermitianPairing_gamma
    (direction : Fin 3)
    (first second : D9DoubledMatterSpinor) :
    d9DoubledHalfSpinorHermitianPairing
        (d9DoubledMatterSpinorCliffordGamma direction first) second =
      -d9DoubledHalfSpinorHermitianPairing first
        (d9DoubledMatterSpinorCliffordGamma direction second) := by
  rcases first with ⟨firstPlus, firstMinus⟩
  rcases second with ⟨secondPlus, secondMinus⟩
  fin_cases direction <;>
    simp [d9DoubledHalfSpinorHermitianPairing,
      ambientHalfSpinorHermitianPairing,
      ambientPinCSpinorHermitianPairing, ambientHalfSpinorEmbed,
      Fin.sum_univ_succ] <;>
    ring

/-- Skew-Hermitian Clifford action on the actual doubled D9 matter fiber. -/
theorem d9DoubledMatterSpinorHermitianPairing_gamma
    (direction : Fin 3)
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing
        (d9DoubledMatterFiberCliffordGamma direction first) second =
      -d9DoubledMatterSpinorHermitianPairing first
        (d9DoubledMatterFiberCliffordGamma direction second) := by
  rw [d9DoubledMatterSpinorHermitianPairing_eq_halfSpinor,
    d9DoubledMatterSpinorHermitianPairing_eq_halfSpinor,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma]
  exact d9DoubledHalfSpinorHermitianPairing_gamma direction
    (d9DoubledMatterFiberHalfSpinorLinearEquiv first)
    (d9DoubledMatterFiberHalfSpinorLinearEquiv second)

/-- Equivalent right-to-left form used in the Dirac Green calculation. -/
theorem d9DoubledMatterSpinorHermitianPairing_gamma_right
    (direction : Fin 3)
    (first second : D9DoubledMatterFiber) :
    d9DoubledMatterSpinorHermitianPairing first
        (d9DoubledMatterFiberCliffordGamma direction second) =
      -d9DoubledMatterSpinorHermitianPairing
        (d9DoubledMatterFiberCliffordGamma direction first) second := by
  rw [d9DoubledMatterSpinorHermitianPairing_gamma]
  simp

/-- Public certificate for the three algebraic Clifford Green signs. -/
structure ProgramPPrimitiveSpinCCliffordHermitianSkewCertificate4D : Prop where
  skew : ∀ direction first second,
    d9DoubledMatterSpinorHermitianPairing
        (d9DoubledMatterFiberCliffordGamma direction first) second =
      -d9DoubledMatterSpinorHermitianPairing first
        (d9DoubledMatterFiberCliffordGamma direction second)

/-- The explicit D9 Clifford representation supplies the certificate
unconditionally. -/
def programPPrimitiveSpinCCliffordHermitianSkewCertificate4D :
    ProgramPPrimitiveSpinCCliffordHermitianSkewCertificate4D where
  skew := d9DoubledMatterSpinorHermitianPairing_gamma

end
end P0EFTJanusProgramPPrimitiveSpinCCliffordHermitianSkew4D
end JanusFormal
