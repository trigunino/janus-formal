import Mathlib

namespace JanusFormal
namespace P0EFTJanusSignedMatterChargeNewtonianLimit

set_option autoImplicit false

/-- PT-even and PT-odd gravitational charge sectors. -/
inductive JanusCharge where
  | positive
  | negative
  deriving DecidableEq

/-- Signed coupling carried by matter, not by the spin-2 kinetic energy. -/
def chargeValue : JanusCharge → ℤ
  | JanusCharge.positive => 1
  | JanusCharge.negative => -1

/--
Dimensionless sign of a Newtonian potential written as
`V = sign * G*m1*m2/r`. Negative sign means attraction, positive sign repulsion.
-/
def newtonianPotentialSign (q₁ q₂ : JanusCharge) : ℤ :=
  -(chargeValue q₁ * chargeValue q₂)

@[simp] theorem positive_positive_attracts :
    newtonianPotentialSign JanusCharge.positive JanusCharge.positive = -1 := by
  rfl

@[simp] theorem negative_negative_attracts :
    newtonianPotentialSign JanusCharge.negative JanusCharge.negative = -1 := by
  rfl

@[simp] theorem positive_negative_repels :
    newtonianPotentialSign JanusCharge.positive JanusCharge.negative = 1 := by
  rfl

@[simp] theorem negative_positive_repels :
    newtonianPotentialSign JanusCharge.negative JanusCharge.positive = 1 := by
  rfl

/-- PT exchanges the two signed matter sectors. -/
def ptCharge : JanusCharge → JanusCharge
  | JanusCharge.positive => JanusCharge.negative
  | JanusCharge.negative => JanusCharge.positive

@[simp] theorem pt_charge_involutive (q : JanusCharge) :
    ptCharge (ptCharge q) = q := by
  cases q <;> rfl

@[simp] theorem pt_reverses_charge_value (q : JanusCharge) :
    chargeValue (ptCharge q) = -chargeValue q := by
  cases q <;> rfl

/-- Applying PT to both sources leaves their force sign unchanged. -/
theorem simultaneous_pt_preserves_force_sign (q₁ q₂ : JanusCharge) :
    newtonianPotentialSign (ptCharge q₁) (ptCharge q₂) =
      newtonianPotentialSign q₁ q₂ := by
  cases q₁ <;> cases q₂ <;> rfl

/-- Applying PT to only one source reverses attraction and repulsion. -/
theorem single_pt_reverses_force_sign (q₁ q₂ : JanusCharge) :
    newtonianPotentialSign (ptCharge q₁) q₂ =
      -newtonianPotentialSign q₁ q₂ := by
  cases q₁ <;> cases q₂ <;> rfl

/--
The reduced sign table can be obtained without a negative spin-2 kinetic term.
A covariant completion must derive the signed matter coupling while keeping the
matter Hamiltonians and both graviton kinetic terms positive.
-/
structure SignedMatterCovariantClosureStatus where
  positiveMatterHamiltonianDerived : Prop
  negativeSectorMatterHamiltonianDerivedPositive : Prop
  ptOddGravitationalChargeOperatorDerived : Prop
  signedSourceCouplingDerivedFromAction : Prop
  equivalencePrincipleScopeDeclared : Prop
  positiveSpinTwoKineticTermsDerived : Prop
  janusNewtonianSignTableRecovered : Prop
  nonlinearEnergyStabilityProved : Prop


def signedMatterCovariantClosure
    (s : SignedMatterCovariantClosureStatus) : Prop :=
  s.positiveMatterHamiltonianDerived /\
  s.negativeSectorMatterHamiltonianDerivedPositive /\
  s.ptOddGravitationalChargeOperatorDerived /\
  s.signedSourceCouplingDerivedFromAction /\
  s.equivalencePrincipleScopeDeclared /\
  s.positiveSpinTwoKineticTermsDerived /\
  s.janusNewtonianSignTableRecovered /\
  s.nonlinearEnergyStabilityProved

end P0EFTJanusSignedMatterChargeNewtonianLimit
end JanusFormal
