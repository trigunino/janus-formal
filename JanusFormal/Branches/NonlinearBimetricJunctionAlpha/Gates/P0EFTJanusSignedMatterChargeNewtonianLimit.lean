import Mathlib
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTSymmetricFlatBimetricBranch

namespace JanusFormal
namespace P0EFTJanusSignedMatterChargeNewtonianLimit

set_option autoImplicit false

open P0EFTJanusPTSymmetricFlatBimetricBranch

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
Two positive spin-2 kinetic terms and signed matter charges reproduce the full
Janus Newtonian attraction/repulsion matrix without algebraic conflict.
-/
theorem positive_kinetic_terms_reproduce_full_janus_sign_matrix
    (planckPlusSquared planckMinusSquared hPlus hMinus : ℝ)
    (hPlanckPlus : 0 < planckPlusSquared)
    (hPlanckMinus : 0 < planckMinusSquared)
    (hMode : hPlus ≠ 0 ∨ hMinus ≠ 0) :
    0 < positiveSpinTwoKinetic
        planckPlusSquared planckMinusSquared hPlus hMinus ∧
      newtonianPotentialSign
          JanusCharge.positive JanusCharge.positive = -1 ∧
      newtonianPotentialSign
          JanusCharge.negative JanusCharge.negative = -1 ∧
      newtonianPotentialSign
          JanusCharge.positive JanusCharge.negative = 1 ∧
      newtonianPotentialSign
          JanusCharge.negative JanusCharge.positive = 1 := by
  refine ⟨positive_spin_two_kinetic_is_definite
      planckPlusSquared planckMinusSquared hPlus hMinus
      hPlanckPlus hPlanckMinus hMode, ?_⟩
  simp

/-- Real-valued charge used in the reduced common mediator action. -/
def chargeValueReal (q : JanusCharge) : ℝ :=
  chargeValue q

/-- Total signed source seen by one common Newtonian mediator. -/
def signedSource
    (q₁ q₂ : JanusCharge) (mass₁ mass₂ : ℝ) : ℝ :=
  chargeValueReal q₁ * mass₁ + chargeValueReal q₂ * mass₂

/-- Positive quadratic mediator energy with a linear signed-source coupling. -/
noncomputable def mediatorEnergy (stiffness source field : ℝ) : ℝ :=
  stiffness / 2 * field ^ 2 - source * field

/-- Stationary mediator field for nonzero stiffness. -/
noncomputable def stationaryMediator (stiffness source : ℝ) : ℝ :=
  source / stiffness

/-- Eliminating the mediator gives the exact reduced source energy. -/
theorem mediator_energy_at_stationary
    (stiffness source : ℝ)
    (hStiffness : stiffness ≠ 0) :
    mediatorEnergy stiffness source (stationaryMediator stiffness source) =
      -(source ^ 2) / (2 * stiffness) := by
  unfold mediatorEnergy stationaryMediator
  field_simp
  ring

/--
After subtracting the two self-energies, the common-action cross term is the
product of the signed charges, with the Janus attraction/repulsion sign.
-/
theorem reduced_cross_interaction_from_signed_source
    (stiffness mass₁ mass₂ : ℝ)
    (q₁ q₂ : JanusCharge)
    (hStiffness : stiffness ≠ 0) :
    -(signedSource q₁ q₂ mass₁ mass₂ ^ 2) / (2 * stiffness) -
        (-(chargeValueReal q₁ * mass₁) ^ 2 / (2 * stiffness)) -
        (-(chargeValueReal q₂ * mass₂) ^ 2 / (2 * stiffness)) =
      -(chargeValueReal q₁ * chargeValueReal q₂) *
        mass₁ * mass₂ / stiffness := by
  unfold signedSource
  field_simp
  ring

@[simp] theorem pt_reverses_real_charge (q : JanusCharge) :
    chargeValueReal (ptCharge q) = -chargeValueReal q := by
  cases q <;> norm_num [chargeValueReal, chargeValue, ptCharge]

/-- Reduced acceleration of a test body in a fixed mediator field. -/
noncomputable def testBodyAcceleration
    (charge : JanusCharge) (inertialMass field : ℝ) : ℝ :=
  chargeValueReal charge / inertialMass * field

/--
For the same positive inertial mass and background field, PT-related charges
accelerate in opposite directions.
-/
theorem pt_reverses_test_body_acceleration
    (charge : JanusCharge) (inertialMass field : ℝ) :
    testBodyAcceleration (ptCharge charge) inertialMass field =
      -testBodyAcceleration charge inertialMass field := by
  rw [testBodyAcceleration, testBodyAcceleration, pt_reverses_real_charge]
  ring

/--
Hence one field cannot give charge-independent free fall across both PT sectors
unless the tested field vanishes. The equivalence principle must be sectorwise
or the metric/field seen by PT-related matter must also transform.
-/
theorem cross_sector_universal_free_fall_forces_zero_field
    (inertialMass field : ℝ)
    (hMass : inertialMass ≠ 0)
    (hUniversal :
      testBodyAcceleration JanusCharge.positive inertialMass field =
        testBodyAcceleration JanusCharge.negative inertialMass field) :
    field = 0 := by
  unfold testBodyAcceleration chargeValueReal chargeValue at hUniversal
  field_simp [hMass] at hUniversal
  norm_num at hUniversal
  linarith

/-- PT-odd transformation law for the reduced mediator field. -/
def ptField (field : ℝ) : ℝ := -field

@[simp] theorem pt_field_involutive (field : ℝ) :
    ptField (ptField field) = field := by
  simp [ptField]

/--
When PT transforms both the matter charge and the mediator field, the test-body
acceleration is invariant. This is the reduced sectorwise-equivalence route.
-/
theorem simultaneous_pt_preserves_test_body_acceleration
    (charge : JanusCharge) (inertialMass field : ℝ) :
    testBodyAcceleration
        (ptCharge charge) inertialMass (ptField field) =
      testBodyAcceleration charge inertialMass field := by
  rw [testBodyAcceleration, testBodyAcceleration, pt_reverses_real_charge]
  unfold ptField
  ring

/-- The signed source-field interaction is PT even under simultaneous action. -/
theorem simultaneous_pt_preserves_source_field_coupling
    (charge : JanusCharge) (mass field : ℝ) :
    chargeValueReal (ptCharge charge) * mass * ptField field =
      chargeValueReal charge * mass * field := by
  rw [pt_reverses_real_charge]
  unfold ptField
  ring

/-- PT-odd transformation of the total reduced source. -/
def ptSource (source : ℝ) : ℝ := -source

/-- The positive mediator action is invariant under simultaneous PT. -/
theorem mediator_energy_is_pt_invariant
    (stiffness source field : ℝ) :
    mediatorEnergy stiffness (ptSource source) (ptField field) =
      mediatorEnergy stiffness source field := by
  unfold mediatorEnergy ptSource ptField
  ring

/-- The stationary mediator solution is equivariant under PT. -/
theorem stationary_mediator_is_pt_equivariant
    (stiffness source : ℝ) :
    stationaryMediator stiffness (ptSource source) =
      ptField (stationaryMediator stiffness source) := by
  unfold stationaryMediator ptSource ptField
  ring

/-- Real interaction sign carried by a pair of PT charges. -/
def pairInteractionSign (q₁ q₂ : JanusCharge) : ℝ :=
  -(chargeValueReal q₁ * chargeValueReal q₂)

/-- Translation-invariant reduced common potential for two sector variables. -/
noncomputable def signedPairPotential
    (coupling : ℝ) (q₁ q₂ : JanusCharge) (xPlus xMinus : ℝ) : ℝ :=
  pairInteractionSign q₁ q₂ * coupling / 2 * (xPlus - xMinus) ^ 2

/-- Euler source obtained by varying the plus variable. -/
def signedPairEulerPlus
    (coupling : ℝ) (q₁ q₂ : JanusCharge) (xPlus xMinus : ℝ) : ℝ :=
  pairInteractionSign q₁ q₂ * coupling * (xPlus - xMinus)

/-- Euler source obtained by varying the minus variable. -/
def signedPairEulerMinus
    (coupling : ℝ) (q₁ q₂ : JanusCharge) (xPlus xMinus : ℝ) : ℝ :=
  pairInteractionSign q₁ q₂ * coupling * (xMinus - xPlus)

/-- The common potential is invariant under diagonal translations. -/
theorem signed_pair_potential_diagonal_translation_invariant
    (coupling shift : ℝ) (q₁ q₂ : JanusCharge) (xPlus xMinus : ℝ) :
    signedPairPotential coupling q₁ q₂
        (xPlus + shift) (xMinus + shift) =
      signedPairPotential coupling q₁ q₂ xPlus xMinus := by
  unfold signedPairPotential
  ring

/-- Reduced diagonal Noether identity: exchange sources are exactly opposite. -/
theorem signed_pair_diagonal_noether_exchange
    (coupling : ℝ) (q₁ q₂ : JanusCharge) (xPlus xMinus : ℝ) :
    signedPairEulerPlus coupling q₁ q₂ xPlus xMinus +
        signedPairEulerMinus coupling q₁ q₂ xPlus xMinus = 0 := by
  unfold signedPairEulerPlus signedPairEulerMinus
  ring

/-- Equality of the reduced mixed variations from the common pair potential. -/
theorem signed_pair_mixed_variations_are_reciprocal
    (coupling increment : ℝ)
    (q₁ q₂ : JanusCharge) (xPlus xMinus : ℝ) :
    signedPairEulerPlus coupling q₁ q₂ xPlus (xMinus + increment) -
        signedPairEulerPlus coupling q₁ q₂ xPlus xMinus =
      signedPairEulerMinus coupling q₁ q₂ (xPlus + increment) xMinus -
        signedPairEulerMinus coupling q₁ q₂ xPlus xMinus := by
  unfold signedPairEulerPlus signedPairEulerMinus
  ring

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
