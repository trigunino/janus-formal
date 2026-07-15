import Mathlib

namespace JanusFormal
namespace P0EFTJanusPTQuasilocalChargePairing

set_option autoImplicit false

/-- A PT involution acting on boundary states with an odd quasi-local charge. -/
structure PTOddChargePair (BoundaryState : Type*) where
  pt : BoundaryState -> BoundaryState
  charge : BoundaryState -> ℝ
  plusState : BoundaryState
  minusState : BoundaryState
  ptInvolutive : ∀ state, pt (pt state) = state
  chargeIsPTOdd : ∀ state, charge (pt state) = -charge state
  pairedBoundaryLaw : minusState = pt plusState

/-- Paired Janus boundaries carry opposite signed quasi-local charges. -/
theorem paired_charges_are_opposite
    {BoundaryState : Type*}
    (p : PTOddChargePair BoundaryState) :
    p.charge p.minusState = -p.charge p.plusState := by
  rw [p.pairedBoundaryLaw]
  exact p.chargeIsPTOdd p.plusState

/-- The magnitudes of the paired charges coincide. -/
theorem paired_charge_squares_are_equal
    {BoundaryState : Type*}
    (p : PTOddChargePair BoundaryState) :
    p.charge p.minusState ^ 2 = p.charge p.plusState ^ 2 := by
  rw [paired_charges_are_opposite p]
  ring

/-- Positive bridge mass obtained from a negative signed sector charge. -/
structure PTBridgeMassPair (BoundaryState : Type*) extends
    PTOddChargePair BoundaryState where
  signedNegativeCharge : ℝ
  bridgeMass : ℝ
  negativeChargeIdentification :
    signedNegativeCharge = charge minusState
  bridgeMassDefinition :
    bridgeMass = -signedNegativeCharge

/-- The bridge mass equals the positive-fold charge for a PT-paired state. -/
theorem bridge_mass_eq_positive_charge
    {BoundaryState : Type*}
    (p : PTBridgeMassPair BoundaryState) :
    p.bridgeMass = p.charge p.plusState := by
  calc
    p.bridgeMass = -p.signedNegativeCharge := p.bridgeMassDefinition
    _ = -p.charge p.minusState := by rw [p.negativeChargeIdentification]
    _ = p.charge p.plusState := by
      rw [paired_charges_are_opposite p.toPTOddChargePair]
      ring

/-- PT-paired boundary first-variation data. -/
structure PTOddBoundaryVariationPair (BoundaryVariation : Type*) where
  pt : BoundaryVariation → BoundaryVariation
  boundaryTerm : BoundaryVariation → ℝ
  plusVariation : BoundaryVariation
  minusVariation : BoundaryVariation
  ptInvolutive : ∀ variation, pt (pt variation) = variation
  boundaryTermPTOdd : ∀ variation,
    boundaryTerm (pt variation) = -boundaryTerm variation
  pairedVariationLaw : minusVariation = pt plusVariation

/-- PT-paired boundary variations cancel in the total first variation. -/
theorem paired_boundary_variations_cancel
    {BoundaryVariation : Type*}
    (p : PTOddBoundaryVariationPair BoundaryVariation) :
    p.boundaryTerm p.plusVariation +
        p.boundaryTerm p.minusVariation = 0 := by
  rw [p.pairedVariationLaw, p.boundaryTermPTOdd]
  ring

/--
Cancellation on the PT-paired subspace is weaker than independent boundary
stationarity; the latter must still be derived from the full junction action.
-/
theorem paired_cancellation_does_not_force_independent_vanishing :
    ∃ plusTerm minusTerm : ℝ,
      plusTerm + minusTerm = 0 ∧ plusTerm ≠ 0 ∧ minusTerm ≠ 0 := by
  exact ⟨1, -1, by norm_num, by norm_num, by norm_num⟩

/--
The algebraic sign reversal is closed.  The physical work is to construct the
quasi-local charge from the nonlinear two-metric action and prove its PT oddness
with the correct orientations and null-boundary terms.
-/
structure PTChargeDerivationStatus where
  covariantPhaseSpaceDefined : Prop
  boundarySymplecticPotentialDerived : Prop
  HamiltonianChargeIntegrable : Prop
  plusMinusBoundaryPairingDerived : Prop
  ptActionOnNormalsDerived : Prop
  ptActionOnTimeOrientationDerived : Prop
  chargePTOddnessProved : Prop
  signedMassToBridgeMassMapDerived : Prop


def ptChargeDerivationClosed
    (s : PTChargeDerivationStatus) : Prop :=
  s.covariantPhaseSpaceDefined /\
  s.boundarySymplecticPotentialDerived /\
  s.HamiltonianChargeIntegrable /\
  s.plusMinusBoundaryPairingDerived /\
  s.ptActionOnNormalsDerived /\
  s.ptActionOnTimeOrientationDerived /\
  s.chargePTOddnessProved /\
  s.signedMassToBridgeMassMapDerived

end P0EFTJanusPTQuasilocalChargePairing
end JanusFormal
