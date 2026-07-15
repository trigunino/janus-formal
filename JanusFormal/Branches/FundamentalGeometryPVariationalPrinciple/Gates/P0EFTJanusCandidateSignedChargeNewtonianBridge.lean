import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitCandidatePointwiseEuler
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCandidateSourceModeDecomposition
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusSignedMatterChargeNewtonianLimit
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTSymmetricFlatBimetricBranch

/-!
# Candidate-A signed-charge Newtonian bridge

This gate connects three already explicit reduced ingredients:

* Candidate A's two independent quadratic matter slots;
* its diagonal/relative source decomposition;
* the positive-kinetic signed-charge Newtonian mediator.

Equal positive quadratic coefficients keep both pointwise matter directions
positive, while opposite PT sources are purely relative.  Eliminating the
positive mediator then gives the complete Janus attraction/repulsion table
without changing the sign of either spin-2 kinetic term.

This is a reduced algebraic bridge.  It does not derive the signed charge,
Poisson equation, or weak-field propagator from the covariant Candidate-A
metric/matter action, and it proves no PPN or nonlinear stability result.
-/

namespace JanusFormal
namespace P0EFTJanusCandidateSignedChargeNewtonianBridge

set_option autoImplicit false

noncomputable section

open P0EFTJanusExplicitCandidatePointwiseEuler
open P0EFTJanusCandidateSourceModeDecomposition
open P0EFTJanusSignedMatterChargeNewtonianLimit
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusPTSymmetricFlatBimetricBranch

/-- PT-paired Candidate-A pointwise matter coefficients. -/
def candidateAPTChargedMatter
    (massCoefficient source : ℝ) : MatterCoefficients where
  plusMass := massCoefficient
  plusSource := source
  minusMass := massCoefficient
  minusSource := -source

@[simp]
theorem candidateAPTChargedMatter_plusMass
    (massCoefficient source : ℝ) :
    (candidateAPTChargedMatter massCoefficient source).plusMass =
      massCoefficient := by
  rfl

@[simp]
theorem candidateAPTChargedMatter_minusMass
    (massCoefficient source : ℝ) :
    (candidateAPTChargedMatter massCoefficient source).minusMass =
      massCoefficient := by
  rfl

/-- The PT-paired source has no diagonal component and unit relative
coefficient in the source normalization used by Candidate A. -/
theorem candidateA_pt_paired_source_is_pure_relative (source : ℝ) :
    candidateADiagonalSource source (-source) = 0 ∧
      candidateARelativeSource source (-source) = source :=
  candidateA_opposite_pt_sources_are_pure_relative source

/-- Exact matter block of the Candidate-A pointwise Hessian on variations
with vanishing spectral component. -/
theorem candidateA_pt_matter_hessian_on_matter_variations
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (massCoefficient source : ℝ) (configuration : CandidateConfiguration)
    (plusVariation minusVariation : ℝ) :
    candidatePointwiseHessian interactionScale coefficients
        (candidateAPTChargedMatter massCoefficient source) configuration
        (0, (plusVariation, minusVariation))
        (0, (plusVariation, minusVariation)) =
      massCoefficient * (plusVariation ^ 2 + minusVariation ^ 2) := by
  rw [candidatePointwiseHessian_apply]
  simp [candidateAPTChargedMatter]
  ring

/-- Positive matter coefficients make the two independent pointwise matter
directions strictly positive away from the origin. -/
theorem candidateA_pt_matter_hessian_positive
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (massCoefficient source : ℝ) (configuration : CandidateConfiguration)
    (plusVariation minusVariation : ℝ)
    (hMass : 0 < massCoefficient)
    (hVariation : plusVariation ≠ 0 ∨ minusVariation ≠ 0) :
    0 < candidatePointwiseHessian interactionScale coefficients
        (candidateAPTChargedMatter massCoefficient source) configuration
        (0, (plusVariation, minusVariation))
        (0, (plusVariation, minusVariation)) := by
  rw [candidateA_pt_matter_hessian_on_matter_variations]
  have hSquares : 0 < plusVariation ^ 2 + minusVariation ^ 2 := by
    rcases hVariation with hPlus | hMinus
    · have hPlusSq : 0 < plusVariation ^ 2 := sq_pos_of_ne_zero hPlus
      nlinarith [sq_nonneg minusVariation]
    · have hMinusSq : 0 < minusVariation ^ 2 := sq_pos_of_ne_zero hMinus
      nlinarith [sq_nonneg plusVariation]
  exact mul_pos hMass hSquares

/-- Real form of the committed reduced PT charge. -/
def candidateAChargeValueReal (charge : JanusCharge) : ℝ :=
  chargeValue charge

/-- Candidate-A source normalization inherited from the signed PT charge. -/
def candidateAChargeSource (charge : JanusCharge) (mass : ℝ) : ℝ :=
  candidateAChargeValueReal charge * mass

@[simp]
theorem candidateAChargeSource_pt
    (charge : JanusCharge) (mass : ℝ) :
    candidateAChargeSource (ptCharge charge) mass =
      -candidateAChargeSource charge mass := by
  cases charge <;>
    norm_num [candidateAChargeSource, candidateAChargeValueReal,
      chargeValue, ptCharge]

/-- Total source of the local positive mediator used by this bridge. -/
def candidateASignedSource
    (charge₁ charge₂ : JanusCharge) (mass₁ mass₂ : ℝ) : ℝ :=
  candidateAChargeSource charge₁ mass₁ +
    candidateAChargeSource charge₂ mass₂

/-- Positive-quadratic reduced mediator energy with signed linear source. -/
def candidateAMediatorEnergy (stiffness source field : ℝ) : ℝ :=
  stiffness / 2 * field ^ 2 - source * field

/-- Stationary field of the reduced mediator for nonzero stiffness. -/
def candidateAStationaryMediator (stiffness source : ℝ) : ℝ :=
  source / stiffness

/-- Positive stiffness gives a strictly positive quadratic mediator term away
from the zero field. -/
theorem candidateA_mediator_quadratic_positive
    (stiffness field : ℝ) (hStiffness : 0 < stiffness)
    (hField : field ≠ 0) :
    0 < stiffness / 2 * field ^ 2 := by
  positivity

theorem candidateA_mediator_energy_at_stationary
    (stiffness source : ℝ) (hStiffness : stiffness ≠ 0) :
    candidateAMediatorEnergy stiffness source
        (candidateAStationaryMediator stiffness source) =
      -(source ^ 2) / (2 * stiffness) := by
  unfold candidateAMediatorEnergy candidateAStationaryMediator
  field_simp [hStiffness]
  ring

/-- The reduced common mediator cross term is exactly the product of the
Candidate-A PT-signed source coefficients. -/
theorem candidateA_signed_mediator_cross_term
    (stiffness mass₁ mass₂ : ℝ) (charge₁ charge₂ : JanusCharge)
    (hStiffness : 0 < stiffness) :
    candidateAMediatorEnergy stiffness
          (candidateASignedSource charge₁ charge₂ mass₁ mass₂)
          (candidateAStationaryMediator stiffness
            (candidateASignedSource charge₁ charge₂ mass₁ mass₂)) -
        candidateAMediatorEnergy stiffness
          (candidateAChargeSource charge₁ mass₁)
          (candidateAStationaryMediator stiffness
            (candidateAChargeSource charge₁ mass₁)) -
        candidateAMediatorEnergy stiffness
          (candidateAChargeSource charge₂ mass₂)
          (candidateAStationaryMediator stiffness
            (candidateAChargeSource charge₂ mass₂)) =
      -(candidateAChargeValueReal charge₁ *
          candidateAChargeValueReal charge₂) *
        mass₁ * mass₂ / stiffness := by
  have hStiffnessNe : stiffness ≠ 0 := ne_of_gt hStiffness
  rw [candidateA_mediator_energy_at_stationary _ _ hStiffnessNe,
    candidateA_mediator_energy_at_stationary _ _ hStiffnessNe,
    candidateA_mediator_energy_at_stationary _ _ hStiffnessNe]
  unfold candidateASignedSource candidateAChargeSource
  field_simp [hStiffnessNe]
  ring

/-- Positive spin-2 kinetic coefficients coexist with the complete Janus
Newtonian sign table in the reduced Candidate-A signed-source bridge. -/
theorem candidateA_positive_kinetic_full_janus_sign_matrix
    (planckPlusSquared planckMinusSquared hPlus hMinus : ℝ)
    (hPlanckPlus : 0 < planckPlusSquared)
    (hPlanckMinus : 0 < planckMinusSquared)
    (hMode : hPlus ≠ 0 ∨ hMinus ≠ 0) :
    0 < positiveSpinTwoKinetic
        planckPlusSquared planckMinusSquared hPlus hMinus ∧
      newtonianPotentialSign JanusCharge.positive JanusCharge.positive = -1 ∧
      newtonianPotentialSign JanusCharge.negative JanusCharge.negative = -1 ∧
      newtonianPotentialSign JanusCharge.positive JanusCharge.negative = 1 ∧
      newtonianPotentialSign JanusCharge.negative JanusCharge.positive = 1 :=
  by
    refine ⟨positive_spin_two_kinetic_is_definite
      planckPlusSquared planckMinusSquared hPlus hMinus
      hPlanckPlus hPlanckMinus hMode, ?_⟩
    simp

end

end P0EFTJanusCandidateSignedChargeNewtonianBridge
end JanusFormal
