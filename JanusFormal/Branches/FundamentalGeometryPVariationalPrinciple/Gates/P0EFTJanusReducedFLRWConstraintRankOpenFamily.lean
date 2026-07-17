import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedFLRWSecondaryConstraint

/-!
# An open rank-three family for the reduced FLRW constraints

The existing reduced Candidate-A gate exhibits one exact constrained point
where a `3 × 3` Jacobian minor of the two primary constraints and the
secondary constraint is nonzero.  This gate proves the general algebraic
implication from that minor to independence of the three displayed
covectors, and promotes the isolated witness to a nonempty open regular locus
along an explicit affine phase-space family.

This is a robust reduced-model rank theorem.  It does not derive the ADM
constraints from the covariant action, prove generic rank on the full phase
space, or exclude the Boulware--Deser mode globally.
-/

namespace JanusFormal
namespace P0EFTJanusReducedFLRWConstraintRankOpenFamily

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Filter Set Topology
open P0EFTJanusReducedFLRWSecondaryConstraint

/-! ## A nonzero minor gives rank three -/

/-- Linear independence of the two primary covectors and the secondary
covector, tested on the three columns used by `constraintJacobianMinor`. -/
def ConstraintDifferentialsIndependent
    (parameters : ReducedParameters) (x : PhasePoint) : Prop :=
  ∀ u v w : ℝ,
    u * (plusDifferential parameters x).aPlus +
          v * (minusDifferential parameters x).aPlus +
          w * (secondaryDifferential parameters x).aPlus = 0 →
      u * (plusDifferential parameters x).pPlus +
          v * (minusDifferential parameters x).pPlus +
          w * (secondaryDifferential parameters x).pPlus = 0 →
      u * (plusDifferential parameters x).aMinus +
          v * (minusDifferential parameters x).aMinus +
          w * (secondaryDifferential parameters x).aMinus = 0 →
      u = 0 ∧ v = 0 ∧ w = 0

theorem constraintDifferentialsIndependent_of_minor_ne_zero
    (parameters : ReducedParameters) (x : PhasePoint)
    (hMinor : constraintJacobianMinor parameters x ≠ 0) :
    ConstraintDifferentialsIndependent parameters x := by
  intro u v w haPlus hpPlus haMinus
  let plus := plusDifferential parameters x
  let minus := minusDifferential parameters x
  let secondary := secondaryDifferential parameters x
  change u * plus.aPlus + v * minus.aPlus + w * secondary.aPlus = 0 at haPlus
  change u * plus.pPlus + v * minus.pPlus + w * secondary.pPlus = 0 at hpPlus
  change u * plus.aMinus + v * minus.aMinus + w * secondary.aMinus = 0 at haMinus
  change det3 plus.aPlus plus.pPlus plus.aMinus
      minus.aPlus minus.pPlus minus.aMinus
      secondary.aPlus secondary.pPlus secondary.aMinus ≠ 0 at hMinor
  have huMul :
      u * det3 plus.aPlus plus.pPlus plus.aMinus
        minus.aPlus minus.pPlus minus.aMinus
        secondary.aPlus secondary.pPlus secondary.aMinus = 0 := by
    unfold det3
    linear_combination
      (minus.pPlus * secondary.aMinus -
          minus.aMinus * secondary.pPlus) * haPlus +
        (minus.aMinus * secondary.aPlus -
          minus.aPlus * secondary.aMinus) * hpPlus +
        (minus.aPlus * secondary.pPlus -
          minus.pPlus * secondary.aPlus) * haMinus
  have hvMul :
      v * det3 plus.aPlus plus.pPlus plus.aMinus
        minus.aPlus minus.pPlus minus.aMinus
        secondary.aPlus secondary.pPlus secondary.aMinus = 0 := by
    unfold det3
    linear_combination
      (plus.aMinus * secondary.pPlus -
          plus.pPlus * secondary.aMinus) * haPlus +
        (plus.aPlus * secondary.aMinus -
          plus.aMinus * secondary.aPlus) * hpPlus +
        (plus.pPlus * secondary.aPlus -
          plus.aPlus * secondary.pPlus) * haMinus
  have hwMul :
      w * det3 plus.aPlus plus.pPlus plus.aMinus
        minus.aPlus minus.pPlus minus.aMinus
        secondary.aPlus secondary.pPlus secondary.aMinus = 0 := by
    unfold det3
    linear_combination
      (plus.pPlus * minus.aMinus -
          plus.aMinus * minus.pPlus) * haPlus +
        (plus.aMinus * minus.aPlus -
          plus.aPlus * minus.aMinus) * hpPlus +
        (plus.aPlus * minus.pPlus -
          plus.pPlus * minus.aPlus) * haMinus
  exact ⟨(mul_eq_zero.mp huMul).resolve_right hMinor,
    (mul_eq_zero.mp hvMul).resolve_right hMinor,
    (mul_eq_zero.mp hwMul).resolve_right hMinor⟩

/-! ## Explicit open regular family through the constrained witness -/

/-- Vary only the minus momentum through the exact rational witness. -/
def constraintRankWitnessLine (parameter : ℝ) : PhasePoint :=
  { aPlus := 1
    pPlus := 3
    aMinus := 2
    pMinus := 66 / 7 + parameter }

@[simp]
theorem constraintRankWitnessLine_zero :
    constraintRankWitnessLine 0 = witnessPoint := by
  norm_num [constraintRankWitnessLine, witnessPoint]

theorem constraintRankWitnessLine_regular_domain (parameter : ℝ) :
    witnessParameters.interactionScale ≠ 0 ∧
      witnessParameters.planckPlusSq ≠ 0 ∧
      witnessParameters.planckMinusSq ≠ 0 ∧
      (constraintRankWitnessLine parameter).aPlus ≠ 0 ∧
      (constraintRankWitnessLine parameter).aMinus ≠ 0 ∧
      potentialFactor witnessParameters
        (constraintRankWitnessLine parameter) ≠ 0 := by
  norm_num [potentialFactor, witnessParameters, constraintRankWitnessLine]

theorem constraintRankWitnessLine_plusConstraint
    (parameter : ℝ) :
    plusConstraint witnessParameters (constraintRankWitnessLine parameter) = 0 := by
  norm_num [plusConstraint, plusPotential, witnessParameters,
    constraintRankWitnessLine]

theorem constraintRankWitnessLine_minusConstraint
    (parameter : ℝ) :
    minusConstraint witnessParameters (constraintRankWitnessLine parameter) =
      -parameter * (7 * parameter + 132) / 1848 := by
  norm_num [minusConstraint, minusPotential, witnessParameters,
    constraintRankWitnessLine]
  ring

theorem constraintRankWitnessLine_secondaryConstraint
    (parameter : ℝ) :
    secondaryConstraint witnessParameters (constraintRankWitnessLine parameter) =
      -13 * parameter / 44 := by
  norm_num [secondaryConstraint, kinematicFactor, potentialFactor,
    witnessParameters, constraintRankWitnessLine]
  ring

theorem constraintRankWitnessLine_on_constraint_surface_iff
    (parameter : ℝ) :
    (plusConstraint witnessParameters (constraintRankWitnessLine parameter) = 0 ∧
      minusConstraint witnessParameters (constraintRankWitnessLine parameter) = 0 ∧
      secondaryConstraint witnessParameters
        (constraintRankWitnessLine parameter) = 0) ↔
      parameter = 0 := by
  rw [constraintRankWitnessLine_plusConstraint,
    constraintRankWitnessLine_minusConstraint,
    constraintRankWitnessLine_secondaryConstraint]
  constructor
  · rintro ⟨_, _, hSecondary⟩
    linarith
  · rintro rfl
    norm_num

/-- Exact polynomial formula for the selected Jacobian minor along the
affine family. -/
theorem constraintJacobianMinor_witnessLine_exact
    (parameter : ℝ) :
    constraintJacobianMinor witnessParameters
        (constraintRankWitnessLine parameter) =
      (1715 * parameter ^ 3 + 7662963 * parameter ^ 2 +
          121546656 * parameter + 3146251680) / 55780032 := by
  norm_num [constraintJacobianMinor, det3, plusDifferential,
    minusDifferential, secondaryDifferential, kinematicFactor,
    potentialFactor, witnessParameters, constraintRankWitnessLine]
  ring

theorem constraintJacobianMinor_witnessLine_continuous :
    Continuous (fun parameter : ℝ =>
      constraintJacobianMinor witnessParameters
        (constraintRankWitnessLine parameter)) := by
  rw [show (fun parameter : ℝ =>
      constraintJacobianMinor witnessParameters
        (constraintRankWitnessLine parameter)) =
      fun parameter : ℝ =>
        (1715 * parameter ^ 3 + 7662963 * parameter ^ 2 +
          121546656 * parameter + 3146251680) / 55780032 by
    funext parameter
    exact constraintJacobianMinor_witnessLine_exact parameter]
  fun_prop

/-- Parameters on the explicit affine family where the three constraint
covectors retain rank three. -/
def ConstraintRankRegularWitnessParameters : Set ℝ :=
  {parameter |
    constraintJacobianMinor witnessParameters
      (constraintRankWitnessLine parameter) ≠ 0}

theorem constraintRankRegularWitnessParameters_isOpen :
    IsOpen ConstraintRankRegularWitnessParameters := by
  exact isOpen_ne_fun constraintJacobianMinor_witnessLine_continuous
    continuous_const

theorem zero_mem_constraintRankRegularWitnessParameters :
    (0 : ℝ) ∈ ConstraintRankRegularWitnessParameters := by
  change constraintJacobianMinor witnessParameters
      (constraintRankWitnessLine 0) ≠ 0
  rw [constraintRankWitnessLine_zero]
  exact witness_constraintJacobianMinor_nonzero

theorem eventually_constraintJacobianMinor_witnessLine_ne_zero :
    ∀ᶠ parameter in 𝓝 (0 : ℝ),
      constraintJacobianMinor witnessParameters
        (constraintRankWitnessLine parameter) ≠ 0 := by
  exact constraintRankRegularWitnessParameters_isOpen.mem_nhds
    zero_mem_constraintRankRegularWitnessParameters

theorem constraintRankWitnessLine_differentials_independent
    (parameter : ℝ)
    (hRegular : parameter ∈ ConstraintRankRegularWitnessParameters) :
    ConstraintDifferentialsIndependent witnessParameters
      (constraintRankWitnessLine parameter) :=
  constraintDifferentialsIndependent_of_minor_ne_zero witnessParameters
    (constraintRankWitnessLine parameter) hRegular

/-- The reduced rank-three locus is open, nonempty, contains the exact
constrained witness, and certifies covector independence at every one of its
points. -/
theorem reducedFLRWConstraintRankOpenFamily_closure :
    IsOpen ConstraintRankRegularWitnessParameters ∧
      ConstraintRankRegularWitnessParameters.Nonempty ∧
      (0 : ℝ) ∈ ConstraintRankRegularWitnessParameters ∧
      (∀ parameter ∈ ConstraintRankRegularWitnessParameters,
        ConstraintDifferentialsIndependent witnessParameters
          (constraintRankWitnessLine parameter)) := by
  exact ⟨constraintRankRegularWitnessParameters_isOpen,
    ⟨0, zero_mem_constraintRankRegularWitnessParameters⟩,
    zero_mem_constraintRankRegularWitnessParameters,
    constraintRankWitnessLine_differentials_independent⟩

end

end P0EFTJanusReducedFLRWConstraintRankOpenFamily
end JanusFormal
