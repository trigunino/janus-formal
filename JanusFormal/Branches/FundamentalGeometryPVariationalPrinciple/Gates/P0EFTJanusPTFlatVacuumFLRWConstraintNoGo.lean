import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedFLRWSecondaryConstraint

/-!
# PT-flat vacuum FLRW constraint no-go

In the exchange-symmetric flat family

`beta0 = beta4 = -4 beta1 - 3 beta2`, `beta3 = beta1`,

with `beta1 > 0`, `beta2 >= 0` and positive reduced gravitational data, the
two vacuum FLRW primary constraints force equal scale factors and vanishing
canonical momenta.  At that point their two primary covectors are dependent.

This is only a reduced, spatially flat, vacuum statement for the displayed
input Hamiltonians.  Matter, spatial curvature, or a different branch may
evade it.  No ADM constraint algebra or Boulware--Deser conclusion is made.
-/

namespace JanusFormal
namespace P0EFTJanusPTFlatVacuumFLRWConstraintNoGo

set_option autoImplicit false

noncomputable section

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusReducedFLRWSecondaryConstraint

/-- Exchange-symmetric coefficients satisfying the proportional-flat
condition at unit ratio. -/
def ptFlatCoefficients (beta1 beta2 : ℝ) : PotentialCoefficients :=
  { beta0 := -4 * beta1 - 3 * beta2
    beta1 := beta1
    beta2 := beta2
    beta3 := beta1
    beta4 := -4 * beta1 - 3 * beta2 }

/-- Reduced vacuum Hamiltonian parameters in the PT/exchange-flat family. -/
def ptFlatParameters
    (beta1 beta2 interactionScale planckPlusSq planckMinusSq : ℝ) :
    ReducedParameters :=
  { coefficients := ptFlatCoefficients beta1 beta2
    interactionScale := interactionScale
    planckPlusSq := planckPlusSq
    planckMinusSq := planckMinusSq }

/-- Positive cofactor of the plus potential on the physical scale-factor
domain. -/
def plusBranchFactor (beta1 beta2 : ℝ) (x : PhasePoint) : ℝ :=
  beta1 *
      (x.aMinus ^ 2 + x.aPlus * x.aMinus + 4 * x.aPlus ^ 2) +
    3 * beta2 * x.aPlus * (x.aMinus + x.aPlus)

/-- Positive cofactor of the minus potential on the physical scale-factor
domain. -/
def minusBranchFactor (beta1 beta2 : ℝ) (x : PhasePoint) : ℝ :=
  beta1 *
      (x.aPlus ^ 2 + x.aPlus * x.aMinus + 4 * x.aMinus ^ 2) +
    3 * beta2 * x.aMinus * (x.aPlus + x.aMinus)

/-- Exact factorization of the plus-lapse interaction polynomial. -/
theorem ptFlat_plusPotential_factor
    (beta1 beta2 interactionScale planckPlusSq planckMinusSq : ℝ)
    (x : PhasePoint) :
    plusPotential
        (ptFlatParameters beta1 beta2 interactionScale planckPlusSq
          planckMinusSq) x =
      (x.aMinus - x.aPlus) * plusBranchFactor beta1 beta2 x := by
  simp [plusPotential, ptFlatParameters, ptFlatCoefficients,
    plusBranchFactor]
  ring

/-- Exact factorization of the minus-lapse interaction polynomial. -/
theorem ptFlat_minusPotential_factor
    (beta1 beta2 interactionScale planckPlusSq planckMinusSq : ℝ)
    (x : PhasePoint) :
    minusPotential
        (ptFlatParameters beta1 beta2 interactionScale planckPlusSq
          planckMinusSq) x =
      (x.aPlus - x.aMinus) * minusBranchFactor beta1 beta2 x := by
  simp [minusPotential, ptFlatParameters, ptFlatCoefficients,
    minusBranchFactor]
  ring

theorem plusBranchFactor_pos
    (beta1 beta2 : ℝ) (x : PhasePoint)
    (hBeta1 : 0 < beta1) (hBeta2 : 0 ≤ beta2)
    (haPlus : 0 < x.aPlus) (haMinus : 0 < x.aMinus) :
    0 < plusBranchFactor beta1 beta2 x := by
  have hCore :
      0 < x.aMinus ^ 2 + x.aPlus * x.aMinus + 4 * x.aPlus ^ 2 := by
    positivity
  have hLeading :
      0 < beta1 *
        (x.aMinus ^ 2 + x.aPlus * x.aMinus + 4 * x.aPlus ^ 2) :=
    mul_pos hBeta1 hCore
  have hRemainder :
      0 ≤ 3 * beta2 * x.aPlus * (x.aMinus + x.aPlus) := by
    positivity
  exact add_pos_of_pos_of_nonneg hLeading hRemainder

theorem minusBranchFactor_pos
    (beta1 beta2 : ℝ) (x : PhasePoint)
    (hBeta1 : 0 < beta1) (hBeta2 : 0 ≤ beta2)
    (haPlus : 0 < x.aPlus) (haMinus : 0 < x.aMinus) :
    0 < minusBranchFactor beta1 beta2 x := by
  have hCore :
      0 < x.aPlus ^ 2 + x.aPlus * x.aMinus + 4 * x.aMinus ^ 2 := by
    positivity
  have hLeading :
      0 < beta1 *
        (x.aPlus ^ 2 + x.aPlus * x.aMinus + 4 * x.aMinus ^ 2) :=
    mul_pos hBeta1 hCore
  have hRemainder :
      0 ≤ 3 * beta2 * x.aMinus * (x.aPlus + x.aMinus) := by
    positivity
  exact add_pos_of_pos_of_nonneg hLeading hRemainder

/-- On the positive reduced domain, simultaneous vacuum primary constraints
force the symmetric static point. -/
theorem simultaneous_primary_constraints_force_symmetric_vacuum
    (beta1 beta2 interactionScale planckPlusSq planckMinusSq : ℝ)
    (x : PhasePoint)
    (hBeta1 : 0 < beta1) (hBeta2 : 0 ≤ beta2)
    (hScale : 0 < interactionScale)
    (hPlanckPlus : 0 < planckPlusSq)
    (hPlanckMinus : 0 < planckMinusSq)
    (haPlus : 0 < x.aPlus) (haMinus : 0 < x.aMinus)
    (hPlus :
      plusConstraint
          (ptFlatParameters beta1 beta2 interactionScale planckPlusSq
            planckMinusSq) x = 0)
    (hMinus :
      minusConstraint
          (ptFlatParameters beta1 beta2 interactionScale planckPlusSq
            planckMinusSq) x = 0) :
    x.aPlus = x.aMinus ∧ x.pPlus = 0 ∧ x.pMinus = 0 := by
  let parameters :=
    ptFlatParameters beta1 beta2 interactionScale planckPlusSq planckMinusSq
  have hDenPlus : 0 < 12 * planckPlusSq * x.aPlus := by positivity
  have hDenMinus : 0 < 12 * planckMinusSq * x.aMinus := by positivity
  have hPlusProduct :
      0 ≤ interactionScale * plusPotential parameters x := by
    have hEquality :
        interactionScale * plusPotential parameters x =
          x.pPlus ^ 2 / (12 * planckPlusSq * x.aPlus) := by
      change -(x.pPlus ^ 2) / (12 * planckPlusSq * x.aPlus) +
          interactionScale * plusPotential parameters x = 0 at hPlus
      rw [neg_div] at hPlus
      linarith
    rw [hEquality]
    exact div_nonneg (sq_nonneg _) hDenPlus.le
  have hMinusProduct :
      0 ≤ interactionScale * minusPotential parameters x := by
    have hEquality :
        interactionScale * minusPotential parameters x =
          x.pMinus ^ 2 / (12 * planckMinusSq * x.aMinus) := by
      change -(x.pMinus ^ 2) / (12 * planckMinusSq * x.aMinus) +
          interactionScale * minusPotential parameters x = 0 at hMinus
      rw [neg_div] at hMinus
      linarith
    rw [hEquality]
    exact div_nonneg (sq_nonneg _) hDenMinus.le
  have hPlusPotential : 0 ≤ plusPotential parameters x :=
    nonneg_of_mul_nonneg_right hPlusProduct hScale
  have hMinusPotential : 0 ≤ minusPotential parameters x :=
    nonneg_of_mul_nonneg_right hMinusProduct hScale
  rw [show parameters =
      ptFlatParameters beta1 beta2 interactionScale planckPlusSq
        planckMinusSq by rfl,
    ptFlat_plusPotential_factor] at hPlusPotential
  rw [show parameters =
      ptFlatParameters beta1 beta2 interactionScale planckPlusSq
        planckMinusSq by rfl,
    ptFlat_minusPotential_factor] at hMinusPotential
  have hMinusGePlus : 0 ≤ x.aMinus - x.aPlus :=
    nonneg_of_mul_nonneg_left hPlusPotential
      (plusBranchFactor_pos beta1 beta2 x hBeta1 hBeta2 haPlus haMinus)
  have hPlusGeMinus : 0 ≤ x.aPlus - x.aMinus :=
    nonneg_of_mul_nonneg_left hMinusPotential
      (minusBranchFactor_pos beta1 beta2 x hBeta1 hBeta2 haPlus haMinus)
  have hEqual : x.aPlus = x.aMinus := by linarith
  have hPlusPotentialZero : plusPotential parameters x = 0 := by
    rw [show parameters =
      ptFlatParameters beta1 beta2 interactionScale planckPlusSq
        planckMinusSq by rfl,
      ptFlat_plusPotential_factor, hEqual]
    simp
  have hMinusPotentialZero : minusPotential parameters x = 0 := by
    rw [show parameters =
      ptFlatParameters beta1 beta2 interactionScale planckPlusSq
        planckMinusSq by rfl,
      ptFlat_minusPotential_factor, hEqual]
    simp
  have hPlusReduced := hPlus
  have hMinusReduced := hMinus
  change plusConstraint parameters x = 0 at hPlusReduced
  change minusConstraint parameters x = 0 at hMinusReduced
  rw [plusConstraint, hPlusPotentialZero, mul_zero, add_zero] at hPlusReduced
  rw [minusConstraint, hMinusPotentialZero, mul_zero, add_zero] at hMinusReduced
  have hPlusNumerator : -(x.pPlus ^ 2) = 0 :=
    (div_eq_zero_iff.mp hPlusReduced).resolve_right hDenPlus.ne'
  have hMinusNumerator : -(x.pMinus ^ 2) = 0 :=
    (div_eq_zero_iff.mp hMinusReduced).resolve_right hDenMinus.ne'
  have hpPlus : x.pPlus = 0 :=
    sq_eq_zero_iff.mp (neg_eq_zero.mp hPlusNumerator)
  have hpMinus : x.pMinus = 0 :=
    sq_eq_zero_iff.mp (neg_eq_zero.mp hMinusNumerator)
  exact ⟨hEqual, hpPlus, hpMinus⟩

/-- Elementary coordinate formulation of dependence for two displayed
canonical covectors. -/
def primaryCovectorsDependent
    (first second : CanonicalCovector) : Prop :=
  ∃ u v : ℝ, (u ≠ 0 ∨ v ≠ 0) ∧
    u * first.aPlus + v * second.aPlus = 0 ∧
    u * first.pPlus + v * second.pPlus = 0 ∧
    u * first.aMinus + v * second.aMinus = 0 ∧
    u * first.pMinus + v * second.pMinus = 0

/-- At the forced symmetric vacuum, the two primary covectors are opposite
component by component. -/
theorem primary_differentials_component_sums_zero
    (beta1 beta2 interactionScale planckPlusSq planckMinusSq : ℝ)
    (x : PhasePoint)
    (hEqual : x.aPlus = x.aMinus)
    (hpPlus : x.pPlus = 0) (hpMinus : x.pMinus = 0) :
    let parameters :=
      ptFlatParameters beta1 beta2 interactionScale planckPlusSq planckMinusSq
    (plusDifferential parameters x).aPlus +
          (minusDifferential parameters x).aPlus = 0 ∧
      (plusDifferential parameters x).pPlus +
          (minusDifferential parameters x).pPlus = 0 ∧
      (plusDifferential parameters x).aMinus +
          (minusDifferential parameters x).aMinus = 0 ∧
      (plusDifferential parameters x).pMinus +
          (minusDifferential parameters x).pMinus = 0 := by
  dsimp
  constructor
  · simp [plusDifferential, minusDifferential, ptFlatParameters,
      ptFlatCoefficients, hEqual, hpPlus, hpMinus]
    ring
  constructor
  · simp [plusDifferential, minusDifferential, hpPlus, hpMinus]
  constructor
  · simp [plusDifferential, minusDifferential, ptFlatParameters,
      ptFlatCoefficients, hEqual, hpPlus, hpMinus]
    ring
  · simp [plusDifferential, minusDifferential, hpPlus, hpMinus]

theorem primary_differentials_dependent_on_symmetric_vacuum
    (beta1 beta2 interactionScale planckPlusSq planckMinusSq : ℝ)
    (x : PhasePoint)
    (hEqual : x.aPlus = x.aMinus)
    (hpPlus : x.pPlus = 0) (hpMinus : x.pMinus = 0) :
    let parameters :=
      ptFlatParameters beta1 beta2 interactionScale planckPlusSq planckMinusSq
    primaryCovectorsDependent (plusDifferential parameters x)
      (minusDifferential parameters x) := by
  dsimp
  rcases primary_differentials_component_sums_zero beta1 beta2
      interactionScale planckPlusSq planckMinusSq x hEqual hpPlus hpMinus with
    ⟨haPlus, hpPlusSum, haMinus, hpMinusSum⟩
  refine ⟨1, 1, Or.inl one_ne_zero, ?_⟩
  simpa only [one_mul] using ⟨haPlus, hpPlusSum, haMinus, hpMinusSum⟩

/-- Reduced PT-flat vacuum no-go: the only simultaneous positive-domain
primary solution is symmetric and static, where the primary covectors lose
independence. -/
theorem ptFlat_vacuum_FLRW_constraint_noGo
    (beta1 beta2 interactionScale planckPlusSq planckMinusSq : ℝ)
    (x : PhasePoint)
    (hBeta1 : 0 < beta1) (hBeta2 : 0 ≤ beta2)
    (hScale : 0 < interactionScale)
    (hPlanckPlus : 0 < planckPlusSq)
    (hPlanckMinus : 0 < planckMinusSq)
    (haPlus : 0 < x.aPlus) (haMinus : 0 < x.aMinus)
    (hPlus :
      plusConstraint
          (ptFlatParameters beta1 beta2 interactionScale planckPlusSq
            planckMinusSq) x = 0)
    (hMinus :
      minusConstraint
          (ptFlatParameters beta1 beta2 interactionScale planckPlusSq
            planckMinusSq) x = 0) :
    x.aPlus = x.aMinus ∧ x.pPlus = 0 ∧ x.pMinus = 0 ∧
      primaryCovectorsDependent
        (plusDifferential
          (ptFlatParameters beta1 beta2 interactionScale planckPlusSq
            planckMinusSq) x)
        (minusDifferential
          (ptFlatParameters beta1 beta2 interactionScale planckPlusSq
            planckMinusSq) x) := by
  obtain ⟨hEqual, hpPlus, hpMinus⟩ :=
    simultaneous_primary_constraints_force_symmetric_vacuum beta1 beta2
      interactionScale planckPlusSq planckMinusSq x hBeta1 hBeta2 hScale
      hPlanckPlus hPlanckMinus haPlus haMinus hPlus hMinus
  exact ⟨hEqual, hpPlus, hpMinus,
    primary_differentials_dependent_on_symmetric_vacuum beta1 beta2
      interactionScale planckPlusSq planckMinusSq x hEqual hpPlus hpMinus⟩

end

end P0EFTJanusPTFlatVacuumFLRWConstraintNoGo
end JanusFormal
