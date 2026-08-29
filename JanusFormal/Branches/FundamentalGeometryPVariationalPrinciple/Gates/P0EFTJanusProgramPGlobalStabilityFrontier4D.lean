import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalADMFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDustFLRWConstrainedStability
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusReducedHamiltonianStability

/-!
# Exact stability frontier for Program P

The reduced proportional safe cone has nonnegative energy.  On the explicit
Candidate-A dust constraint surface, the complete tangent kernel is
one-dimensional and an exact nonlinear curve has constant zero Hamiltonian.
Thus the negative ambient affine Hessian is not a constrained instability,
but the witness is also not a strict isolated reduced vacuum.

This does not close `STABILITY-GLOBAL-01`: it still requires the continuum ADM
quotient, Boulware--Deser exclusion, all perturbative sectors, boundary/matter
control, weak limits and PPN.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalStabilityFrontier4D

set_option autoImplicit false

open P0EFTJanusReducedFLRWSecondaryConstraint
open P0EFTJanusMatterCurvatureFLRWConstraintBranch
open P0EFTJanusDustFLRWConstrainedStability

/-- A distinct constrained point with the same reduced Hamiltonian value as
the positive-dust witness. -/
def ReducedDustEqualEnergyWitness4D : Prop :=
  ∃ point : PhasePoint,
    point ≠ dustPoint ∧
    extendedPlusConstraint dustParameters point = 0 ∧
    extendedMinusConstraint dustParameters point = 0 ∧
    secondaryConstraint dustParameters.base point = 0 ∧
    fixedLapseHamiltonian point = fixedLapseHamiltonian dustPoint

theorem reduced_dust_equal_energy_witness :
    ReducedDustEqualEnergyWitness4D := by
  let point := exactConstraintCurve 1
  have hConstraints :=
    exactConstraintCurve_lies_on_constraints (1 : ℝ) (by norm_num)
  have hAtOne :=
    fixedLapseHamiltonian_exactConstraintCurve_eq_zero
      (1 : ℝ) (by norm_num)
  have hAtZero :=
    fixedLapseHamiltonian_exactConstraintCurve_eq_zero
      (0 : ℝ) (by norm_num)
  rw [exactConstraintCurve_at_zero] at hAtZero
  refine ⟨point, ?_, hConstraints.1, hConstraints.2.1,
    hConstraints.2.2, ?_⟩
  · intro hEqual
    have hCoordinate := congrArg PhasePoint.aPlus hEqual
    norm_num [point, exactConstraintCurve, dustPoint] at hCoordinate
  · exact hAtOne.trans hAtZero.symm

/-- Equal-energy constrained points occur at arbitrarily small positive curve
parameters, not only at one remote witness. -/
def ReducedDustArbitrarilyNearEqualEnergy4D : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ t : ℝ,
      0 < t ∧
      t < ε ∧
      exactConstraintCurve t ≠ dustPoint ∧
      extendedPlusConstraint dustParameters (exactConstraintCurve t) = 0 ∧
      extendedMinusConstraint dustParameters (exactConstraintCurve t) = 0 ∧
      secondaryConstraint dustParameters.base (exactConstraintCurve t) = 0 ∧
      fixedLapseHamiltonian (exactConstraintCurve t) =
        fixedLapseHamiltonian dustPoint

theorem reduced_dust_arbitrarily_near_equal_energy :
    ReducedDustArbitrarilyNearEqualEnergy4D := by
  intro ε hε
  let t : ℝ := ε / 2
  have htPositive : 0 < t := by
    dsimp [t]
    linarith
  have htSmall : t < ε := by
    dsimp [t]
    linarith
  have hScale : 1 + t ≠ 0 := by linarith
  have hConstraints := exactConstraintCurve_lies_on_constraints t hScale
  have hEnergy :=
    fixedLapseHamiltonian_exactConstraintCurve_eq_zero t hScale
  have hEnergyAtZero :=
    fixedLapseHamiltonian_exactConstraintCurve_eq_zero
      (0 : ℝ) (by norm_num)
  rw [exactConstraintCurve_at_zero] at hEnergyAtZero
  have hDistinct : exactConstraintCurve t ≠ dustPoint := by
    intro hEqual
    have hp : 1 + t = 1 := by
      simpa [exactConstraintCurve, dustPoint] using
        congrArg PhasePoint.pPlus hEqual
    linarith
  exact
    ⟨t, htPositive, htSmall, hDistinct,
      hConstraints.1, hConstraints.2.1, hConstraints.2.2,
      hEnergy.trans hEnergyAtZero.symm⟩

def ReducedDustStrictEnergyIsolationAlongConstraintCurve4D : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ t : ℝ, 0 < t → t < ε →
      fixedLapseHamiltonian (exactConstraintCurve t) ≠
        fixedLapseHamiltonian dustPoint

theorem reduced_dust_no_strict_energy_isolation :
    ¬ ReducedDustStrictEnergyIsolationAlongConstraintCurve4D := by
  rintro ⟨ε, hε, hIsolation⟩
  rcases reduced_dust_arbitrarily_near_equal_energy ε hε with
    ⟨t, htPositive, htSmall, _, _, _, _, hEnergy⟩
  exact (hIsolation t htPositive htSmall) hEnergy

def ReducedSafeConeNonnegative4D : Prop :=
  ∀ planckSquared relativeMassSquared beta1 beta2 c hPlus hMinus : ℝ,
    0 < planckSquared →
    0 ≤ relativeMassSquared →
    0 < beta1 →
    0 ≤ beta2 →
    0 < c →
    0 ≤
      P0EFTJanusReducedHamiltonianStability.reducedHamiltonian
        planckSquared relativeMassSquared beta1 beta2 c hPlus hMinus

theorem reduced_safe_cone_nonnegative :
    ReducedSafeConeNonnegative4D :=
  P0EFTJanusReducedHamiltonianStability.reduced_hamiltonian_nonnegative

structure ProgramPReducedStabilityFrontierCertificate4D where
  tangentKernelClassified :
    ∀ variation : PhasePoint,
      ConstrainedTangent variation ↔
        ∃ scale : ℝ, variation = tangentMultiple scale
  tangentGeneratorNonzero :
    tangentGenerator ≠
      ({ aPlus := 0, pPlus := 0, aMinus := 0, pMinus := 0 } : PhasePoint)
  ambientHessianNegative : -(1 / 3 : ℝ) < 0
  exactCurveTangent :
    HasDerivAt (fun t => (exactConstraintCurve t).aPlus)
        tangentGenerator.aPlus 0 ∧
      HasDerivAt (fun t => (exactConstraintCurve t).pPlus)
        tangentGenerator.pPlus 0 ∧
      HasDerivAt (fun t => (exactConstraintCurve t).aMinus)
        tangentGenerator.aMinus 0 ∧
      HasDerivAt (fun t => (exactConstraintCurve t).pMinus)
        tangentGenerator.pMinus 0
  exactCurveConstrained :
    ∀ (t : ℝ), 1 + t ≠ 0 →
      extendedPlusConstraint dustParameters (exactConstraintCurve t) = 0 ∧
      extendedMinusConstraint dustParameters (exactConstraintCurve t) = 0 ∧
      secondaryConstraint dustParameters.base (exactConstraintCurve t) = 0
  exactCurveHamiltonianFlat :
    ∀ (t : ℝ), 1 + t ≠ 0 →
      fixedLapseHamiltonian (exactConstraintCurve t) = 0
  exactCurveSecondVariationZero :
    HasDerivAt
      (fun t => deriv
        (fun s => fixedLapseHamiltonian (exactConstraintCurve s)) t)
      (0 : ℝ) 0
  distinctEqualEnergyPoint : ReducedDustEqualEnergyWitness4D
  arbitrarilyNearEqualEnergy : ReducedDustArbitrarilyNearEqualEnergy4D
  noStrictEnergyIsolation :
    ¬ ReducedDustStrictEnergyIsolationAlongConstraintCurve4D
  proportionalSafeCone : ReducedSafeConeNonnegative4D

def programPReducedStabilityFrontierCertificate4D :
    ProgramPReducedStabilityFrontierCertificate4D where
  tangentKernelClassified := constrainedTangent_iff_multiple
  tangentGeneratorNonzero := tangentGenerator_nonzero
  ambientHessianNegative := tangentGenerator_ambientHessian_negative
  exactCurveTangent := exactConstraintCurve_has_tangentGenerator
  exactCurveConstrained := exactConstraintCurve_lies_on_constraints
  exactCurveHamiltonianFlat :=
    fixedLapseHamiltonian_exactConstraintCurve_eq_zero
  exactCurveSecondVariationZero :=
    fixedLapseHamiltonian_exactConstraintCurve_secondVariation
  distinctEqualEnergyPoint := reduced_dust_equal_energy_witness
  arbitrarilyNearEqualEnergy := reduced_dust_arbitrarily_near_equal_energy
  noStrictEnergyIsolation := reduced_dust_no_strict_energy_isolation
  proportionalSafeCone := reduced_safe_cone_nonnegative

theorem global_stability_frontier_gate :
    Nonempty ProgramPReducedStabilityFrontierCertificate4D :=
  ⟨programPReducedStabilityFrontierCertificate4D⟩

/-- Explicit obligations still needed for terminal `STABILITY-GLOBAL-01`.
No inhabitant is constructed in this module. -/
structure ProgramPGlobalStabilityResidualContract4D
    extends
      P0EFTJanusProgramPGlobalADMFrontier4D.ProgramPGlobalADMResidualContract4D where
  physicalConstraintQuotientConstructed : Prop
  constrainedHessianSemibounded : Prop
  allScalarVectorTensorModesControlled : Prop
  nonlinearMatterBoundaryEnergyControlled : Prop
  weakFieldAndLongTimeLimitsControlled : Prop
  ppnLimitDerived : Prop

end P0EFTJanusProgramPGlobalStabilityFrontier4D
end JanusFormal
