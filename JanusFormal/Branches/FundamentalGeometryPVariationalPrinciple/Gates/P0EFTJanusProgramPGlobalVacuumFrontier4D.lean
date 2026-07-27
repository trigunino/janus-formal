import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalStabilityFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPTFlatBimetricVariationalBridge
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalSchemeFrontier4D

/-!
# Exact vacuum frontier for Program P

The PT-flat proportional interaction has a unique positive minimizer at
ratio one with positive reduced Hessian.  The vacuum FLRW constraints,
however, force a symmetric static point where their primary covectors become
dependent; the sourced reduced branch also contains a nontrivial
equal-energy constrained curve.  Finally, the effective action retains a
formally proved finite-scheme freedom.

Therefore these exact sectorial results do not close `VACUUM-GLOBAL-01`.
A unique physical vacuum still requires the complete constraint quotient,
anomaly trivialization and microscopic finite-part selection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalVacuumFrontier4D

set_option autoImplicit false

open P0EFTJanusReducedFLRWSecondaryConstraint
open P0EFTJanusPTFlatVacuumFLRWConstraintNoGo
open P0EFTJanusPTSymmetricFlatBimetricBranch
open P0EFTJanusPTFlatBimetricVariationalBridge
open P0EFTJanusProgramPGlobalStabilityFrontier4D
open P0EFTJanusProgramPGlobalSchemeFrontier4D

def ProportionalVacuumMinimum4D : Prop :=
  ∀ beta1 beta2 c : ℝ,
    0 < beta1 →
    0 ≤ beta2 →
    0 < c →
    proportionalInteractionEnergy beta1 beta2 1 ≤
        proportionalInteractionEnergy beta1 beta2 c ∧
      (proportionalInteractionEnergy beta1 beta2 c =
          proportionalInteractionEnergy beta1 beta2 1 ↔ c = 1)

theorem proportional_vacuum_minimum :
    ProportionalVacuumMinimum4D :=
  symmetric_point_unique_positive_global_minimizer

def ProportionalVacuumHessianPositive4D : Prop :=
  ∀ beta1 beta2 : ℝ,
    0 < beta1 →
    0 ≤ beta2 →
    0 < 2 * relativeShape beta1 beta2 1

theorem proportional_vacuum_hessian_positive :
    ProportionalVacuumHessianPositive4D :=
  symmetric_hessian_positive

def PTFlatVacuumConstraintNoGo4D : Prop :=
  ∀ (beta1 beta2 interactionScale planckPlusSq planckMinusSq : ℝ)
      (x : PhasePoint),
    0 < beta1 →
    0 ≤ beta2 →
    0 < interactionScale →
    0 < planckPlusSq →
    0 < planckMinusSq →
    0 < x.aPlus →
    0 < x.aMinus →
    plusConstraint
        (ptFlatParameters beta1 beta2 interactionScale planckPlusSq
          planckMinusSq) x = 0 →
    minusConstraint
        (ptFlatParameters beta1 beta2 interactionScale planckPlusSq
          planckMinusSq) x = 0 →
    x.aPlus = x.aMinus ∧
      x.pPlus = 0 ∧
      x.pMinus = 0 ∧
      primaryCovectorsDependent
        (plusDifferential
          (ptFlatParameters beta1 beta2 interactionScale planckPlusSq
            planckMinusSq) x)
        (minusDifferential
          (ptFlatParameters beta1 beta2 interactionScale planckPlusSq
            planckMinusSq) x)

theorem pt_flat_vacuum_constraint_no_go :
    PTFlatVacuumConstraintNoGo4D :=
  ptFlat_vacuum_FLRW_constraint_noGo

structure ProgramPReducedVacuumFrontierCertificate4D where
  proportionalMinimum : ProportionalVacuumMinimum4D
  proportionalHessianPositive : ProportionalVacuumHessianPositive4D
  vacuumConstraintNoGo : PTFlatVacuumConstraintNoGo4D
  sourcedConstraintFlatDirection : ReducedDustEqualEnergyWitness4D
  sourcedNoStrictEnergyIsolation :
    ¬ ReducedDustStrictEnergyIsolationAlongConstraintCurve4D
  effectiveSchemeFreedom :
    Nonempty ProgramPGlobalSchemeNoGoCertificate4D

def programPReducedVacuumFrontierCertificate4D :
    ProgramPReducedVacuumFrontierCertificate4D where
  proportionalMinimum := proportional_vacuum_minimum
  proportionalHessianPositive := proportional_vacuum_hessian_positive
  vacuumConstraintNoGo := pt_flat_vacuum_constraint_no_go
  sourcedConstraintFlatDirection := reduced_dust_equal_energy_witness
  sourcedNoStrictEnergyIsolation :=
    reduced_dust_no_strict_energy_isolation
  effectiveSchemeFreedom := global_scheme_frontier_gate

theorem global_vacuum_frontier_gate :
    Nonempty ProgramPReducedVacuumFrontierCertificate4D :=
  ⟨programPReducedVacuumFrontierCertificate4D⟩

/-- Explicit obligations still needed for terminal `VACUUM-GLOBAL-01`.
No inhabitant is constructed in this module. -/
structure ProgramPGlobalVacuumResidualContract4D
    extends
      P0EFTJanusProgramPGlobalStabilityFrontier4D.ProgramPGlobalStabilityResidualContract4D where
  renormalizedEffectiveActionFixed : Prop
  anomalyTrivializationDerived : Prop
  finitePartsFixedMicroscopically : Prop
  stationaryBranchesGloballyClassified : Prop
  uniqueVacuumModuloGauge : Prop
  vacuumHessianPositiveOnPhysicalQuotient : Prop

end P0EFTJanusProgramPGlobalVacuumFrontier4D
end JanusFormal
