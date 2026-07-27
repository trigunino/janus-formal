import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedFLRWPrimaryLapseDerivatives
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedFLRWConstraintRankOpenFamily
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterCurvatureFLRWConstraintBranch
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusADMBDConstraintCount

/-!
# Exact reduced ADM frontier for Program P

The Candidate-A FLRW reduction has an actual Legendre transform, primary
lapse derivatives, a canonical secondary bracket, preservation equations and
a nonempty open rank-three locus.  A positive-dust witness also realizes the
three constraints and fixes the lapse ratio.

This is not `ADM-GLOBAL-01`: the covariant action has not yet been reduced
with both shifts and spatial derivatives, and no functional Dirac algebra or
global Boulware--Deser exclusion is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalADMFrontier4D

set_option autoImplicit false

open P0EFTJanusReducedFLRWSecondaryConstraint
open P0EFTJanusReducedFLRWLegendreBridge

def ReducedADMLegendreClosure4D : Prop :=
  ∀ (parameters : ReducedParameters) (x : PhasePoint)
      (lapsePlus lapseMinus : ℝ),
    parameters.planckPlusSq ≠ 0 →
    parameters.planckMinusSq ≠ 0 →
    x.aPlus ≠ 0 →
    x.aMinus ≠ 0 →
    reducedLegendreTransform parameters x lapsePlus lapseMinus =
      lapsePlus * plusConstraint parameters x +
        lapseMinus * minusConstraint parameters x

theorem reduced_adm_legendre_closure :
    ReducedADMLegendreClosure4D := by
  intro parameters x lapsePlus lapseMinus
    hPlanckPlus hPlanckMinus haPlus haMinus
  exact
    P0EFTJanusReducedFLRWPrimaryLapseDerivatives.reducedLegendreTransform_eq_lapse_constraints_for_all_lapses
        parameters x lapsePlus lapseMinus hPlanckPlus hPlanckMinus
        haPlus haMinus

def ReducedADMPrimaryClosure4D : Prop :=
  ∀ (parameters : ReducedParameters) (x : PhasePoint)
      (lapsePlus lapseMinus : ℝ),
    parameters.planckPlusSq ≠ 0 →
    parameters.planckMinusSq ≠ 0 →
    x.aPlus ≠ 0 →
    x.aMinus ≠ 0 →
    HasDerivAt
        (fun variedLapsePlus =>
          reducedLegendreTransform parameters x variedLapsePlus lapseMinus)
        (plusConstraint parameters x) lapsePlus ∧
      HasDerivAt
        (fun variedLapseMinus =>
          reducedLegendreTransform parameters x lapsePlus variedLapseMinus)
        (minusConstraint parameters x) lapseMinus

theorem reduced_adm_primary_closure :
    ReducedADMPrimaryClosure4D :=
  P0EFTJanusReducedFLRWPrimaryLapseDerivatives.reducedFLRW_primary_lapse_derivatives_from_same_action

def ReducedADMSecondaryClosure4D : Prop :=
  ∀ (parameters : ReducedParameters) (x : PhasePoint),
    parameters.planckPlusSq ≠ 0 →
    parameters.planckMinusSq ≠ 0 →
    x.aPlus ≠ 0 →
    x.aMinus ≠ 0 →
    canonicalPoisson (plusDifferential parameters x)
        (minusDifferential parameters x) =
        secondaryConstraint parameters x ∧
      ∀ lapsePlus lapseMinus : ℝ,
        lapsePlus ≠ 0 →
        lapseMinus ≠ 0 →
        canonicalPoisson (plusDifferential parameters x)
            (hamiltonianDifferential lapsePlus lapseMinus parameters x) = 0 →
        canonicalPoisson (minusDifferential parameters x)
            (hamiltonianDifferential lapsePlus lapseMinus parameters x) = 0 →
        secondaryConstraint parameters x = 0

theorem reduced_adm_secondary_closure :
    ReducedADMSecondaryClosure4D := by
  intro parameters x hPlanckPlus hPlanckMinus haPlus haMinus
  constructor
  · exact primary_poisson_bracket_factorization parameters x
      hPlanckPlus hPlanckMinus haPlus haMinus
  · intro lapsePlus lapseMinus hLapsePlus hLapseMinus
      hPreservePlus hPreserveMinus
    exact secondary_constraint_of_primary_preservation
      lapsePlus lapseMinus parameters x hLapsePlus hLapseMinus
      hPlanckPlus hPlanckMinus haPlus haMinus
      hPreservePlus hPreserveMinus

def ReducedADMRankOpenClosure4D : Prop :=
  let regular :=
    P0EFTJanusReducedFLRWConstraintRankOpenFamily.ConstraintRankRegularWitnessParameters
  IsOpen regular ∧
    regular.Nonempty ∧
    (0 : ℝ) ∈ regular ∧
    ∀ parameter ∈ regular,
      P0EFTJanusReducedFLRWConstraintRankOpenFamily.ConstraintDifferentialsIndependent
          P0EFTJanusReducedFLRWSecondaryConstraint.witnessParameters
          (P0EFTJanusReducedFLRWConstraintRankOpenFamily.constraintRankWitnessLine
            parameter)

theorem reduced_adm_rank_open_closure :
    ReducedADMRankOpenClosure4D := by
  simpa [ReducedADMRankOpenClosure4D] using
    P0EFTJanusReducedFLRWConstraintRankOpenFamily.reducedFLRWConstraintRankOpenFamily_closure

def ReducedADMMatterWitness4D : Prop :=
  let parameters :=
    P0EFTJanusMatterCurvatureFLRWConstraintBranch.witnessParameters
  let point :=
    P0EFTJanusMatterCurvatureFLRWConstraintBranch.witnessPoint
  (0 < point.aPlus ∧ 0 < point.aMinus ∧
      0 < parameters.dustPlus ∧ 0 < parameters.dustMinus) ∧
    (P0EFTJanusMatterCurvatureFLRWConstraintBranch.extendedPlusConstraint
        parameters point = 0 ∧
      P0EFTJanusMatterCurvatureFLRWConstraintBranch.extendedMinusConstraint
        parameters point = 0) ∧
    (potentialFactor parameters.base point = 2 ∧
      secondaryConstraint parameters.base point = 0) ∧
    P0EFTJanusMatterCurvatureFLRWConstraintBranch.extendedConstraintJacobianMinor
      parameters point ≠ 0 ∧
    ∀ lapsePlus lapseMinus : ℝ,
      canonicalPoisson
          (secondaryDifferential parameters.base point)
          (P0EFTJanusMatterCurvatureFLRWConstraintBranch.extendedHamiltonianDifferential
            lapsePlus lapseMinus
              parameters point) = 0 →
        lapseMinus = lapsePlus

theorem reduced_adm_matter_witness :
    ReducedADMMatterWitness4D := by
  exact
    ⟨P0EFTJanusMatterCurvatureFLRWConstraintBranch.witness_has_positive_scales_and_dust,
      P0EFTJanusMatterCurvatureFLRWConstraintBranch.witness_lies_on_both_primary_constraints,
      P0EFTJanusMatterCurvatureFLRWConstraintBranch.witness_lies_on_dynamical_secondary_branch,
      P0EFTJanusMatterCurvatureFLRWConstraintBranch.witness_constraintJacobianMinor_nonzero,
      P0EFTJanusMatterCurvatureFLRWConstraintBranch.witness_secondary_preservation_fixes_lapse_ratio⟩

def ConditionalHRCountTarget4D : Prop :=
  P0EFTJanusADMBDConstraintCount.physicalPhaseDimension 24 4 2 = 14 ∧
    P0EFTJanusADMBDConstraintCount.physicalPhaseDimension 24 4 2 / 2 = 7

theorem conditional_hr_count_target :
    ConditionalHRCountTarget4D :=
  ⟨P0EFTJanusADMBDConstraintCount.hr_bimetric_phase_dimension,
    P0EFTJanusADMBDConstraintCount.hr_bimetric_configuration_dof⟩

/-- Everything proved without importing the missing continuum ADM bridge. -/
structure ProgramPReducedADMFrontierCertificate4D where
  legendre : ReducedADMLegendreClosure4D
  primary : ReducedADMPrimaryClosure4D
  secondary : ReducedADMSecondaryClosure4D
  rankOpen : ReducedADMRankOpenClosure4D
  matterWitness : ReducedADMMatterWitness4D
  conditionalCountTarget : ConditionalHRCountTarget4D

def programPReducedADMFrontierCertificate4D :
    ProgramPReducedADMFrontierCertificate4D where
  legendre := reduced_adm_legendre_closure
  primary := reduced_adm_primary_closure
  secondary := reduced_adm_secondary_closure
  rankOpen := reduced_adm_rank_open_closure
  matterWitness := reduced_adm_matter_witness
  conditionalCountTarget := conditional_hr_count_target

theorem global_adm_frontier_gate :
    Nonempty ProgramPReducedADMFrontierCertificate4D :=
  ⟨programPReducedADMFrontierCertificate4D⟩

/-- Explicit obligations still needed for terminal `ADM-GLOBAL-01`.
No inhabitant is constructed in this module. -/
structure ProgramPGlobalADMResidualContract4D where
  covariantActionADMReductionDerived : Prop
  bothShiftRedefinitionsControlled : Prop
  functionalPoissonDiracAlgebraDerived : Prop
  globalPrimaryConstraintsDerived : Prop
  independentGlobalSecondaryConstraintDerived : Prop
  genericConstraintRankProved : Prop
  boundaryHamiltonianCompatible : Prop
  matterConstraintClosureProved : Prop
  boulwareDeserModeRemoved : Prop

end P0EFTJanusProgramPGlobalADMFrontier4D
end JanusFormal
