/-
Program P: select or reconstruct the Janus action.

The branch separates three routes:

* P-A: a relative universal property for an action class, with bulk on-shell
  reduction as its strongest concrete realization;
* P-B: anomaly cancellation as a discrete selector and consistency filter;
* P-C: the inverse problem of the calculus of variations, using Helmholtz
  conditions to reconstruct a Lagrangian from its Euler--Lagrange/Hessian data.

The entry no-go proves that an L2, symplectic or Kähler-like geometry on moduli
cannot select a scalar functional by itself.
-/

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusModuliGeometryNoGo
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusUniversalActionProperty
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusAnomalySelection
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusHessianHelmholtzReconstruction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBulkUniversalHelmholtzSynthesis

namespace JanusFormal
namespace JanusFundamentalGeometryPVariationalPrinciple

set_option autoImplicit false

structure ProgramStatus where
  moduliMetricNoGoProved : Prop
  moduliSymplecticNoGoProved : Prop
  kahlerGeometryNotSufficientProved : Prop
  paAffineHessianAmbiguityProved : Prop
  paRelativeUniversalSpecificationConstructed : Prop
  paUniqueExistenceRelativeToSpecificationProved : Prop
  paBulkOnShellReductionConstructed : Prop
  paDirichletToNeumannOrSchurHessianDerived : Prop
  paBoundaryActionUniqueRelativeToParentProved : Prop
  pbPTAnomalyCancellationProved : Prop
  pbParityEvenFreedomProved : Prop
  pbTrivializationFreedomProved : Prop
  pbDiscreteMultiplicitySelectorDerived : Prop
  pcFormalSelfAdjointnessNecessaryProved : Prop
  pcQuadraticHelmholtzIffProved : Prop
  pcAffineReconstructionAmbiguityProved : Prop
  pcPTNormalizedUniqueReconstructionProved : Prop
  invariantLocalFunctionalBasisClassified : Prop
  fullEulerLagrangeOperatorDerived : Prop
  nonlinearHelmholtzConditionsProved : Prop
  variationalBicomplexObstructionVanishing : Prop
  nullLagrangiansAndBoundaryTermsClassified : Prop
  anomalyConstraintsApplied : Prop
  parentBulkOrMicroscopicSelectionPrincipleDerived : Prop
  actionNormalizationDerived : Prop
  finiteCountertermsFixedMicroscopically : Prop
  globalActionClassReconstructed : Prop
  hessianMatchesNaturalFredholmFamily : Prop
  uniqueStableVacuumDerived : Prop
  absoluteScaleDerivedNoFit : Prop

/-- Algebraic and logical Program-P foundation. -/
def programPFoundationClosed (s : ProgramStatus) : Prop :=
  s.moduliMetricNoGoProved /\
  s.moduliSymplecticNoGoProved /\
  s.kahlerGeometryNotSufficientProved /\
  s.paAffineHessianAmbiguityProved /\
  s.paRelativeUniversalSpecificationConstructed /\
  s.paUniqueExistenceRelativeToSpecificationProved /\
  s.paBulkOnShellReductionConstructed /\
  s.paDirichletToNeumannOrSchurHessianDerived /\
  s.paBoundaryActionUniqueRelativeToParentProved /\
  s.pbPTAnomalyCancellationProved /\
  s.pbParityEvenFreedomProved /\
  s.pbTrivializationFreedomProved /\
  s.pbDiscreteMultiplicitySelectorDerived /\
  s.pcFormalSelfAdjointnessNecessaryProved /\
  s.pcQuadraticHelmholtzIffProved /\
  s.pcAffineReconstructionAmbiguityProved /\
  s.pcPTNormalizedUniqueReconstructionProved

/-- Nonlinear variational reconstruction. -/
def nonlinearReconstructionClosed (s : ProgramStatus) : Prop :=
  s.invariantLocalFunctionalBasisClassified /\
  s.fullEulerLagrangeOperatorDerived /\
  s.nonlinearHelmholtzConditionsProved /\
  s.variationalBicomplexObstructionVanishing /\
  s.nullLagrangiansAndBoundaryTermsClassified /\
  s.anomalyConstraintsApplied /\
  s.parentBulkOrMicroscopicSelectionPrincipleDerived /\
  s.actionNormalizationDerived /\
  s.finiteCountertermsFixedMicroscopically /\
  s.globalActionClassReconstructed /\
  s.hessianMatchesNaturalFredholmFamily

/-- Predictive physical closure. -/
def fullProgramPClosure (s : ProgramStatus) : Prop :=
  programPFoundationClosed s /\
  nonlinearReconstructionClosed s /\
  s.uniqueStableVacuumDerived /\
  s.absoluteScaleDerivedNoFit

/-- P-A alone is only relative: without a parent or microscopic selector it cannot close. -/
theorem missing_parent_selection_blocks_full_program_p
    (s : ProgramStatus)
    (hMissing : Not s.parentBulkOrMicroscopicSelectionPrincipleDerived) :
    Not (fullProgramPClosure s) := by
  intro hClosed
  rcases hClosed with ⟨_, hNonlinear, _, _⟩
  rcases hNonlinear with ⟨_, _, _, _, _, _, hParent, _⟩
  exact hMissing hParent

/-- P-B anomaly cancellation cannot replace parity-even Euler--Lagrange dynamics. -/
theorem missing_euler_lagrange_operator_blocks_full_program_p
    (s : ProgramStatus)
    (hMissing : Not s.fullEulerLagrangeOperatorDerived) :
    Not (fullProgramPClosure s) := by
  intro hClosed
  rcases hClosed with ⟨_, hNonlinear, _, _⟩
  exact hMissing hNonlinear.2.1

/-- P-C requires the nonlinear Helmholtz theorem, not merely a symmetric quadratic proxy. -/
theorem missing_nonlinear_helmholtz_blocks_full_program_p
    (s : ProgramStatus)
    (hMissing : Not s.nonlinearHelmholtzConditionsProved) :
    Not (fullProgramPClosure s) := by
  intro hClosed
  rcases hClosed with ⟨_, hNonlinear, _, _⟩
  exact hMissing hNonlinear.2.2.1

/-- Scheme-independent prediction requires a microscopic finite-part law. -/
theorem missing_finite_counterterm_law_blocks_full_program_p
    (s : ProgramStatus)
    (hMissing : Not s.finiteCountertermsFixedMicroscopically) :
    Not (fullProgramPClosure s) := by
  intro hClosed
  rcases hClosed with ⟨_, hNonlinear, _, _⟩
  rcases hNonlinear with ⟨_, _, _, _, _, _, _, _, hCounterterm, _⟩
  exact hMissing hCounterterm

/--
Program-P verdict:

* P-A can characterize a unique normalized action only relative to already
  specified Hessian/critical/value data; the parent-bulk on-shell action is the
  strongest non-tautological realization currently available;
* P-B can select discrete anomaly arithmetic but leaves parity-even and finite
  data free;
* P-C is the mathematically strongest inverse route: a global action class can
  be reconstructed from a local Euler--Lagrange family only after the
  Helmholtz and variational-cohomology obstructions vanish.
-/
structure ProgramPVerdict where
  moduliGeometryAloneInsufficient : Prop
  universalPropertyRelativeNotAbsolute : Prop
  bulkOnShellActionCanonicalRelativeToParent : Prop
  anomalyCancellationConstraintNotFullSelection : Prop
  helmholtzRouteNecessaryForInverseProblem : Prop
  ptAndNormalizationRemoveAffineAmbiguity : Prop
  parentOrMicroscopicPrincipleStillRequired : Prop
  finiteRenormalizationStillRequired : Prop


def programPVerdictClosed (s : ProgramPVerdict) : Prop :=
  s.moduliGeometryAloneInsufficient /\
  s.universalPropertyRelativeNotAbsolute /\
  s.bulkOnShellActionCanonicalRelativeToParent /\
  s.anomalyCancellationConstraintNotFullSelection /\
  s.helmholtzRouteNecessaryForInverseProblem /\
  s.ptAndNormalizationRemoveAffineAmbiguity /\
  s.parentOrMicroscopicPrincipleStillRequired /\
  s.finiteRenormalizationStillRequired

end JanusFundamentalGeometryPVariationalPrinciple
end JanusFormal
