/-
Program P.F: compatibility geometry, Helmholtz reciprocity and Noether identities.

The original speculative implication

  Gauss--Codazzi--Ricci--Bianchi => Helmholtz

is false without an additional variational pairing.  The corrected bridge is:

1. regular local natural data reduce locally to an equivariant finite-jet map;
2. geometric compatibility defines a constrained invariant map `K` and its
   linearization `J`;
3. a self-adjoint target pairing/Hessian `H` pulls back to `J^T H J`;
4. this pullback is formally self-adjoint and therefore satisfies the quadratic
   Helmholtz condition;
5. if `K` is gauge invariant (`K R = 0`), the same pulled-back Hessian satisfies
   the linearized Noether identity;
6. for nonlinear `K`, the formula `J^T H J` is the complete second variation
   only at a target critical point; off shell there is an extra gradient-times-
   second-jet term.
-/

import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCorrectedJetUniversality
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompatibleJetPullbackHelmholtz
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNonlinearJetSecondVariation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusInvariantMapNoetherHelmholtz
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaussCodazziHelmholtzBridge
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompatibilityBridgeHierarchy

namespace JanusFormal
namespace JanusFundamentalGeometryPFCompatibilityHelmholtz

set_option autoImplicit false

structure ProgramStatus where
  correctedFiniteJetTheoremFormalized : Prop
  smoothCovariantRatherThanPolynomialStatementUsed : Prop
  ellipticitySeparatedFromNaturality : Prop
  compatibleJetMapConstructed : Prop
  geometryAloneHelmholtzCounterexampleFormalized : Prop
  selfAdjointTargetPairingConstructed : Prop
  pullbackHessianFormulaProved : Prop
  pullbackHelmholtzProved : Prop
  pulledBackActionIdentityProved : Prop
  nonlinearSecondVariationFormulaProved : Prop
  criticalPointRemovesSecondJetCorrectionProved : Prop
  gaugeInvariantMapConstructed : Prop
  noetherIdentityDerived : Prop
  helmholtzAndNoetherIndependenceProved : Prop
  suppliedAbstractCompatibilityConsequencesProved : Prop
  actualGaussCodazziJetComplexConstructed : Prop
  actualJanusTargetPairingDerived : Prop
  globalVariationalPrimitiveConstructed : Prop

/-- Algebraic/local P.F foundation. -/
def programPFFoundationClosed (s : ProgramStatus) : Prop :=
  s.correctedFiniteJetTheoremFormalized /\
  s.smoothCovariantRatherThanPolynomialStatementUsed /\
  s.ellipticitySeparatedFromNaturality /\
  s.compatibleJetMapConstructed /\
  s.geometryAloneHelmholtzCounterexampleFormalized /\
  s.selfAdjointTargetPairingConstructed /\
  s.pullbackHessianFormulaProved /\
  s.pullbackHelmholtzProved /\
  s.pulledBackActionIdentityProved /\
  s.nonlinearSecondVariationFormulaProved /\
  s.criticalPointRemovesSecondJetCorrectionProved /\
  s.gaugeInvariantMapConstructed /\
  s.noetherIdentityDerived /\
  s.helmholtzAndNoetherIndependenceProved /\
  s.suppliedAbstractCompatibilityConsequencesProved

/-- Full geometric/analytic P.F closure. -/
def fullProgramPFClosure (s : ProgramStatus) : Prop :=
  programPFFoundationClosed s /\
  s.actualGaussCodazziJetComplexConstructed /\
  s.actualJanusTargetPairingDerived /\
  s.globalVariationalPrimitiveConstructed

/-- Geometry alone cannot close P.F because the target pairing is independent. -/
theorem missing_target_pairing_blocks_full_pf
    (s : ProgramStatus)
    (hMissing : Not s.actualJanusTargetPairingDerived) :
    Not (fullProgramPFClosure s) := by
  intro hClosed
  exact hMissing hClosed.2.2.1

/-- The abstract matrix bridge does not substitute for the actual Gauss--Codazzi jet complex. -/
theorem missing_actual_compatibility_complex_blocks_full_pf
    (s : ProgramStatus)
    (hMissing : Not s.actualGaussCodazziJetComplexConstructed) :
    Not (fullProgramPFClosure s) := by
  intro hClosed
  exact hMissing hClosed.2.1

/-- Local Hessian integrability does not by itself construct a global action. -/
theorem missing_global_primitive_blocks_full_pf
    (s : ProgramStatus)
    (hMissing : Not s.globalVariationalPrimitiveConstructed) :
    Not (fullProgramPFClosure s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2

/--
Final corrected P.F theorem architecture.  This is a positive theorem schema,
not yet a proof that the concrete Janus Gauss--Codazzi complex supplies the
required `K`, `J` and `H` globally.
-/
structure PFVerdict where
  finiteJetReductionConditional : Prop
  compatibilityDefinesJetLocus : Prop
  compatibilityAloneNotHelmholtz : Prop
  selfAdjointPairingPullbackIsHelmholtz : Prop
  invariantMapPullbackSatisfiesNoether : Prop
  noetherAndHelmholtzIndependentInGeneral : Prop
  nonlinearFormulaRequiresCriticalPoint : Prop
  concreteJanusComplexStillOpen : Prop


def pfVerdictClosed (s : PFVerdict) : Prop :=
  s.finiteJetReductionConditional /\
  s.compatibilityDefinesJetLocus /\
  s.compatibilityAloneNotHelmholtz /\
  s.selfAdjointPairingPullbackIsHelmholtz /\
  s.invariantMapPullbackSatisfiesNoether /\
  s.noetherAndHelmholtzIndependentInGeneral /\
  s.nonlinearFormulaRequiresCriticalPoint /\
  s.concreteJanusComplexStillOpen

end JanusFundamentalGeometryPFCompatibilityHelmholtz
end JanusFormal
