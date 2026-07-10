/-
Nonlinear two-metric action and finite PT-junction route.

This branch formalizes the variational architecture, cross-source integrability,
diagonal Noether exchange, PT-odd quasi-local charge pairing and a reciprocal
covariant interaction candidate.  It derives relational bridge laws but does
not generate the independent quantum charge scale.
-/

import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusTwoMetricFirstVariation
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusBimetricActionIntegrability
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusDiagonalNoetherExchange
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTQuasilocalChargePairing
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusReciprocalBimetricPotential
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusMisnerSharpPTBridge
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusFiniteSphereBridgeMatching

namespace JanusFormal
namespace JanusNonlinearBimetricJunctionAlpha

set_option autoImplicit false

structure ProgramStatus where
  twoMetricBulkActionDefined : Prop
  allBoundaryTermsDefined : Prop
  commonCrossInteractionConstructed : Prop
  mixedVariationIntegrabilityProved : Prop
  diagonalNoetherIdentityProved : Prop
  nonlinearConstraintAlgebraClosed : Prop
  stableLocalGRBranchProved : Prop
  ptOddQuasilocalChargeDerived : Prop
  misnerSharpFiniteSphereReductionProved : Prop
  nullJunctionConditionsDerived : Prop
  bridgeMassReversalDerived : Prop
  alphaEqualsBridgeRadiusDerived : Prop
  noObservedScaleImported : Prop
  absoluteChargeScaleDerived : Prop
  absoluteAlphaScaleClosed : Prop


def classicalBimetricJunctionClosed (s : ProgramStatus) : Prop :=
  s.twoMetricBulkActionDefined /\
  s.allBoundaryTermsDefined /\
  s.commonCrossInteractionConstructed /\
  s.mixedVariationIntegrabilityProved /\
  s.diagonalNoetherIdentityProved /\
  s.nonlinearConstraintAlgebraClosed /\
  s.stableLocalGRBranchProved /\
  s.ptOddQuasilocalChargeDerived /\
  s.misnerSharpFiniteSphereReductionProved /\
  s.nullJunctionConditionsDerived /\
  s.bridgeMassReversalDerived /\
  s.alphaEqualsBridgeRadiusDerived /\
  s.noObservedScaleImported


def fullBimetricAlphaClosure (s : ProgramStatus) : Prop :=
  classicalBimetricJunctionClosed s /\
  s.absoluteChargeScaleDerived /\
  s.absoluteAlphaScaleClosed


theorem classical_action_without_charge_scale_does_not_close_absolute_alpha
    (s : ProgramStatus)
    (hClassical : classicalBimetricJunctionClosed s)
    (hMissing : Not s.absoluteChargeScaleDerived) :
    Not (fullBimetricAlphaClosure s) := by
  intro h
  exact hMissing h.2.1

end JanusNonlinearBimetricJunctionAlpha
end JanusFormal
