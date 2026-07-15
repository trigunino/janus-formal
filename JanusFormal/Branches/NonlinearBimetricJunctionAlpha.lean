/-
Nonlinear two-metric action and finite PT-junction route.

This branch formalizes the variational architecture, common-action
integrability, diagonal Noether exchange, the relative kinetic-sign obstruction,
a classified positive-kinetic PT-symmetric proportional branch, the
massless/massive mode decomposition, signed PT matter charges, quasi-local
charge pairing and a reciprocal covariant interaction candidate. It derives
relational bridge laws but does not generate the independent quantum charge
scale.
-/

import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusTwoMetricFirstVariation
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusTwoSheetActionNoGo
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusBimetricActionIntegrability
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusDiagonalNoetherExchange
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusRelativeKineticSignNoGo
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTQuasilocalChargePairing
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusReciprocalBimetricPotential
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTSymmetricFlatBimetricBranch
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTFlatCoefficientClassification
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPositiveKineticMassEigenmodes
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusSignedMatterChargeNewtonianLimit
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
  relativeKineticSignObstructionAudited : Prop
  ptFlatCoefficientsClassified : Prop
  positiveKineticPTBranchConstructed : Prop
  masslessAndMassiveModesDerived : Prop
  signedMatterChargeLimitDerived : Prop
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
  s.relativeKineticSignObstructionAudited /\
  s.ptFlatCoefficientsClassified /\
  s.positiveKineticPTBranchConstructed /\
  s.masslessAndMassiveModesDerived /\
  s.signedMatterChargeLimitDerived /\
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
    (_hClassical : classicalBimetricJunctionClosed s)
    (hMissing : Not s.absoluteChargeScaleDerived) :
    Not (fullBimetricAlphaClosure s) := by
  intro h
  exact hMissing h.2.1

end JanusNonlinearBimetricJunctionAlpha
end JanusFormal
