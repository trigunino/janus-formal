/-
Experimental branch head: RP4 twisted flux, finite PT bridge and LL-brane
alpha-scale route.

The branch now proves the relational/conditional algebra and isolates the last
physical inputs.  It does not promote an absolute no-fit value of alpha.
-/

import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusRP4TwistedFluxPrimitiveSelector
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusRP4FourFormScaleAudit
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusExactCoshNormalizationAudit
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusSpatialCurvatureMatchingNoGo
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusFiniteSphereBridgeMatching
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusLLBraneAuxiliaryFluxClosure
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusLLAuxiliaryBundleCompactnessGate
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusPrimitiveChargeAreaScaleLaw
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusBulkWorldvolumeFluxSeparation
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusConditionalAlphaSpectrumClosure
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusDustCurrentThreeFormBridge
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusScaleCovarianceNoGo
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusCasimirPlanckScaleAudit
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusBounceThroatScaleMatching

namespace JanusFormal
namespace JanusRP4TwistedFourFormAlpha

set_option autoImplicit false

structure ProgramStatus where
  sourceNormalizationAudited : Prop
  primitiveTwistedFluxSelectorProved : Prop
  rp4PinPlusCompatibilityAudited : Prop
  wholeSliceRoundMatchingNoGoProved : Prop
  finiteSphereConditionalAlgebraClosed : Prop
  llAuxiliaryInvariantOneHalfProved : Prop
  conditionalAlphaSpectrumClosed : Prop
  bulkWorldvolumeFluxSeparationAudited : Prop
  llAuxiliaryCompactBundleDerived : Prop
  signedBimetricJunctionDerived : Prop
  llChargeUnitMagnitudeDerivedNoFit : Prop
  hierarchyMechanismDerived : Prop
  absoluteAlphaScaleClosedNoFit : Prop


def mathematicalAdvanceClosed (s : ProgramStatus) : Prop :=
  s.sourceNormalizationAudited /\
  s.primitiveTwistedFluxSelectorProved /\
  s.rp4PinPlusCompatibilityAudited /\
  s.wholeSliceRoundMatchingNoGoProved /\
  s.finiteSphereConditionalAlgebraClosed /\
  s.llAuxiliaryInvariantOneHalfProved /\
  s.conditionalAlphaSpectrumClosed /\
  s.bulkWorldvolumeFluxSeparationAudited


def honestFrontier (s : ProgramStatus) : Prop :=
  mathematicalAdvanceClosed s /\
  Not s.llAuxiliaryCompactBundleDerived /\
  Not s.signedBimetricJunctionDerived /\
  Not s.llChargeUnitMagnitudeDerivedNoFit /\
  Not s.hierarchyMechanismDerived /\
  Not s.absoluteAlphaScaleClosedNoFit


theorem current_advance_does_not_claim_absolute_alpha_closure
    (s : ProgramStatus)
    (h : honestFrontier s) :
    Not s.absoluteAlphaScaleClosedNoFit := by
  rcases h with ⟨_, _, _, _, _, hNotClosed⟩
  exact hNotClosed

end JanusRP4TwistedFourFormAlpha
end JanusFormal
