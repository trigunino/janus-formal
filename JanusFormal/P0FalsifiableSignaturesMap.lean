import JanusFormal.P0LinearGrowthEarlyStructureMap

namespace JanusFormal
namespace P0FalsifiableSignaturesMap

open P0LinearGrowthEarlyStructureMap
open P0CosmologyObservableProgram

set_option autoImplicit false

structure FalsifiableSignaturesCertificate where
  growth : LinearGrowthEarlyStructureCertificate
  growthClosed : linearGrowthEarlyStructureClosed growth
  nullGeodesicBundleDeclared : Prop
  ricciSourceSeparated : Prop
  weylShearTracked : Prop
  angularDistanceEquationWritten : Prop
  observerSourceGaugeFixed : Prop
  gwTransferMatrixWritten : Prop
  gwFrequencyPhaseWritten : Prop
  gwModeMixingWritten : Prop
  gwBlueRedTiltCorrectionWritten : Prop

def falsifiableSignaturesClosed (c : FalsifiableSignaturesCertificate) : Prop :=
  c.nullGeodesicBundleDeclared /\
  c.ricciSourceSeparated /\
  c.weylShearTracked /\
  c.angularDistanceEquationWritten /\
  c.observerSourceGaugeFixed /\
  c.gwTransferMatrixWritten /\
  c.gwFrequencyPhaseWritten /\
  c.gwModeMixingWritten /\
  c.gwBlueRedTiltCorrectionWritten

def cosmologyProgramFromFalsifiableSignatures
    (c : FalsifiableSignaturesCertificate)
    (_h : falsifiableSignaturesClosed c) :
    CosmologyObservableProgram :=
  let base : CosmologyObservableProgram := cosmologyProgramFromGrowth c.growth c.growthClosed
  { base with
    negativeLensingSignatureDerived := True
    primordialGWTransitionSignatureDerived := True }

theorem falsifiable_signatures_gate_from_certificate
    (c : FalsifiableSignaturesCertificate)
    (h : falsifiableSignaturesClosed c) :
    falsifiableSignatureGateClosed (cosmologyProgramFromFalsifiableSignatures c h) := by
  exact And.intro trivial trivial

theorem observable_prediction_still_requires_likelihood
    (c : FalsifiableSignaturesCertificate)
    (h : falsifiableSignaturesClosed c) :
    Not (observablePredictionReady (cosmologyProgramFromFalsifiableSignatures c h)) := by
  intro hPred
  exact hPred.right.right.right.right.right.right

def sampleFalsifiableSignaturesCertificate : FalsifiableSignaturesCertificate :=
  { growth := sampleGrowthCertificate
    growthClosed := sample_growth_gate_closed
    nullGeodesicBundleDeclared := True
    ricciSourceSeparated := True
    weylShearTracked := True
    angularDistanceEquationWritten := True
    observerSourceGaugeFixed := True
    gwTransferMatrixWritten := True
    gwFrequencyPhaseWritten := True
    gwModeMixingWritten := True
    gwBlueRedTiltCorrectionWritten := True }

theorem sample_falsifiable_signatures_closed :
    falsifiableSignaturesClosed sampleFalsifiableSignaturesCertificate := by
  norm_num [falsifiableSignaturesClosed, sampleFalsifiableSignaturesCertificate]

theorem sample_falsifiable_signature_gate_closed :
    falsifiableSignatureGateClosed
      (cosmologyProgramFromFalsifiableSignatures
        sampleFalsifiableSignaturesCertificate
        sample_falsifiable_signatures_closed) := by
  exact falsifiable_signatures_gate_from_certificate
    sampleFalsifiableSignaturesCertificate
    sample_falsifiable_signatures_closed

theorem sample_pred_still_needs_likelihood :
    Not (observablePredictionReady
      (cosmologyProgramFromFalsifiableSignatures
        sampleFalsifiableSignaturesCertificate
        sample_falsifiable_signatures_closed)) := by
  exact
    observable_prediction_still_requires_likelihood
      sampleFalsifiableSignaturesCertificate
      sample_falsifiable_signatures_closed

end P0FalsifiableSignaturesMap
end JanusFormal
