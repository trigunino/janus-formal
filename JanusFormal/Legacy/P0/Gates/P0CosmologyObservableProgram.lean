import JanusFormal.Legacy.P0.Gates.P0ScalarVectorActionSpec

namespace JanusFormal
namespace P0CosmologyObservableProgram

open P0ScalarVectorActionSpec

set_option autoImplicit false

structure CosmologyObservableProgram where
  microTheory : FullSVTPredictionReadyCertificate
  microTheoryReady : predictionReady microTheory
  flrwAnsatzLifted : Prop
  modifiedFriedmannDerived : Prop
  effectiveDarkMatterMapDerived : Prop
  effectiveDarkEnergyMapDerived : Prop
  hubbleTensionObservableDerived : Prop
  earlyStructureGrowthDerived : Prop
  jwstEarlyGalaxyObservableDerived : Prop
  negativeLensingSignatureDerived : Prop
  primordialGWTransitionSignatureDerived : Prop
  likelihoodPipelineImplemented : Prop
  noExtraDarkParticlesPostulated : Prop

def flrwGateClosed (p : CosmologyObservableProgram) : Prop :=
  p.flrwAnsatzLifted /\ p.modifiedFriedmannDerived

def darkSectorGateClosed (p : CosmologyObservableProgram) : Prop :=
  p.effectiveDarkMatterMapDerived /\
  p.effectiveDarkEnergyMapDerived /\
  p.noExtraDarkParticlesPostulated

def hubbleGateClosed (p : CosmologyObservableProgram) : Prop :=
  p.modifiedFriedmannDerived /\ p.hubbleTensionObservableDerived

def structureGateClosed (p : CosmologyObservableProgram) : Prop :=
  p.earlyStructureGrowthDerived /\ p.jwstEarlyGalaxyObservableDerived

def falsifiableSignatureGateClosed (p : CosmologyObservableProgram) : Prop :=
  p.negativeLensingSignatureDerived /\
  p.primordialGWTransitionSignatureDerived

def observablePredictionReady (p : CosmologyObservableProgram) : Prop :=
  predictionReady p.microTheory /\
  flrwGateClosed p /\
  darkSectorGateClosed p /\
  hubbleGateClosed p /\
  structureGateClosed p /\
  falsifiableSignatureGateClosed p /\
  p.likelihoodPipelineImplemented

theorem cosmology_program_ready_from_all_gates
    (p : CosmologyObservableProgram)
    (hFlrw : flrwGateClosed p)
    (hDark : darkSectorGateClosed p)
    (hHubble : hubbleGateClosed p)
    (hStructure : structureGateClosed p)
    (hSignature : falsifiableSignatureGateClosed p)
    (hLikelihood : p.likelihoodPipelineImplemented) :
    observablePredictionReady p := by
  exact ⟨p.microTheoryReady, hFlrw, hDark, hHubble,
    hStructure, hSignature, hLikelihood⟩

theorem missing_friedmann_blocks_observable_prediction
    (p : CosmologyObservableProgram)
    (hMissing : Not p.modifiedFriedmannDerived) :
    Not (observablePredictionReady p) := by
  intro h
  exact hMissing h.right.left.right

theorem missing_hubble_map_blocks_observable_prediction
    (p : CosmologyObservableProgram)
    (hMissing : Not p.hubbleTensionObservableDerived) :
    Not (observablePredictionReady p) := by
  intro h
  exact hMissing h.right.right.right.left.right

theorem missing_falsifiable_signature_blocks_observable_prediction
    (p : CosmologyObservableProgram)
    (hMissing : Not p.negativeLensingSignatureDerived) :
    Not (observablePredictionReady p) := by
  intro h
  exact hMissing h.right.right.right.right.right.left.left

def canonicalMicroTheoryReady :
    FullSVTPredictionReadyCertificate :=
  canonicalPredictionReadyCertificate

theorem canonical_micro_theory_ready :
    predictionReady canonicalMicroTheoryReady := by
  exact canonical_prediction_ready

end P0CosmologyObservableProgram
end JanusFormal
