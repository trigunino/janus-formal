import JanusFormal.P0EFTJanusZ2SigmaBAOActiveReadinessGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOOfficialChi2Gate

set_option autoImplicit false

structure Z2SigmaBAOOfficialChi2Gate where
  activeManifestAvailable : Prop
  manifestActiveCoreZ2Sigma : Prop
  manifestSourceActiveDerived : Prop
  compressedPlanckLCDMRdRejected : Prop
  archivedZ4ReuseRejected : Prop
  phenomenologicalHolstBAOScanRejected : Prop
  inputProvenanceVerified : Prop
  sourceComponentManifestHashVerified : Prop
  predictionVectorComputed : Prop
  chi2EvaluatedAgainstDESIDR2 : Prop
  officialBAOEvaluation : Prop
  baoOfficialChi2GatePassed : Prop

def officialManifestValid
    (g : Z2SigmaBAOOfficialChi2Gate) : Prop :=
  g.activeManifestAvailable /\
  g.manifestActiveCoreZ2Sigma /\
  g.manifestSourceActiveDerived /\
  g.compressedPlanckLCDMRdRejected /\
  g.archivedZ4ReuseRejected /\
  g.phenomenologicalHolstBAOScanRejected /\
  g.inputProvenanceVerified /\
  g.sourceComponentManifestHashVerified

def officialChi2Closed
    (g : Z2SigmaBAOOfficialChi2Gate) : Prop :=
  officialManifestValid g /\
  g.predictionVectorComputed /\
  g.chi2EvaluatedAgainstDESIDR2 /\
  g.officialBAOEvaluation

theorem official_chi2_requires_valid_manifest
    (g : Z2SigmaBAOOfficialChi2Gate)
    (hGate : g.baoOfficialChi2GatePassed)
    (hImplies : g.baoOfficialChi2GatePassed -> officialChi2Closed g) :
    officialManifestValid g := by
  exact (hImplies hGate).1

theorem official_chi2_requires_desi_chi2
    (g : Z2SigmaBAOOfficialChi2Gate)
    (hClosed : officialChi2Closed g) :
    g.chi2EvaluatedAgainstDESIDR2 := by
  exact hClosed.2.2.1

end P0EFTJanusZ2SigmaBAOOfficialChi2Gate
end JanusFormal
