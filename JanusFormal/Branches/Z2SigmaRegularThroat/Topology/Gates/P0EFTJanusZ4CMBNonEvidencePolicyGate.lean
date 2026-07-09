namespace JanusFormal
namespace P0EFTJanusZ4CMBNonEvidencePolicyGate

set_option autoImplicit false

structure Z4CMBNonEvidencePolicy where
  z4CMBAttemptsKeptForDiagnostics : Prop
  cyclicZ4NotUsedByActiveGeometry : Prop
  noMonodromyProofAvailable : Prop
  noNewZ4PhysicsAllowed : Prop
  z4ModulesDiagnosticOnly : Prop
  activeCoreIsZ2TunnelSigma : Prop

def z4CMBMarkedNonEvidence (p : Z4CMBNonEvidencePolicy) : Prop :=
  p.z4CMBAttemptsKeptForDiagnostics /\
  p.cyclicZ4NotUsedByActiveGeometry /\
  p.noMonodromyProofAvailable /\
  p.noNewZ4PhysicsAllowed /\
  p.z4ModulesDiagnosticOnly /\
  p.activeCoreIsZ2TunnelSigma

theorem z4_cmb_non_evidence_policy_blocks_active_geometry
    (p : Z4CMBNonEvidencePolicy)
    (h : z4CMBMarkedNonEvidence p) :
    p.z4ModulesDiagnosticOnly /\ p.activeCoreIsZ2TunnelSigma := by
  exact And.intro h.2.2.2.2.1 h.2.2.2.2.2

end P0EFTJanusZ4CMBNonEvidencePolicyGate
end JanusFormal
