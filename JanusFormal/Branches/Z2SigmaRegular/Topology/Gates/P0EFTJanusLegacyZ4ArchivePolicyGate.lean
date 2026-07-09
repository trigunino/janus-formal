namespace JanusFormal
namespace P0EFTJanusLegacyZ4ArchivePolicyGate

set_option autoImplicit false

structure LegacyZ4ArchivePolicy where
  oldZ4CMBGatesPreservedForHistory : Prop
  cyclicZ4NotUsedByActiveGeometry : Prop
  noMonodromyProofAvailable : Prop
  noNewZ4PhysicsAllowed : Prop
  z4ModulesDiagnosticOnly : Prop
  activeCoreIsZ2TunnelSigma : Prop

def legacyZ4Archived (p : LegacyZ4ArchivePolicy) : Prop :=
  p.oldZ4CMBGatesPreservedForHistory /\
  p.cyclicZ4NotUsedByActiveGeometry /\
  p.noMonodromyProofAvailable /\
  p.noNewZ4PhysicsAllowed /\
  p.z4ModulesDiagnosticOnly /\
  p.activeCoreIsZ2TunnelSigma

theorem archived_z4_cannot_promote_active_geometry
    (p : LegacyZ4ArchivePolicy)
    (h : legacyZ4Archived p) :
    p.z4ModulesDiagnosticOnly /\ p.activeCoreIsZ2TunnelSigma := by
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩

end P0EFTJanusLegacyZ4ArchivePolicyGate
end JanusFormal
