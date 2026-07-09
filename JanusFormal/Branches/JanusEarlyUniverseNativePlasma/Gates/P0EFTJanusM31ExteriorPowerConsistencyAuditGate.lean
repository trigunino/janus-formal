import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusM31TorsorCPTExteriorPowerCandidateGate

namespace JanusFormal
namespace P0EFTJanusM31ExteriorPowerConsistencyAuditGate

set_option autoImplicit false

structure M31ExteriorPowerConsistencyAuditGate where
  additive11Plus3Gives1001 : Prop
  cptLabelsAreDiscreteComponentsInM31 : Prop
  cptAsFermionicModesDerived : Prop
  pureTorsorExteriorGives330 : Prop
  cptSuperselectionFactorGives2640 : Prop
  legalM31ReadingMatches1001 : Prop

def additiveRouteLegal
    (g : M31ExteriorPowerConsistencyAuditGate) : Prop :=
  g.additive11Plus3Gives1001 /\
  g.cptAsFermionicModesDerived

def strictM31ExteriorAudit
    (g : M31ExteriorPowerConsistencyAuditGate) : Prop :=
  g.additive11Plus3Gives1001 /\
  g.cptLabelsAreDiscreteComponentsInM31 /\
  Not g.cptAsFermionicModesDerived /\
  g.pureTorsorExteriorGives330 /\
  g.cptSuperselectionFactorGives2640 /\
  Not g.legalM31ReadingMatches1001

theorem strict_M31_audit_blocks_additive_1001_selector
    (g : M31ExteriorPowerConsistencyAuditGate)
    (hAudit : strictM31ExteriorAudit g) :
    Not (additiveRouteLegal g) := by
  intro h
  exact hAudit.2.2.1 h.right

end P0EFTJanusM31ExteriorPowerConsistencyAuditGate
end JanusFormal
