namespace JanusFormal
namespace P0EFTJanusZ2SigmaFlowTangencyFromEmbeddingVelocityGate

set_option autoImplicit false

structure FlowTangencyFromEmbeddingVelocityGate where
  metricOnSigmaInputsReady : Prop
  fourVelocityOnSigmaInputsReady : Prop
  activeTunnelEmbeddingGeometryInputsReady : Prop
  uDotNPlusZeroDerived : Prop
  uDotNMinusZeroDerived : Prop
  eDotNPlusZeroDerived : Prop
  eDotNMinusZeroDerived : Prop
  flowTangencyReady : Prop

def flowTangencyComputed (g : FlowTangencyFromEmbeddingVelocityGate) : Prop :=
  g.metricOnSigmaInputsReady /\
  g.fourVelocityOnSigmaInputsReady /\
  g.activeTunnelEmbeddingGeometryInputsReady /\
  g.uDotNPlusZeroDerived /\
  g.uDotNMinusZeroDerived /\
  g.eDotNPlusZeroDerived /\
  g.eDotNMinusZeroDerived /\
  g.flowTangencyReady

theorem flow_tangency_requires_velocity_and_embedding
    (g : FlowTangencyFromEmbeddingVelocityGate)
    (h : flowTangencyComputed g) :
    g.fourVelocityOnSigmaInputsReady /\
      g.activeTunnelEmbeddingGeometryInputsReady := by
  exact And.intro h.2.1 h.2.2.1

theorem flow_tangency_supplies_un_and_en_zero
    (g : FlowTangencyFromEmbeddingVelocityGate)
    (h : flowTangencyComputed g) :
    g.uDotNPlusZeroDerived /\ g.uDotNMinusZeroDerived /\
      g.eDotNPlusZeroDerived /\ g.eDotNMinusZeroDerived := by
  exact And.intro h.2.2.2.1
    (And.intro h.2.2.2.2.1
      (And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2.1))

end P0EFTJanusZ2SigmaFlowTangencyFromEmbeddingVelocityGate
end JanusFormal
