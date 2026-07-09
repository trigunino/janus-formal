import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusPlusMinusBoundaryLegOperatorAuditGate

namespace JanusFormal
namespace P0EFTJanusSym4InternalTransferFrontierVerdictGate

set_option autoImplicit false

structure Sym4InternalTransferFrontierVerdictGate where
  scalarBoundaryEnergyExhausted : Prop
  isotropicM31DiagonalExhausted : Prop
  naturalM31GeneratorsExhausted : Prop
  plusMinusLegOperatorExhausted : Prop
  manualBasisOrderingRejected : Prop
  nonDiagonalPTSigmaHNormalDerived : Prop
  modularHamiltonianDerived : Prop
  orderedSym4SpectrumToAminProved : Prop

def internalTransferClosed
    (g : Sym4InternalTransferFrontierVerdictGate) : Prop :=
  g.scalarBoundaryEnergyExhausted /\
  g.isotropicM31DiagonalExhausted /\
  g.naturalM31GeneratorsExhausted /\
  g.plusMinusLegOperatorExhausted /\
  g.manualBasisOrderingRejected /\
  (g.nonDiagonalPTSigmaHNormalDerived \/ g.modularHamiltonianDerived) /\
  g.orderedSym4SpectrumToAminProved

def internalTransferFrontier
    (g : Sym4InternalTransferFrontierVerdictGate) : Prop :=
  g.scalarBoundaryEnergyExhausted /\
  g.isotropicM31DiagonalExhausted /\
  g.naturalM31GeneratorsExhausted /\
  g.plusMinusLegOperatorExhausted /\
  g.manualBasisOrderingRejected /\
  Not g.nonDiagonalPTSigmaHNormalDerived /\
  Not g.modularHamiltonianDerived /\
  Not g.orderedSym4SpectrumToAminProved

theorem exhausted_simple_routes_require_action_or_modular_H
    (g : Sym4InternalTransferFrontierVerdictGate)
    (hFrontier : internalTransferFrontier g) :
    Not (internalTransferClosed g) := by
  intro h
  rcases h.2.2.2.2.2.1 with hAction | hModular
  · exact hFrontier.2.2.2.2.2.1 hAction
  · exact hFrontier.2.2.2.2.2.2.1 hModular

end P0EFTJanusSym4InternalTransferFrontierVerdictGate
end JanusFormal
