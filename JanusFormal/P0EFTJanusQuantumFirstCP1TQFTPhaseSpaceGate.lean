import JanusFormal.P0EFTJanusQuantumFirstBoundaryStateOpeningGate

namespace JanusFormal
namespace P0EFTJanusQuantumFirstCP1TQFTPhaseSpaceGate

set_option autoImplicit false

structure QuantumFirstCP1TQFTPhaseSpaceGate where
  cp1CompactOrbitDeclared : Prop
  cp1KKSPeriodDeclared : Prop
  cp1PrequantizationDeclared : Prop
  tqftBoundaryTheoryDeclared : Prop
  tqftLevelIntegralDeclared : Prop
  primitiveSectorLawDerived : Prop
  boundaryHamiltonianDerived : Prop

def quantumLabelsAvailable (g : QuantumFirstCP1TQFTPhaseSpaceGate) : Prop :=
  g.cp1CompactOrbitDeclared /\
  g.cp1KKSPeriodDeclared /\
  g.cp1PrequantizationDeclared /\
  g.tqftBoundaryTheoryDeclared /\
  g.tqftLevelIntegralDeclared

def physicalEnergyScaleAvailable (g : QuantumFirstCP1TQFTPhaseSpaceGate) : Prop :=
  g.primitiveSectorLawDerived /\ g.boundaryHamiltonianDerived

end P0EFTJanusQuantumFirstCP1TQFTPhaseSpaceGate
end JanusFormal
