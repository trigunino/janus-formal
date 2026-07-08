import JanusFormal.P0EFTJanusAsymptoticNullBoundarySymmetryOpeningGate

namespace JanusFormal
namespace P0EFTJanusAsymptoticNullBoundaryCandidateMatrixGate

set_option autoImplicit false

structure AsymptoticNullBoundaryCandidateMatrixGate where
  nullInfinityCandidateDeclared : Prop
  internalNullBridgeCandidateDeclared : Prop
  finiteThroatSigmaCandidateDeclared : Prop
  asymptoticFlatnessForBMSAvailable : Prop
  nullBoundaryStructureAvailable : Prop
  referenceCutOrTimeGeneratorAvailable : Prop

def bmsChargeCandidateReady (g : AsymptoticNullBoundaryCandidateMatrixGate) : Prop :=
  g.nullInfinityCandidateDeclared /\
  g.asymptoticFlatnessForBMSAvailable /\
  g.referenceCutOrTimeGeneratorAvailable

def internalNullChargeCandidateReady (g : AsymptoticNullBoundaryCandidateMatrixGate) : Prop :=
  g.internalNullBridgeCandidateDeclared /\
  g.nullBoundaryStructureAvailable /\
  g.referenceCutOrTimeGeneratorAvailable

end P0EFTJanusAsymptoticNullBoundaryCandidateMatrixGate
end JanusFormal
