import JanusFormal.Branches.AsymptoticNullBoundaryCharges.Gates.P0EFTJanusAsymptoticNullBoundarySymmetryOpeningGate

namespace JanusFormal
namespace P0EFTJanusAsymptoticNullBoundaryCandidateMatrixGate

set_option autoImplicit false

structure AsymptoticNullBoundaryChargesCandidateMatrixGate where
  nullInfinityCandidateDeclared : Prop
  internalNullBridgeCandidateDeclared : Prop
  finiteThroatSigmaCandidateDeclared : Prop
  asymptoticFlatnessForBMSAvailable : Prop
  nullBoundaryStructureAvailable : Prop
  referenceCutOrTimeGeneratorAvailable : Prop

def bmsChargeCandidateReady (g : AsymptoticNullBoundaryChargesCandidateMatrixGate) : Prop :=
  g.nullInfinityCandidateDeclared /\
  g.asymptoticFlatnessForBMSAvailable /\
  g.referenceCutOrTimeGeneratorAvailable

def internalNullChargeCandidateReady (g : AsymptoticNullBoundaryChargesCandidateMatrixGate) : Prop :=
  g.internalNullBridgeCandidateDeclared /\
  g.nullBoundaryStructureAvailable /\
  g.referenceCutOrTimeGeneratorAvailable

end P0EFTJanusAsymptoticNullBoundaryCandidateMatrixGate
end JanusFormal
