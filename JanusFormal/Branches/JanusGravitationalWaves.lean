import JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWMinkowskiTensorGate
import JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWFLRWTensorInterface
import JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWStabilityCausalityGate
import JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWOscillationGate
import JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWSourceDetectorInterface
import JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWProgramPTechnicalBridge

namespace JanusFormal
namespace JanusGravitationalWaves

/-- J-GW starts with a closed Minkowski TT gate. The FLRW action, matter
projection, waveform and likelihood gates remain open. -/
structure ProgramStatus where
  programPTechnicalBridge : Prop
  gw01MinkowskiTensorGate : Prop
  gw01ConditionalFLRWTensorInterface : Prop
  gw01PhysicalFLRWTensorGate : Prop
  gw02ReducedMinkowskiStabilityCausalityGate : Prop
  gw02PhysicalFLRWStabilityCausalityGate : Prop
  gw03GenericOscillationGate : Prop
  gw03PhysicalPropagationGate : Prop
  gw04SourceDetectorInterface : Prop
  gw04PhysicalWaveformGate : Prop
  gw05LikelihoodGate : Prop

def initialGateClosed (s : ProgramStatus) : Prop :=
  s.gw01MinkowskiTensorGate

def programClosed (s : ProgramStatus) : Prop :=
  s.gw01MinkowskiTensorGate ∧
  s.gw01ConditionalFLRWTensorInterface ∧
  s.gw01PhysicalFLRWTensorGate ∧
  s.gw02ReducedMinkowskiStabilityCausalityGate ∧
  s.gw02PhysicalFLRWStabilityCausalityGate ∧
  s.gw03GenericOscillationGate ∧
  s.gw03PhysicalPropagationGate ∧
  s.gw04SourceDetectorInterface ∧
  s.gw04PhysicalWaveformGate ∧
  s.gw05LikelihoodGate

end JanusGravitationalWaves
end JanusFormal
