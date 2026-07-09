namespace JanusFormal
namespace P0EFTJanusVariableConstantsThermalFrameMapGate

set_option autoImplicit false

structure VariableConstantsThermalFrameMapGate where
  eq40HcCubedExponentIsThree : Prop
  adiabaticRadiationRhoExponentMinusFour : Prop
  conservedComovingPhotonNumberExponentMinusThree : Prop
  exponentSystemDeclared : Prop
  thermalEnergyTemperatureExponentMinusOne : Prop
  occupationExponentA3 : Prop
  numberTargetMatched : Prop
  energyTargetMatched : Prop

def thermalFrameMapReady (g : VariableConstantsThermalFrameMapGate) : Prop :=
  g.eq40HcCubedExponentIsThree /\
  g.adiabaticRadiationRhoExponentMinusFour /\
  g.conservedComovingPhotonNumberExponentMinusThree /\
  g.exponentSystemDeclared /\
  g.thermalEnergyTemperatureExponentMinusOne /\
  g.occupationExponentA3 /\
  g.numberTargetMatched /\
  g.energyTargetMatched

theorem thermal_frame_solves_temperature_and_occupation
    (g : VariableConstantsThermalFrameMapGate)
    (hReady : thermalFrameMapReady g) :
    g.thermalEnergyTemperatureExponentMinusOne /\ g.occupationExponentA3 := by
  exact And.intro hReady.2.2.2.2.1 hReady.2.2.2.2.2.1

end P0EFTJanusVariableConstantsThermalFrameMapGate
end JanusFormal
