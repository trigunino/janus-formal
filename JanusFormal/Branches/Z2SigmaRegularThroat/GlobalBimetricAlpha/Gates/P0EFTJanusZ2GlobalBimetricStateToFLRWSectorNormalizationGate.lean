namespace JanusFormal
namespace P0EFTJanusZ2GlobalBimetricStateToFLRWSectorNormalizationGate

set_option autoImplicit false

structure GlobalBimetricStateToFLRWSectorNormalizationGate where
  globalStressEnergyStateAvailable : Prop
  rhoPlus0Derived : Prop
  rhoMinus0Derived : Prop
  PTSignReversalProved : Prop
  volumeProjectionDeclared : Prop
  fittedDensityUsed : Prop
  lcdmDensityUsed : Prop
  nGapForcedToDensity : Prop

def sectorNormalizationsReady
    (g : GlobalBimetricStateToFLRWSectorNormalizationGate) : Prop :=
  g.globalStressEnergyStateAvailable /\
  g.rhoPlus0Derived /\
  g.rhoMinus0Derived /\
  g.PTSignReversalProved /\
  g.volumeProjectionDeclared /\
  Not g.fittedDensityUsed /\
  Not g.lcdmDensityUsed /\
  Not g.nGapForcedToDensity

theorem no_global_state_blocks_sector_normalization
    (g : GlobalBimetricStateToFLRWSectorNormalizationGate)
    (hMissing : Not g.globalStressEnergyStateAvailable) :
    Not (sectorNormalizationsReady g) := by
  intro h
  exact hMissing h.left

end P0EFTJanusZ2GlobalBimetricStateToFLRWSectorNormalizationGate
end JanusFormal
