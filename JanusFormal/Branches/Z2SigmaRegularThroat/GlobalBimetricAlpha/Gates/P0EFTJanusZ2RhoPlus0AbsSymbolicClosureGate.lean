namespace JanusFormal
namespace P0EFTJanusZ2RhoPlus0AbsSymbolicClosureGate

set_option autoImplicit false

structure RhoPlus0AbsSymbolicClosureGate where
  baryonMassAvailable : Prop
  occupationStateAvailable : Prop
  curvatureRadiusAvailable : Prop
  publishedSectorRatioAvailable : Prop
  usesObservationOmegaB : Prop
  usesLCDMDensity : Prop
  usesLegacyZ4 : Prop

def rhoPlus0AbsReady (g : RhoPlus0AbsSymbolicClosureGate) : Prop :=
  g.baryonMassAvailable /\
  g.occupationStateAvailable /\
  g.curvatureRadiusAvailable /\
  g.publishedSectorRatioAvailable /\
  Not g.usesObservationOmegaB /\
  Not g.usesLCDMDensity /\
  Not g.usesLegacyZ4

theorem missing_occupation_blocks_rhoPlus0Abs
    (g : RhoPlus0AbsSymbolicClosureGate)
    (hMissing : Not g.occupationStateAvailable) :
    Not (rhoPlus0AbsReady g) := by
  intro h
  exact hMissing h.right.left

theorem missing_radius_blocks_rhoPlus0Abs
    (g : RhoPlus0AbsSymbolicClosureGate)
    (hMissing : Not g.curvatureRadiusAvailable) :
    Not (rhoPlus0AbsReady g) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTJanusZ2RhoPlus0AbsSymbolicClosureGate
end JanusFormal
