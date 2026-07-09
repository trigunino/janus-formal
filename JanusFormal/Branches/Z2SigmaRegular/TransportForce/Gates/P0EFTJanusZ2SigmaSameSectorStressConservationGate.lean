import JanusFormal.Branches.Z2SigmaRegular.MatterPlasmaSpinor.Gates.P0EFTJanusZ2SigmaPlusMinusDiracMatterActionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSameSectorStressConservationGate

set_option autoImplicit false

structure SameSectorStressConservationGate where
  plusMinusDiracMatterActionGateImported : Prop
  plusStressTensorDeclaredFromMatterAction : Prop
  minusStressTensorDeclaredFromMatterAction : Prop
  plusMatterDiffeomorphismNoetherIdentityDeclared : Prop
  minusMatterDiffeomorphismNoetherIdentityDeclared : Prop
  crossStressExcludedFromSameSectorStress : Prop
  plusMatterActionReady : Prop
  minusMatterActionReady : Prop
  plusMatterEomReady : Prop
  minusMatterEomReady : Prop
  sameSectorPlusStressConserved : Prop
  sameSectorMinusStressConserved : Prop

def sameSectorStressConservationLedgerDeclared
    (g : SameSectorStressConservationGate) : Prop :=
  g.plusMinusDiracMatterActionGateImported /\
  g.plusStressTensorDeclaredFromMatterAction /\
  g.minusStressTensorDeclaredFromMatterAction /\
  g.plusMatterDiffeomorphismNoetherIdentityDeclared /\
  g.minusMatterDiffeomorphismNoetherIdentityDeclared /\
  g.crossStressExcludedFromSameSectorStress

def sameSectorStressConservationReady
    (g : SameSectorStressConservationGate) : Prop :=
  sameSectorStressConservationLedgerDeclared g /\
  g.plusMatterActionReady /\
  g.minusMatterActionReady /\
  g.plusMatterEomReady /\
  g.minusMatterEomReady /\
  g.sameSectorPlusStressConserved /\
  g.sameSectorMinusStressConserved

theorem same_sector_stress_conservation_feeds_conditional_closure
    (g : SameSectorStressConservationGate)
    (hReady : sameSectorStressConservationReady g) :
    g.sameSectorPlusStressConserved /\ g.sameSectorMinusStressConserved := by
  exact And.intro hReady.right.right.right.right.right.left
    hReady.right.right.right.right.right.right

theorem missing_plus_matter_action_blocks_stress_conservation
    (g : SameSectorStressConservationGate)
    (hMissing : Not g.plusMatterActionReady) :
    Not (sameSectorStressConservationReady g) := by
  intro hReady
  exact hMissing hReady.right.left

theorem missing_plus_matter_eom_blocks_stress_conservation
    (g : SameSectorStressConservationGate)
    (hMissing : Not g.plusMatterEomReady) :
    Not (sameSectorStressConservationReady g) := by
  intro hReady
  exact hMissing hReady.right.right.right.left

end P0EFTJanusZ2SigmaSameSectorStressConservationGate
end JanusFormal
