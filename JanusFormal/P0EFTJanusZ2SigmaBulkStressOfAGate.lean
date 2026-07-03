import JanusFormal.P0EFTJanusZ2SigmaMatterFluxActiveProjectionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBulkStressOfAGate

set_option autoImplicit false

structure BulkStressOfAGate where
  janusBimetricStressBibliographyChecked : Prop
  plusSectorStressDeclared : Prop
  minusSectorStressDeclared : Prop
  perfectFluidFLRWStressImported : Prop
  holstTorsionStressContributionDeclared : Prop
  z2SignPolicyDeclared : Prop
  observationalFitForbidden : Prop
  tPlusMunvOfADeclared : Prop
  tMinusMunvOfADeclared : Prop
  plusMatterDensityPressureOfAReady : Prop
  minusMatterDensityPressureOfAReady : Prop
  torsionStressOfAReady : Prop
  bulkStressPlusOfAReady : Prop
  bulkStressMinusOfAReady : Prop

def bulkStressLedgerDeclared
    (g : BulkStressOfAGate) : Prop :=
  g.janusBimetricStressBibliographyChecked /\
  g.plusSectorStressDeclared /\
  g.minusSectorStressDeclared /\
  g.perfectFluidFLRWStressImported /\
  g.holstTorsionStressContributionDeclared /\
  g.z2SignPolicyDeclared /\
  g.observationalFitForbidden /\
  g.tPlusMunvOfADeclared /\
  g.tMinusMunvOfADeclared

def bulkStressOfAReady
    (g : BulkStressOfAGate) : Prop :=
  bulkStressLedgerDeclared g /\
  g.plusMatterDensityPressureOfAReady /\
  g.minusMatterDensityPressureOfAReady /\
  g.torsionStressOfAReady /\
  g.bulkStressPlusOfAReady /\
  g.bulkStressMinusOfAReady

theorem bulk_stress_requires_sector_density_pressure
    (g : BulkStressOfAGate)
    (hReady : bulkStressOfAReady g) :
    g.plusMatterDensityPressureOfAReady /\ g.minusMatterDensityPressureOfAReady := by
  exact And.intro hReady.2.1 hReady.2.2.1

end P0EFTJanusZ2SigmaBulkStressOfAGate
end JanusFormal
