import JanusFormal.Legacy.P0.Gates.P0ModifiedFriedmannMinisuperspace

namespace JanusFormal
namespace P0DarkSectorEffectiveMap

open P0CosmologyObservableProgram
open P0ModifiedFriedmannMinisuperspace

set_option autoImplicit false

def flrwVolumeRatio (p : FLRWMinisuperspaceParams) : Rat :=
  flrwScaleRatio p ^ 3

def apparentDarkMatterDensityFLRW
    (p : FLRWMinisuperspaceParams) : Rat :=
  flrwVolumeRatio p * p.rhoMinus

def apparentDarkEnergyDensityFLRW
    (p : FLRWMinisuperspaceParams) : Rat :=
  lambdaEffNumeratorFLRW p

def totalEffectiveDarkSectorDensityFLRW
    (p : FLRWMinisuperspaceParams) : Rat :=
  apparentDarkMatterDensityFLRW p +
    apparentDarkEnergyDensityFLRW p

def hPlusSquaredWithEffectiveDarkSector
    (p : FLRWMinisuperspaceParams) : Rat :=
  (p.rhoPlus + totalEffectiveDarkSectorDensityFLRW p) /
    (3 * p.planckMassSquared)

structure DarkSectorEffectiveMapCertificate where
  flrw : FLRWMinisuperspaceCertificate
  flrwClosed : flrwMinisuperspaceClosed flrw
  determinantVolumeTransportDerived : Prop
  minusSheetDensityTransported : Prop
  lambdaEffInterpretedAsGeometry : Prop
  noNewDarkParticleSpecies : Prop
  effectiveFriedmannRewriteWritten : Prop

def darkSectorEffectiveMapClosed
    (c : DarkSectorEffectiveMapCertificate) : Prop :=
  c.determinantVolumeTransportDerived /\
  c.minusSheetDensityTransported /\
  c.lambdaEffInterpretedAsGeometry /\
  c.noNewDarkParticleSpecies /\
  c.effectiveFriedmannRewriteWritten

def cosmologyProgramFromDarkSector
    (c : DarkSectorEffectiveMapCertificate)
    (_h : darkSectorEffectiveMapClosed c) :
    CosmologyObservableProgram :=
  { microTheory := c.flrw.microTheory
    microTheoryReady := c.flrw.microTheoryReady
    flrwAnsatzLifted := c.flrw.flatFLRWAnsatzLifted
    modifiedFriedmannDerived := c.flrw.effectiveFriedmannPairWritten
    effectiveDarkMatterMapDerived := c.minusSheetDensityTransported
    effectiveDarkEnergyMapDerived := c.lambdaEffInterpretedAsGeometry
    hubbleTensionObservableDerived := False
    earlyStructureGrowthDerived := False
    jwstEarlyGalaxyObservableDerived := False
    negativeLensingSignatureDerived := False
    primordialGWTransitionSignatureDerived := False
    likelihoodPipelineImplemented := False
    noExtraDarkParticlesPostulated := c.noNewDarkParticleSpecies }

theorem dark_sector_gate_closed_from_effective_map
    (c : DarkSectorEffectiveMapCertificate)
    (h : darkSectorEffectiveMapClosed c) :
    darkSectorGateClosed (cosmologyProgramFromDarkSector c h) := by
  exact ⟨h.right.left, h.right.right.left, h.right.right.right.left⟩

theorem hubble_still_blocks_after_dark_sector_only
    (c : DarkSectorEffectiveMapCertificate)
    (h : darkSectorEffectiveMapClosed c) :
    Not (observablePredictionReady (cosmologyProgramFromDarkSector c h)) := by
  intro hReady
  exact hReady.right.right.right.left.right

theorem effective_dark_sector_density_splits
    (p : FLRWMinisuperspaceParams) :
    totalEffectiveDarkSectorDensityFLRW p =
      flrwVolumeRatio p * p.rhoMinus + lambdaEffNumeratorFLRW p := by
  rfl

def sampleDarkSectorCertificate : DarkSectorEffectiveMapCertificate :=
  { flrw := sampleFLRWCertificate
    flrwClosed := sample_flrw_minisuperspace_closed
    determinantVolumeTransportDerived := True
    minusSheetDensityTransported := True
    lambdaEffInterpretedAsGeometry := True
    noNewDarkParticleSpecies := True
    effectiveFriedmannRewriteWritten := True }

theorem sample_dark_sector_effective_map_closed :
    darkSectorEffectiveMapClosed sampleDarkSectorCertificate := by
  norm_num [darkSectorEffectiveMapClosed, sampleDarkSectorCertificate]

theorem sample_dark_sector_gate_closed :
    darkSectorGateClosed
      (cosmologyProgramFromDarkSector
        sampleDarkSectorCertificate sample_dark_sector_effective_map_closed) := by
  exact dark_sector_gate_closed_from_effective_map
    sampleDarkSectorCertificate sample_dark_sector_effective_map_closed

end P0DarkSectorEffectiveMap
end JanusFormal
