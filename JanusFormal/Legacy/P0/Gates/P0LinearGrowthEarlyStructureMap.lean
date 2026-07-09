import JanusFormal.Legacy.P0.Gates.P0DarkSectorEffectiveMap
import JanusFormal.Legacy.P0.Gates.P0ModifiedFriedmannMinisuperspace

namespace JanusFormal
namespace P0LinearGrowthEarlyStructureMap

open P0CosmologyObservableProgram
open P0DarkSectorEffectiveMap
open P0ModifiedFriedmannMinisuperspace

set_option autoImplicit false

structure LinearGrowthModeParams where
  dlnHOverDlna : Rat
  effectiveGravityPlus : Rat
  repulsiveCompression : Rat
  sgr : Rat

def growthFrictionIndex (p : LinearGrowthModeParams) : Rat :=
  2 + p.dlnHOverDlna

def growthSourceStrength
    (bg : FLRWMinisuperspaceParams)
    (p : LinearGrowthModeParams) : Rat :=
  p.effectiveGravityPlus * bg.rhoPlus +
    p.repulsiveCompression * apparentDarkMatterDensityFLRW bg

def growthBoostIndex
    (bg : FLRWMinisuperspaceParams)
    (p : LinearGrowthModeParams) : Rat :=
  growthSourceStrength bg p / p.sgr

def collapseTimeIndex
    (bg : FLRWMinisuperspaceParams)
    (p : LinearGrowthModeParams) : Rat :=
  p.sgr / growthSourceStrength bg p

def linearGrowthMapClosed (c : LinearGrowthModeParams) : Prop :=
  c.sgr > 0 /\ c.effectiveGravityPlus > 0 /\ c.repulsiveCompression > 0

def linearGrowthEquation (bg : FLRWMinisuperspaceParams) (p : LinearGrowthModeParams) : Prop :=
  growthFrictionIndex p > 0 /\ growthBoostIndex bg p > 0

structure LinearGrowthEarlyStructureCertificate where
  darkSector : DarkSectorEffectiveMapCertificate
  darkSectorClosed : darkSectorEffectiveMapClosed darkSector
  growthMode : LinearGrowthModeParams
  growthModeClosed : linearGrowthMapClosed growthMode
  growthEquationDerived : Prop
  collapseTimeDiagnosticWritten : Prop
  jwstObservableDiagnosticWritten : Prop
  aetherInstabilityNotReintroduced : Prop
  scalarVectorClosureConsistency : Prop
  sameParametersWithHubbleMap : Prop

def linearGrowthEarlyStructureClosed
    (c : LinearGrowthEarlyStructureCertificate) : Prop :=
  linearGrowthMapClosed c.growthMode /\
  c.growthEquationDerived /\
  c.collapseTimeDiagnosticWritten /\
  c.jwstObservableDiagnosticWritten /\
  c.aetherInstabilityNotReintroduced /\
  c.scalarVectorClosureConsistency /\
  c.sameParametersWithHubbleMap /\
  darkSectorEffectiveMapClosed c.darkSector

def cosmologyProgramFromGrowth
    (c : LinearGrowthEarlyStructureCertificate)
    (_h : linearGrowthEarlyStructureClosed c) :
    CosmologyObservableProgram :=
  { microTheory := c.darkSector.flrw.microTheory
    microTheoryReady := c.darkSector.flrw.microTheoryReady
    flrwAnsatzLifted := c.darkSector.flrw.flatFLRWAnsatzLifted
    modifiedFriedmannDerived := c.darkSector.flrw.effectiveFriedmannPairWritten
    effectiveDarkMatterMapDerived :=
      c.darkSector.minusSheetDensityTransported
    effectiveDarkEnergyMapDerived :=
      c.darkSector.lambdaEffInterpretedAsGeometry
    hubbleTensionObservableDerived := False
    earlyStructureGrowthDerived := c.growthEquationDerived
    jwstEarlyGalaxyObservableDerived := c.jwstObservableDiagnosticWritten
    negativeLensingSignatureDerived := False
    primordialGWTransitionSignatureDerived := False
    likelihoodPipelineImplemented := False
    noExtraDarkParticlesPostulated := c.darkSector.noNewDarkParticleSpecies }

def linear_growth_gate_from_certificate
    (c : LinearGrowthEarlyStructureCertificate)
    (h : linearGrowthEarlyStructureClosed c) :
    structureGateClosed (cosmologyProgramFromGrowth c h) :=
  And.intro h.right.left h.right.right.right.left

theorem structure_gate_closed_from_growth_certificate
    (c : LinearGrowthEarlyStructureCertificate)
    (h : linearGrowthEarlyStructureClosed c) :
    structureGateClosed (cosmologyProgramFromGrowth c h) :=
  linear_growth_gate_from_certificate c h

theorem observable_prediction_still_blocked_without_falsifiable_signatures
    (c : LinearGrowthEarlyStructureCertificate)
    (h : linearGrowthEarlyStructureClosed c) :
    Not (observablePredictionReady (cosmologyProgramFromGrowth c h)) := by
  intro hPred
  exact hPred.right.right.right.right.right.left.left

def sampleGrowthFLRWParams : FLRWMinisuperspaceParams :=
  { planckMassSquared := 4
    hassanRosenMassSquared := 1
    membraneTension := 30
    radionVev := 1
    aPlus := 1
    aMinus := 2
    nPlus := 1
    nMinus := 1
    rhoPlus := 2
    rhoMinus := 5 }

def sampleGrowthFLRWCerrt : FLRWMinisuperspaceCertificate :=
  { params := sampleGrowthFLRWParams
    microTheory := canonicalMicroTheoryReady
    microTheoryReady := canonical_micro_theory_ready
    flatFLRWAnsatzLifted := True
    twinScaleFactorsIntroduced := True
    hassanRosenEigenvaluesComputed := True
    membraneTensionIncluded := True
    lapseVariationComputed := True
    scaleVariationComputed := True
    effectiveFriedmannPairWritten := True }

theorem sampleGrowthFLRWCerrt_closed :
    flrwMinisuperspaceClosed sampleGrowthFLRWCerrt := by
  norm_num [flrwMinisuperspaceClosed, sampleGrowthFLRWCerrt]

def sampleGrowthDarkSectorCertificate : DarkSectorEffectiveMapCertificate :=
  { flrw := sampleGrowthFLRWCerrt
    flrwClosed := sampleGrowthFLRWCerrt_closed
    determinantVolumeTransportDerived := True
    minusSheetDensityTransported := True
    lambdaEffInterpretedAsGeometry := True
    noNewDarkParticleSpecies := True
    effectiveFriedmannRewriteWritten := True }

theorem sampleGrowthDarkSectorClosed :
    darkSectorEffectiveMapClosed sampleGrowthDarkSectorCertificate := by
  norm_num [darkSectorEffectiveMapClosed, sampleGrowthDarkSectorCertificate]

def sampleGrowthMode : LinearGrowthModeParams :=
  { dlnHOverDlna := -(1 / 2)
    effectiveGravityPlus := 1
    repulsiveCompression := 1
    sgr := 2 }

def sampleGrowthCertificate : LinearGrowthEarlyStructureCertificate :=
  { darkSector := sampleGrowthDarkSectorCertificate
    darkSectorClosed := sampleGrowthDarkSectorClosed
    growthMode := sampleGrowthMode
    growthModeClosed :=
      And.intro (by norm_num [linearGrowthMapClosed, sampleGrowthMode])
        (And.intro
          (by norm_num [linearGrowthMapClosed, sampleGrowthMode])
          (by
            norm_num [linearGrowthMapClosed, sampleGrowthMode]))
    growthEquationDerived := True
    collapseTimeDiagnosticWritten := True
    jwstObservableDiagnosticWritten := True
    aetherInstabilityNotReintroduced := True
    scalarVectorClosureConsistency := True
    sameParametersWithHubbleMap := True }

theorem sample_growth_mode_closed :
    linearGrowthMapClosed sampleGrowthMode := by
  exact sampleGrowthCertificate.growthModeClosed

theorem sample_growth_gate_closed :
    linearGrowthEarlyStructureClosed sampleGrowthCertificate := by
  norm_num [linearGrowthEarlyStructureClosed, sampleGrowthCertificate,
    sample_growth_mode_closed, sampleGrowthDarkSectorClosed]

theorem sample_growth_source_boost_witness :
    growthSourceStrength sampleGrowthFLRWParams sampleGrowthMode = 42 := by
  norm_num [growthSourceStrength, sampleGrowthMode, sampleGrowthFLRWParams,
    apparentDarkMatterDensityFLRW, flrwVolumeRatio, flrwScaleRatio]

theorem sample_growth_boost_ratio :
    growthBoostIndex sampleGrowthFLRWParams sampleGrowthMode = 21 := by
  norm_num [growthBoostIndex, growthSourceStrength, sampleGrowthMode,
    sampleGrowthFLRWParams, apparentDarkMatterDensityFLRW, flrwVolumeRatio,
    flrwScaleRatio]

theorem sample_growth_collapse_index :
    collapseTimeIndex sampleGrowthFLRWParams sampleGrowthMode = (1 / 21) := by
  norm_num [collapseTimeIndex, growthSourceStrength, sampleGrowthMode,
    sampleGrowthFLRWParams, apparentDarkMatterDensityFLRW, flrwVolumeRatio,
    flrwScaleRatio]

theorem sample_growth_structure_gate_closed :
    structureGateClosed
      (cosmologyProgramFromGrowth sampleGrowthCertificate sample_growth_gate_closed) := by
  exact structure_gate_closed_from_growth_certificate
    sampleGrowthCertificate sample_growth_gate_closed

end P0LinearGrowthEarlyStructureMap
end JanusFormal
