import JanusFormal.P0DarkSectorEffectiveMap

namespace JanusFormal
namespace P0HubbleTensionEffectiveMap

open P0CosmologyObservableProgram
open P0ModifiedFriedmannMinisuperspace
open P0DarkSectorEffectiveMap

set_option autoImplicit false

structure HubbleInferencePoint where
  params : FLRWMinisuperspaceParams
  referenceExpansionSquared : Rat

def apparentH0Squared (p : HubbleInferencePoint) : Rat :=
  hPlusSquaredWithEffectiveDarkSector p.params /
    p.referenceExpansionSquared

def h0SquaredSplit
    (early late : HubbleInferencePoint) : Rat :=
  apparentH0Squared late - apparentH0Squared early

def h0SquaredRatio
    (early late : HubbleInferencePoint) : Rat :=
  apparentH0Squared late / apparentH0Squared early

structure HubbleTensionEffectiveMapCertificate where
  darkSector : DarkSectorEffectiveMapCertificate
  darkSectorClosed : darkSectorEffectiveMapClosed darkSector
  earlyPoint : HubbleInferencePoint
  latePoint : HubbleInferencePoint
  referenceExpansionDeclared : Prop
  cmbLikeWindowSelected : Prop
  lateTimeWindowSelected : Prop
  sameParametersNoAdHocFit : Prop
  apparentH0MapDerived : Prop
  h0SplitWritten : Prop

def hubbleTensionEffectiveMapClosed
    (c : HubbleTensionEffectiveMapCertificate) : Prop :=
  c.referenceExpansionDeclared /\
  c.cmbLikeWindowSelected /\
  c.lateTimeWindowSelected /\
  c.sameParametersNoAdHocFit /\
  c.apparentH0MapDerived /\
  c.h0SplitWritten

def cosmologyProgramFromHubbleMap
    (c : HubbleTensionEffectiveMapCertificate)
    (_h : hubbleTensionEffectiveMapClosed c) :
    CosmologyObservableProgram :=
  { microTheory := c.darkSector.flrw.microTheory
    microTheoryReady := c.darkSector.flrw.microTheoryReady
    flrwAnsatzLifted := c.darkSector.flrw.flatFLRWAnsatzLifted
    modifiedFriedmannDerived := c.darkSector.flrw.effectiveFriedmannPairWritten
    effectiveDarkMatterMapDerived := c.darkSector.minusSheetDensityTransported
    effectiveDarkEnergyMapDerived := c.darkSector.lambdaEffInterpretedAsGeometry
    hubbleTensionObservableDerived := c.h0SplitWritten
    earlyStructureGrowthDerived := False
    jwstEarlyGalaxyObservableDerived := False
    negativeLensingSignatureDerived := False
    primordialGWTransitionSignatureDerived := False
    likelihoodPipelineImplemented := False
    noExtraDarkParticlesPostulated := c.darkSector.noNewDarkParticleSpecies }

theorem hubble_gate_closed_from_effective_map
    (c : HubbleTensionEffectiveMapCertificate)
    (h : hubbleTensionEffectiveMapClosed c) :
    hubbleGateClosed (cosmologyProgramFromHubbleMap c h) := by
  exact ⟨c.darkSector.flrwClosed.right.right.right.right.right.right,
    h.right.right.right.right.right⟩

theorem structure_still_blocks_after_hubble_only
    (c : HubbleTensionEffectiveMapCertificate)
    (h : hubbleTensionEffectiveMapClosed c) :
    Not (observablePredictionReady (cosmologyProgramFromHubbleMap c h)) := by
  intro hReady
  exact hReady.right.right.right.right.left.left

theorem h0_map_formula
    (p : HubbleInferencePoint) :
    apparentH0Squared p =
      hPlusSquaredWithEffectiveDarkSector p.params /
        p.referenceExpansionSquared := by
  rfl

def sampleEarlyH0Point : HubbleInferencePoint :=
  { params := sampleFLRWParams
    referenceExpansionSquared := 2 }

def sampleLateH0Point : HubbleInferencePoint :=
  { params :=
      { sampleFLRWParams with
        rhoPlus := 2
        rhoMinus := 5
        aMinus := 2 }
    referenceExpansionSquared := 1 }

def sampleHubbleTensionCertificate :
    HubbleTensionEffectiveMapCertificate :=
  { darkSector := sampleDarkSectorCertificate
    darkSectorClosed := sample_dark_sector_effective_map_closed
    earlyPoint := sampleEarlyH0Point
    latePoint := sampleLateH0Point
    referenceExpansionDeclared := True
    cmbLikeWindowSelected := True
    lateTimeWindowSelected := True
    sameParametersNoAdHocFit := True
    apparentH0MapDerived := True
    h0SplitWritten := True }

theorem sample_hubble_tension_effective_map_closed :
    hubbleTensionEffectiveMapClosed sampleHubbleTensionCertificate := by
  norm_num [hubbleTensionEffectiveMapClosed, sampleHubbleTensionCertificate]

theorem sample_hubble_gate_closed :
    hubbleGateClosed
      (cosmologyProgramFromHubbleMap
        sampleHubbleTensionCertificate
        sample_hubble_tension_effective_map_closed) := by
  exact hubble_gate_closed_from_effective_map
    sampleHubbleTensionCertificate
    sample_hubble_tension_effective_map_closed

end P0HubbleTensionEffectiveMap
end JanusFormal
