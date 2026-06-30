import JanusFormal.P0CosmologyObservableProgram

namespace JanusFormal
namespace P0ModifiedFriedmannMinisuperspace

open P0CosmologyObservableProgram
open P0ScalarVectorActionSpec

set_option autoImplicit false

structure FLRWMinisuperspaceParams where
  planckMassSquared : Rat
  hassanRosenMassSquared : Rat
  membraneTension : Rat
  radionVev : Rat
  aPlus : Rat
  aMinus : Rat
  nPlus : Rat
  nMinus : Rat
  rhoPlus : Rat
  rhoMinus : Rat

def flrwScaleRatio (p : FLRWMinisuperspaceParams) : Rat :=
  p.aMinus / p.aPlus

def flrwTimeEigenvalue (p : FLRWMinisuperspaceParams) : Rat :=
  p.radionVev * p.nMinus / p.nPlus

def hrE0 (_p : FLRWMinisuperspaceParams) : Rat := 1

def hrE1 (p : FLRWMinisuperspaceParams) : Rat :=
  flrwTimeEigenvalue p + 3 * flrwScaleRatio p

def hrE2 (p : FLRWMinisuperspaceParams) : Rat :=
  3 * flrwTimeEigenvalue p * flrwScaleRatio p +
    3 * flrwScaleRatio p ^ 2

def hrE3 (p : FLRWMinisuperspaceParams) : Rat :=
  3 * flrwTimeEigenvalue p * flrwScaleRatio p ^ 2 +
    flrwScaleRatio p ^ 3

def hrPotentialFLRW (p : FLRWMinisuperspaceParams) : Rat :=
  hrE0 p + 3 * hrE1 p + 3 * hrE2 p + hrE3 p

def lambdaEffNumeratorFLRW (p : FLRWMinisuperspaceParams) : Rat :=
  p.membraneTension +
    p.hassanRosenMassSquared * p.planckMassSquared * hrPotentialFLRW p

def hPlusSquaredFLRW (p : FLRWMinisuperspaceParams) : Rat :=
  (p.rhoPlus + lambdaEffNumeratorFLRW p) /
    (3 * p.planckMassSquared)

def hMinusSquaredFLRW (p : FLRWMinisuperspaceParams) : Rat :=
  (p.rhoMinus + lambdaEffNumeratorFLRW p) /
    (3 * p.planckMassSquared * p.radionVev ^ 2)

theorem hr_potential_flrw_formula
    (p : FLRWMinisuperspaceParams) :
    hrPotentialFLRW p =
      1 + 3 * (flrwTimeEigenvalue p + 3 * flrwScaleRatio p) +
        3 * (3 * flrwTimeEigenvalue p * flrwScaleRatio p +
          3 * flrwScaleRatio p ^ 2) +
        (3 * flrwTimeEigenvalue p * flrwScaleRatio p ^ 2 +
          flrwScaleRatio p ^ 3) := by
  rfl

structure FLRWMinisuperspaceCertificate where
  params : FLRWMinisuperspaceParams
  microTheory : FullSVTPredictionReadyCertificate
  microTheoryReady : predictionReady microTheory
  flatFLRWAnsatzLifted : Prop
  twinScaleFactorsIntroduced : Prop
  hassanRosenEigenvaluesComputed : Prop
  membraneTensionIncluded : Prop
  lapseVariationComputed : Prop
  scaleVariationComputed : Prop
  effectiveFriedmannPairWritten : Prop

def flrwMinisuperspaceClosed
    (c : FLRWMinisuperspaceCertificate) : Prop :=
  c.flatFLRWAnsatzLifted /\
  c.twinScaleFactorsIntroduced /\
  c.hassanRosenEigenvaluesComputed /\
  c.membraneTensionIncluded /\
  c.lapseVariationComputed /\
  c.scaleVariationComputed /\
  c.effectiveFriedmannPairWritten

def cosmologyProgramFromFLRW
    (c : FLRWMinisuperspaceCertificate)
    (_h : flrwMinisuperspaceClosed c) :
    CosmologyObservableProgram :=
  { microTheory := c.microTheory
    microTheoryReady := c.microTheoryReady
    flrwAnsatzLifted := c.flatFLRWAnsatzLifted
    modifiedFriedmannDerived := c.effectiveFriedmannPairWritten
    effectiveDarkMatterMapDerived := False
    effectiveDarkEnergyMapDerived := False
    hubbleTensionObservableDerived := False
    earlyStructureGrowthDerived := False
    jwstEarlyGalaxyObservableDerived := False
    negativeLensingSignatureDerived := False
    primordialGWTransitionSignatureDerived := False
    likelihoodPipelineImplemented := False
    noExtraDarkParticlesPostulated := True }

theorem flrw_gate_closed_from_minisuperspace
    (c : FLRWMinisuperspaceCertificate)
    (h : flrwMinisuperspaceClosed c) :
    flrwGateClosed (cosmologyProgramFromFLRW c h) := by
  exact ⟨h.left, h.right.right.right.right.right.right⟩

theorem dark_sector_still_blocks_after_flrw_only
    (c : FLRWMinisuperspaceCertificate)
    (h : flrwMinisuperspaceClosed c) :
    Not (observablePredictionReady (cosmologyProgramFromFLRW c h)) := by
  intro hReady
  exact hReady.right.right.left.left

def sampleFLRWParams : FLRWMinisuperspaceParams :=
  { planckMassSquared := 4
    hassanRosenMassSquared := 1
    membraneTension := 30
    radionVev := 1
    aPlus := 1
    aMinus := 1
    nPlus := 1
    nMinus := 1
    rhoPlus := 0
    rhoMinus := 0 }

def sampleFLRWCertificate : FLRWMinisuperspaceCertificate :=
  { params := sampleFLRWParams
    microTheory := canonicalMicroTheoryReady
    microTheoryReady := canonical_micro_theory_ready
    flatFLRWAnsatzLifted := True
    twinScaleFactorsIntroduced := True
    hassanRosenEigenvaluesComputed := True
    membraneTensionIncluded := True
    lapseVariationComputed := True
    scaleVariationComputed := True
    effectiveFriedmannPairWritten := True }

theorem sample_flrw_minisuperspace_closed :
    flrwMinisuperspaceClosed sampleFLRWCertificate := by
  norm_num [flrwMinisuperspaceClosed, sampleFLRWCertificate]

theorem sample_flrw_gate_closed :
    flrwGateClosed
      (cosmologyProgramFromFLRW
        sampleFLRWCertificate sample_flrw_minisuperspace_closed) := by
  exact flrw_gate_closed_from_minisuperspace
    sampleFLRWCertificate sample_flrw_minisuperspace_closed

end P0ModifiedFriedmannMinisuperspace
end JanusFormal
