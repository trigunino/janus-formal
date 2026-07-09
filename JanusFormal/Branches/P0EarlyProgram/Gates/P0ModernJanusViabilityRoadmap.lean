import JanusFormal.Branches.P0EarlyProgram.Gates.P0OrbifoldActionCandidate
import JanusFormal.Branches.P0EarlyProgram.Gates.P0SouriauPoincareEnergyBranch
import JanusFormal.Branches.P0EarlyProgram.Gates.P0OrbifoldBoundaryNoether

namespace JanusFormal
namespace P0ModernJanusViabilityRoadmap

open P0OrbifoldActionProgram
open P0OrbifoldActionCandidate
open P0VielbeinEnergyResolution
open P0SouriauPoincareEnergyBranch
open P0OrbifoldBoundaryNoether
open P0ClosureAxiomatics

set_option autoImplicit false

structure ModernJanusData (Metric Vielbein Bridge Measure : Type) where
  actionCandidate : OrbifoldActionCandidate
  actionUnique : uniqueOrbifoldAction candidateActionProblem
  vielbeinResolution : VielbeinEnergyResolution Vielbein Metric
  souriauCertificate : SouriauEnergyBranchCertificate
  topology : OrbifoldTopologicalInvariants
  metricBreaking : TwoMetricBreaking Metric
  bridgeSelectedByOrbifoldVariation : Prop
  sameBridgeForKAndQcross : Prop
  b4volSelectedBySourceMeasure : Prop
  pressureAndPiTransportClosed : Prop
  noScalarAbsorption : Prop

def modernJanusObligations
    {Metric Vielbein Bridge Measure : Type}
    (d : ModernJanusData Metric Vielbein Bridge Measure) : Prop :=
  acceptedOrbifoldAction candidateActionProblem d.actionCandidate /\
  uniqueOrbifoldAction candidateActionProblem /\
  resolutionClosed d.vielbeinResolution /\
  negativeSectorEnergyClosed (quantumEnergyFromSouriau d.souriauCertificate) /\
  topologyConservationReady d.topology /\
  metricBreakingClosed d.metricBreaking /\
  d.bridgeSelectedByOrbifoldVariation /\
  d.sameBridgeForKAndQcross /\
  d.b4volSelectedBySourceMeasure /\
  d.pressureAndPiTransportClosed /\
  d.noScalarAbsorption

def orbifoldProgramFromModernJanus
    {Metric Vielbein Bridge Measure : Type}
    (d : ModernJanusData Metric Vielbein Bridge Measure) :
    OrbifoldProgramData OrbifoldActionCandidate Metric Bridge Measure :=
  { actionProblem := candidateActionProblem
    action := d.actionCandidate
    metricBreaking := d.metricBreaking
    topology := d.topology
    bridgeSelectedByOrbifoldVariation := d.bridgeSelectedByOrbifoldVariation
    sameBridgeForKAndQcross := d.sameBridgeForKAndQcross
    b4volSelectedBySourceMeasure := d.b4volSelectedBySourceMeasure
    pressureAndPiTransportClosed := d.pressureAndPiTransportClosed
    noScalarAbsorption := d.noScalarAbsorption }

theorem modern_janus_obligations_give_orbifold_certificate
    {Metric Vielbein Bridge Measure : Type}
    (d : ModernJanusData Metric Vielbein Bridge Measure)
    (h : modernJanusObligations d) :
    OrbifoldProgramCertificate (orbifoldProgramFromModernJanus d) := by
  rcases h with
    ⟨hAction, hUnique, _hResolution, _hEnergy, hTopology,
      hMetric, hBridge, hSame, hB4, hPressurePi, hNoAbsorb⟩
  exact
    { acceptedAction := hAction
      uniqueAction := hUnique
      metricBreaking := hMetric
      topologyReady := hTopology
      bridgeSelected := hBridge
      sameBridge := hSame
      b4volSelected := hB4
      pressurePiClosed := hPressurePi
      noScalarAbsorb := hNoAbsorb }

theorem modern_janus_obligations_give_conditional_prediction
    {Metric Vielbein Bridge Measure : Type}
    (d : ModernJanusData Metric Vielbein Bridge Measure)
    (h : modernJanusObligations d) :
    (closureTargetFromAxioms
      (dynamicAxiomsFromOrbifoldProgram
        (orbifoldProgramFromModernJanus d))).predictionReady := by
  exact orbifold_program_certificate_gives_conditional_prediction
    (orbifoldProgramFromModernJanus d)
    (modern_janus_obligations_give_orbifold_certificate d h)

theorem souriau_certificate_supplies_energy_part
    (c : SouriauEnergyBranchCertificate) :
    negativeSectorEnergyClosed (quantumEnergyFromSouriau c) := by
  exact souriau_route_closes_negative_energy_orientation c

theorem roadmap_blocks_overclaim_without_unique_action
    {Metric Vielbein Bridge Measure : Type}
    (d : ModernJanusData Metric Vielbein Bridge Measure)
    (hMissing : Not (uniqueOrbifoldAction candidateActionProblem)) :
    Not (modernJanusObligations d) := by
  intro h
  exact hMissing h.right.left

theorem roadmap_blocks_overclaim_without_souriau_confinement
    (s : FullPoincareSouriauData)
    (c : MinusSheetConfinementData)
    (hMissingBranch : Not c.branchSelectedOnMinusSheet) :
    Not (Nonempty
      { cert : SouriauEnergyBranchCertificate //
        cert.souriauData = s /\ cert.confinementData = c }) := by
  exact missing_branch_selection_blocks_souriau_certificate s c hMissingBranch

end P0ModernJanusViabilityRoadmap
end JanusFormal
