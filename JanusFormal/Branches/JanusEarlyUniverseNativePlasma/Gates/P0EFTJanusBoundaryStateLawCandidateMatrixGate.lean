import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusBoundaryHilbertSectorSelectionFrontierGate

namespace JanusFormal
namespace P0EFTJanusBoundaryStateLawCandidateMatrixGate

set_option autoImplicit false

structure BoundaryStateLawCandidateMatrixGate where
  requiredNEquals1001 : Prop
  factorization1001Equals7Times11Times13 : Prop
  binomial1001EqualsChoose14_4 : Prop
  cp1SpinSectorCanRepresent1001 : Prop
  kksLevelCanRepresent1001 : Prop
  fluxOrAreaSectorCanRepresent1001 : Prop
  exteriorPowerSectorCanRepresent1001 : Prop
  anomalyOrModularSectorCandidateDeclared : Prop
  microcanonicalSectorCandidateDeclared : Prop
  cp1LawDerivedFromJanus : Prop
  kksLawDerivedFromJanus : Prop
  fluxAreaLawDerivedFromJanus : Prop
  exteriorPowerLawDerivedFromJanus : Prop
  anomalyModularLawDerivedFromJanus : Prop
  microcanonicalLawDerivedFromJanus : Prop

def atLeastOneBoundaryStateLawDerived
    (g : BoundaryStateLawCandidateMatrixGate) : Prop :=
  g.cp1LawDerivedFromJanus \/
  g.kksLawDerivedFromJanus \/
  g.fluxAreaLawDerivedFromJanus \/
  g.exteriorPowerLawDerivedFromJanus \/
  g.anomalyModularLawDerivedFromJanus \/
  g.microcanonicalLawDerivedFromJanus

def candidateMatrixFrontier
    (g : BoundaryStateLawCandidateMatrixGate) : Prop :=
  g.requiredNEquals1001 /\
  g.factorization1001Equals7Times11Times13 /\
  g.binomial1001EqualsChoose14_4 /\
  g.cp1SpinSectorCanRepresent1001 /\
  g.kksLevelCanRepresent1001 /\
  g.fluxOrAreaSectorCanRepresent1001 /\
  g.exteriorPowerSectorCanRepresent1001 /\
  g.anomalyOrModularSectorCandidateDeclared /\
  g.microcanonicalSectorCandidateDeclared /\
  Not g.cp1LawDerivedFromJanus /\
  Not g.kksLawDerivedFromJanus /\
  Not g.fluxAreaLawDerivedFromJanus /\
  Not g.exteriorPowerLawDerivedFromJanus /\
  Not g.anomalyModularLawDerivedFromJanus /\
  Not g.microcanonicalLawDerivedFromJanus

theorem candidate_matrix_frontier_blocks_derived_state_law
    (g : BoundaryStateLawCandidateMatrixGate)
    (hFrontier : candidateMatrixFrontier g) :
    Not (atLeastOneBoundaryStateLawDerived g) := by
  intro h
  rcases hFrontier with
    ⟨_, _, _, _, _, _, _, _, _, hNoCP1, hNoKKS, hNoFluxArea,
      hNoExterior, hNoAnomaly, hNoMicro⟩
  rcases h with hCP1 | hKKS | hFluxArea | hExterior | hAnomaly | hMicro
  · exact hNoCP1 hCP1
  · exact hNoKKS hKKS
  · exact hNoFluxArea hFluxArea
  · exact hNoExterior hExterior
  · exact hNoAnomaly hAnomaly
  · exact hNoMicro hMicro

end P0EFTJanusBoundaryStateLawCandidateMatrixGate
end JanusFormal
