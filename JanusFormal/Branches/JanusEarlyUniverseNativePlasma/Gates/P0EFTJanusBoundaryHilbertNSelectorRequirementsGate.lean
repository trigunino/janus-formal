import JanusFormal.Branches.ComplexRealityQuantumStateLaw.Gates.P0EFTJanusComplexRealityCP1FromJanusPTGate
import JanusFormal.Branches.ComplexRealityQuantumStateLaw.Gates.P0EFTJanusComplexRealityPrequantizationIntegralityGate

namespace JanusFormal
namespace P0EFTJanusBoundaryHilbertNSelectorRequirementsGate

set_option autoImplicit false

structure BoundaryHilbertNSelectorRequirementsGate where
  cp1CandidateImported : Prop
  kksPrequantizationScaffoldImported : Prop
  requiredNComputed : Prop
  cp1SpinJEquals500Required : Prop
  kksOrCSLevel1000Required : Prop
  cp1MathValid : Prop
  kksMathValid : Prop
  janusSectorSelectionLawDerived : Prop
  NEntersAminAndPhotonRulerDynamics : Prop

def boundaryHilbertNSelectorReady
    (g : BoundaryHilbertNSelectorRequirementsGate) : Prop :=
  g.cp1CandidateImported /\
  g.kksPrequantizationScaffoldImported /\
  g.requiredNComputed /\
  g.cp1SpinJEquals500Required /\
  g.kksOrCSLevel1000Required /\
  g.cp1MathValid /\
  g.kksMathValid /\
  Not g.janusSectorSelectionLawDerived /\
  Not g.NEntersAminAndPhotonRulerDynamics

theorem boundary_Hilbert_route_needs_sector_selection
    (g : BoundaryHilbertNSelectorRequirementsGate)
    (hReady : boundaryHilbertNSelectorReady g) :
    Not g.janusSectorSelectionLawDerived /\ Not g.NEntersAminAndPhotonRulerDynamics := by
  exact And.intro hReady.2.2.2.2.2.2.2.1 hReady.2.2.2.2.2.2.2.2

end P0EFTJanusBoundaryHilbertNSelectorRequirementsGate
end JanusFormal
