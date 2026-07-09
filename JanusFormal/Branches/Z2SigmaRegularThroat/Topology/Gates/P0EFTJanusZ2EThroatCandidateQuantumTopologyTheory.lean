namespace JanusFormal
namespace P0EFTJanusZ2EThroatCandidateQuantumTopologyTheory

set_option autoImplicit false

structure CandidateQuantumThroatTheory where
  quantumBoundaryPhaseSpace : Prop
  areaFluxSpectrum : Prop
  integerSectorN : Prop
  LFromArea : Prop
  eThroatEqualsEGlobal : Prop
  primitiveSectorSelected : Prop
  uniqueMacroscopicNSelected : Prop
  derivedFromCurrentJanusAction : Prop

def discreteFamilyAvailable (g : CandidateQuantumThroatTheory) : Prop :=
  g.quantumBoundaryPhaseSpace /\
  g.areaFluxSpectrum /\
  g.integerSectorN /\
  g.LFromArea /\
  g.eThroatEqualsEGlobal

def noFitAlphaFromCandidate (g : CandidateQuantumThroatTheory) : Prop :=
  discreteFamilyAvailable g /\
  g.uniqueMacroscopicNSelected /\
  g.derivedFromCurrentJanusAction

theorem discrete_family_without_unique_N_is_not_no_fit
    (g : CandidateQuantumThroatTheory)
    (_h : discreteFamilyAvailable g)
    (hNoN : Not g.uniqueMacroscopicNSelected) :
    Not (noFitAlphaFromCandidate g) := by
  intro h
  exact hNoN h.2.1

theorem new_postulate_without_action_derivation_is_not_current_janus_derivation
    (g : CandidateQuantumThroatTheory)
    (_h : discreteFamilyAvailable g)
    (hNoDerivation : Not g.derivedFromCurrentJanusAction) :
    Not (noFitAlphaFromCandidate g) := by
  intro h
  exact hNoDerivation h.2.2

end P0EFTJanusZ2EThroatCandidateQuantumTopologyTheory
end JanusFormal
