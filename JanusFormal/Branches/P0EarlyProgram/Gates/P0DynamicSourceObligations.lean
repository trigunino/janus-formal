import JanusFormal.Branches.P0EarlyProgram.Gates.P0ClosureAxiomatics

namespace JanusFormal
namespace P0DynamicSourceObligations

open P0ClosureAxiomatics

set_option autoImplicit false

structure CandidateSourceAction where
  actionFunctional : Prop
  eulerLagrangeEquations : Prop
  noetherIdentities : Prop
  covariantSourceMeasure : Prop
  bridgeVariablePresent : Prop
  pressurePiSectorPresent : Prop

def acceptedSourceAction (s : CandidateSourceAction) : Prop :=
  s.actionFunctional /\
  s.eulerLagrangeEquations /\
  s.noetherIdentities /\
  s.covariantSourceMeasure /\
  s.bridgeVariablePresent /\
  s.pressurePiSectorPresent

structure BridgeUniqueness where
  bridgeEquationWritten : Prop
  uniqueBridgeSolution : Prop
  sameBridgeTransportLaw : Prop

def bridgeSelectedBySourceAction
    (s : CandidateSourceAction)
    (u : BridgeUniqueness) : Prop :=
  acceptedSourceAction s /\
  u.bridgeEquationWritten /\
  u.uniqueBridgeSolution /\
  u.sameBridgeTransportLaw

def dynamicAxiomsFromSource
    (s : CandidateSourceAction)
    (u : BridgeUniqueness)
    (b4volSelected pressurePiClosed noScalarAbsorb : Prop) :
    DynamicActionAxioms :=
  { sourceActionExists := s.actionFunctional
    actionVariationEquationsWritten := s.eulerLagrangeEquations
    bridgeSelectedByEulerLagrange := bridgeSelectedBySourceAction s u
    sameBridgeForKAndQcross := u.sameBridgeTransportLaw
    b4volSelectedBySourceMeasure := b4volSelected
    pressureAndPiTransportClosed := pressurePiClosed
    splitNoetherIdentitiesClosed := s.noetherIdentities
    noScalarAbsorption := noScalarAbsorb }

theorem accepted_source_action_has_variation_equations
    (s : CandidateSourceAction)
    (h : acceptedSourceAction s) :
    s.eulerLagrangeEquations := by
  exact h.right.left

theorem bridge_selection_requires_uniqueness
    (s : CandidateSourceAction)
    (u : BridgeUniqueness)
    (h : bridgeSelectedBySourceAction s u) :
    u.uniqueBridgeSolution := by
  exact h.right.right.left

theorem missing_bridge_uniqueness_blocks_bridge_selection
    (s : CandidateSourceAction)
    (u : BridgeUniqueness)
    (hMissing : Not u.uniqueBridgeSolution) :
    Not (bridgeSelectedBySourceAction s u) := by
  intro hSelected
  exact hMissing (bridge_selection_requires_uniqueness s u hSelected)

theorem source_action_and_uniqueness_give_bridge_selection
    (s : CandidateSourceAction)
    (u : BridgeUniqueness)
    (hSource : acceptedSourceAction s)
    (hEquation : u.bridgeEquationWritten)
    (hUnique : u.uniqueBridgeSolution)
    (hSame : u.sameBridgeTransportLaw) :
    bridgeSelectedBySourceAction s u := by
  exact ⟨hSource, hEquation, hUnique, hSame⟩

theorem full_source_obligations_give_conditional_prediction
    (s : CandidateSourceAction)
    (u : BridgeUniqueness)
    {b4volSelected pressurePiClosed noScalarAbsorb : Prop}
    (hSource : acceptedSourceAction s)
    (hEquation : u.bridgeEquationWritten)
    (hUnique : u.uniqueBridgeSolution)
    (hSame : u.sameBridgeTransportLaw)
    (hB4 : b4volSelected)
    (hPressurePi : pressurePiClosed)
    (hNoAbsorb : noScalarAbsorb) :
    (closureTargetFromAxioms
      (dynamicAxiomsFromSource s u b4volSelected pressurePiClosed noScalarAbsorb)).predictionReady := by
  rcases hSource with
    ⟨hAction, hVariation, hNoether, hMeasure, hBridgePresent, hPressurePiPresent⟩
  exact conditional_closure_from_dynamic_action_axioms
    (dynamicAxiomsFromSource s u b4volSelected pressurePiClosed noScalarAbsorb)
    ⟨hAction,
      hVariation,
      ⟨⟨hAction, hVariation, hNoether, hMeasure, hBridgePresent, hPressurePiPresent⟩,
        hEquation, hUnique, hSame⟩,
      hSame,
      hB4,
      hPressurePi,
      hNoether,
      hNoAbsorb⟩

theorem missing_source_action_blocks_prediction
    (s : CandidateSourceAction)
    (u : BridgeUniqueness)
    {b4volSelected pressurePiClosed noScalarAbsorb : Prop}
  (hMissing : Not s.actionFunctional) :
    Not (closureTargetFromAxioms
      (dynamicAxiomsFromSource s u b4volSelected pressurePiClosed noScalarAbsorb)).predictionReady := by
  apply prediction_blocked_by_missing_dynamic_axiom
    (m := DynamicAxiomName.sourceAction)
  exact hMissing

theorem missing_same_bridge_blocks_prediction
    (s : CandidateSourceAction)
    (u : BridgeUniqueness)
    {b4volSelected pressurePiClosed noScalarAbsorb : Prop}
  (hMissing : Not u.sameBridgeTransportLaw) :
    Not (closureTargetFromAxioms
      (dynamicAxiomsFromSource s u b4volSelected pressurePiClosed noScalarAbsorb)).predictionReady := by
  apply prediction_blocked_by_missing_dynamic_axiom
    (m := DynamicAxiomName.sameBridge)
  exact hMissing

end P0DynamicSourceObligations
end JanusFormal
