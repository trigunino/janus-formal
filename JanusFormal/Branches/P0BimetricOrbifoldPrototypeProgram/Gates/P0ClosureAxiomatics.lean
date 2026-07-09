import JanusFormal.Basic

namespace JanusFormal
namespace P0ClosureAxiomatics

set_option autoImplicit false

structure NoGoLayer where
  spathFilterOnlyNotUnique : Prop
  orbifoldFilterOnlyNotUnique : Prop
  solderFilterOnlyNotUnique : Prop

structure DynamicActionAxioms where
  sourceActionExists : Prop
  actionVariationEquationsWritten : Prop
  bridgeSelectedByEulerLagrange : Prop
  sameBridgeForKAndQcross : Prop
  b4volSelectedBySourceMeasure : Prop
  pressureAndPiTransportClosed : Prop
  splitNoetherIdentitiesClosed : Prop
  noScalarAbsorption : Prop

structure ClosureTarget where
  bridgeSelected : Prop
  qcrossTransportClosed : Prop
  matterMeasureClosed : Prop
  pressurePiClosed : Prop
  noetherClosed : Prop
  predictionReady : Prop

def closureTargetFromAxioms (a : DynamicActionAxioms) : ClosureTarget :=
  { bridgeSelected := a.bridgeSelectedByEulerLagrange
    qcrossTransportClosed := a.sameBridgeForKAndQcross
    matterMeasureClosed := a.b4volSelectedBySourceMeasure
    pressurePiClosed := a.pressureAndPiTransportClosed
    noetherClosed := a.splitNoetherIdentitiesClosed
    predictionReady :=
      a.sourceActionExists /\
      a.actionVariationEquationsWritten /\
      a.bridgeSelectedByEulerLagrange /\
      a.sameBridgeForKAndQcross /\
      a.b4volSelectedBySourceMeasure /\
      a.pressureAndPiTransportClosed /\
      a.splitNoetherIdentitiesClosed /\
      a.noScalarAbsorption }

def allDynamicAxiomsHold (a : DynamicActionAxioms) : Prop :=
  a.sourceActionExists /\
  a.actionVariationEquationsWritten /\
  a.bridgeSelectedByEulerLagrange /\
  a.sameBridgeForKAndQcross /\
  a.b4volSelectedBySourceMeasure /\
  a.pressureAndPiTransportClosed /\
  a.splitNoetherIdentitiesClosed /\
  a.noScalarAbsorption

inductive DynamicAxiomName where
  | sourceAction
  | actionVariation
  | bridgeEulerLagrange
  | sameBridge
  | b4volMeasure
  | pressurePiTransport
  | splitNoether
  | noScalarAbsorption
deriving DecidableEq

def dynamicAxiomHolds (a : DynamicActionAxioms) : DynamicAxiomName -> Prop
  | DynamicAxiomName.sourceAction => a.sourceActionExists
  | DynamicAxiomName.actionVariation => a.actionVariationEquationsWritten
  | DynamicAxiomName.bridgeEulerLagrange => a.bridgeSelectedByEulerLagrange
  | DynamicAxiomName.sameBridge => a.sameBridgeForKAndQcross
  | DynamicAxiomName.b4volMeasure => a.b4volSelectedBySourceMeasure
  | DynamicAxiomName.pressurePiTransport => a.pressureAndPiTransportClosed
  | DynamicAxiomName.splitNoether => a.splitNoetherIdentitiesClosed
  | DynamicAxiomName.noScalarAbsorption => a.noScalarAbsorption

theorem conditional_closure_from_dynamic_action_axioms
    (a : DynamicActionAxioms)
    (h : allDynamicAxiomsHold a) :
    (closureTargetFromAxioms a).predictionReady := by
  simpa [closureTargetFromAxioms, allDynamicAxiomsHold] using h

theorem prediction_ready_iff_all_dynamic_axioms
    (a : DynamicActionAxioms) :
    (closureTargetFromAxioms a).predictionReady <-> allDynamicAxiomsHold a := by
  rfl

theorem prediction_ready_requires_dynamic_axiom
    (a : DynamicActionAxioms)
    (m : DynamicAxiomName)
    (h : (closureTargetFromAxioms a).predictionReady) :
    dynamicAxiomHolds a m := by
  rcases h with
    ⟨hSource, hVariation, hBridge, hSame, hMeasure, hPressurePi, hNoether, hNoAbsorb⟩
  cases m with
  | sourceAction => exact hSource
  | actionVariation => exact hVariation
  | bridgeEulerLagrange => exact hBridge
  | sameBridge => exact hSame
  | b4volMeasure => exact hMeasure
  | pressurePiTransport => exact hPressurePi
  | splitNoether => exact hNoether
  | noScalarAbsorption => exact hNoAbsorb

theorem prediction_blocked_by_missing_dynamic_axiom
    (a : DynamicActionAxioms)
    (m : DynamicAxiomName)
    (hMissing : Not (dynamicAxiomHolds a m)) :
    Not (closureTargetFromAxioms a).predictionReady := by
  intro hReady
  exact hMissing (prediction_ready_requires_dynamic_axiom a m hReady)

theorem closure_requires_no_scalar_absorption
    (a : DynamicActionAxioms)
    (h : (closureTargetFromAxioms a).predictionReady) :
    a.noScalarAbsorption := by
  rcases h with ⟨_, _, _, _, _, _, _, hNoAbsorb⟩
  exact hNoAbsorb

theorem closure_requires_source_action
    (a : DynamicActionAxioms)
    (h : (closureTargetFromAxioms a).predictionReady) :
    a.sourceActionExists := by
  exact h.left

theorem closure_requires_same_bridge
    (a : DynamicActionAxioms)
    (h : (closureTargetFromAxioms a).predictionReady) :
    a.sameBridgeForKAndQcross := by
  exact h.right.right.right.left

theorem no_go_layer_preserved_by_conditional_closure
    (n : NoGoLayer) (a : DynamicActionAxioms)
    (hNoGo :
      n.spathFilterOnlyNotUnique /\
      n.orbifoldFilterOnlyNotUnique /\
      n.solderFilterOnlyNotUnique)
    (_hClosure : (closureTargetFromAxioms a).predictionReady) :
    n.spathFilterOnlyNotUnique /\
    n.orbifoldFilterOnlyNotUnique /\
    n.solderFilterOnlyNotUnique := by
  exact hNoGo

def dustHypothesesFromAxioms (a : DynamicActionAxioms) : BianchiDustHypotheses :=
  { sameSectorConserved := a.splitNoetherIdentitiesClosed
    transportedContinuity := a.b4volSelectedBySourceMeasure
    transportedForceCancellation := a.noScalarAbsorption }

theorem dynamic_axioms_imply_basic_dust_hypotheses
    (a : DynamicActionAxioms)
    (h : allDynamicAxiomsHold a) :
    (dustHypothesesFromAxioms a).sameSectorConserved /\
    (dustHypothesesFromAxioms a).transportedContinuity /\
    (dustHypothesesFromAxioms a).transportedForceCancellation := by
  rcases h with ⟨_, _, _, _, hMeasure, _, hNoether, hNoAbsorb⟩
  exact conditionalDustClosure
    (dustHypothesesFromAxioms a)
    hNoether
    hMeasure
    hNoAbsorb

end P0ClosureAxiomatics
end JanusFormal
