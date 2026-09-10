import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFixedFrameDeckData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02RankOneDirectedQuadraticExactness4D

/-!
# A deck-fixed rank-one channel in the canonical frame

The real LL-measure slot of the complete physical value product is fixed by
the canonical fixed-frame deck action of Gate896.  Projection to that slot
therefore gives an explicit nonzero continuous real covector.  Its
coefficientwise scalarization is fixed on every finite spatial jet order; the
orders zero through four are recorded explicitly below.

For every directed quadratic density using this channel, evaluation and the
Gate880 Euler expression are deck invariant.  In the Euler-null case the
explicit affine-plus-quadratic `dH` representative is invariant as well.

All statements are confined to Gate896's canonical fixed product frame.
They assert no compatibility with the varying-frame `coordChange` maps of
the T02 second-jet bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalFixedFrameRankOneChannel4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D
open P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D
open P0EFTJanusProgramPT06ScalarDirectedQuadraticExactness4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06CanonicalFixedFrameDeckData4D
open P0EFTJanusProgramPT06T02RankOneDirectedQuadraticExactness4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace

private abbrev Fiber := ActualPhysicalValueProductFiber
private abbrev Jet (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

/-- Projection to the real LL-measure slot of the eleven-component physical
value product. -/
noncomputable def programPT06ActualPhysicalCanonicalLLScalarChannel :
    Fiber →L[Real] Real :=
  let gaugeLLMetric :
      Fiber →L[Real]
        ((ActualGaugeValueProductFiber × ActualLLValueProductFiber) ×
          ActualMetricValueProductFiber) :=
    ContinuousLinearMap.fst Real _ _
  let gaugeLL :
      Fiber →L[Real]
        (ActualGaugeValueProductFiber × ActualLLValueProductFiber) :=
    (ContinuousLinearMap.fst Real _ _).comp gaugeLLMetric
  let ll : Fiber →L[Real] ActualLLValueProductFiber :=
    (ContinuousLinearMap.snd Real _ _).comp gaugeLL
  let llMetricScalar : Fiber →L[Real] (LLMetricFiber × Real) :=
    (ContinuousLinearMap.fst Real _ _).comp ll
  (ContinuousLinearMap.snd Real _ _).comp llMetricScalar

@[simp] theorem programPT06ActualPhysicalCanonicalLLScalarChannel_apply
    (value : Fiber) :
    programPT06ActualPhysicalCanonicalLLScalarChannel value =
      value.1.1.2.1.2 := by
  rfl

/-- An explicit value detected by the canonical LL scalar channel. -/
def programPT06ActualPhysicalCanonicalLLScalarChannelUnit : Fiber :=
  (((0, ((0, 1), 0)), 0), 0)

@[simp] theorem programPT06ActualPhysicalCanonicalLLScalarChannel_unit :
    programPT06ActualPhysicalCanonicalLLScalarChannel
        programPT06ActualPhysicalCanonicalLLScalarChannelUnit = 1 := by
  rfl

/-- The canonical LL scalar channel is genuinely nonzero. -/
theorem programPT06ActualPhysicalCanonicalLLScalarChannel_ne_zero :
    programPT06ActualPhysicalCanonicalLLScalarChannel ≠ 0 := by
  intro hZero
  have hAtUnit :
      programPT06ActualPhysicalCanonicalLLScalarChannel
          programPT06ActualPhysicalCanonicalLLScalarChannelUnit = 0 := by
    rw [hZero]
    rfl
  have hOne :
      programPT06ActualPhysicalCanonicalLLScalarChannel
          programPT06ActualPhysicalCanonicalLLScalarChannelUnit = 1 :=
    programPT06ActualPhysicalCanonicalLLScalarChannel_unit
  exact one_ne_zero (hOne.symm.trans hAtUnit)

/-- The canonical value deck action fixes the selected real slot. -/
@[simp] theorem programPT06ActualPhysicalCanonicalLLScalarChannel_deck_invariant
    (choice : NormalRootChoice) (winding : Int) (value : Fiber) :
    programPT06ActualPhysicalCanonicalLLScalarChannel
        (programPT06ActualPhysicalCanonicalValueDeckAction
          choice winding value) =
      programPT06ActualPhysicalCanonicalLLScalarChannel value := by
  rfl

/-- Coefficientwise deck invariance at an arbitrary finite jet order. -/
@[simp] theorem programPT06ActualPhysicalCanonicalLLScalarChannel_jet_deck_invariant
    (choice : NormalRootChoice) (winding : Int) (order : Nat)
    (jet : Jet order) (index : ThroatSpatialTruncatedIndex order) :
    programPT06ActualPhysicalCanonicalLLScalarChannel
        (programPT06ActualPhysicalCanonicalJetDeckAction
          choice winding order jet index) =
      programPT06ActualPhysicalCanonicalLLScalarChannel (jet index) := by
  exact programPT06ActualPhysicalCanonicalLLScalarChannel_deck_invariant
    choice winding (jet index)

/-- Scalarization by the canonical channel commutes with the deck action at
every finite order. -/
theorem programPT06ActualPhysicalCanonicalLLScalarizeJet_deck_invariant
    (choice : NormalRootChoice) (winding : Int) (order : Nat)
    (jet : Jet order) :
    programPT06T02RankOneScalarizeJet order
        programPT06ActualPhysicalCanonicalLLScalarChannel
        (programPT06ActualPhysicalCanonicalJetDeckAction
          choice winding order jet) =
      programPT06T02RankOneScalarizeJet order
        programPT06ActualPhysicalCanonicalLLScalarChannel jet := by
  funext index
  exact programPT06ActualPhysicalCanonicalLLScalarChannel_jet_deck_invariant
    choice winding order jet index

theorem programPT06ActualPhysicalCanonicalLLScalarizeJet0_deck_invariant
    (choice : NormalRootChoice) (winding : Int)
    (jet : ThroatSpatialMultiindexJet0 Fiber) :
    programPT06T02RankOneScalarizeJet 0
        programPT06ActualPhysicalCanonicalLLScalarChannel
        (programPT06ActualPhysicalCanonicalJetDeckAction
          choice winding 0 jet) =
      programPT06T02RankOneScalarizeJet 0
        programPT06ActualPhysicalCanonicalLLScalarChannel jet :=
  programPT06ActualPhysicalCanonicalLLScalarizeJet_deck_invariant
    choice winding 0 jet

theorem programPT06ActualPhysicalCanonicalLLScalarizeJet1_deck_invariant
    (choice : NormalRootChoice) (winding : Int)
    (jet : ThroatSpatialMultiindexJet1 Fiber) :
    programPT06T02RankOneScalarizeJet 1
        programPT06ActualPhysicalCanonicalLLScalarChannel
        (programPT06ActualPhysicalCanonicalJetDeckAction
          choice winding 1 jet) =
      programPT06T02RankOneScalarizeJet 1
        programPT06ActualPhysicalCanonicalLLScalarChannel jet :=
  programPT06ActualPhysicalCanonicalLLScalarizeJet_deck_invariant
    choice winding 1 jet

theorem programPT06ActualPhysicalCanonicalLLScalarizeJet2_deck_invariant
    (choice : NormalRootChoice) (winding : Int)
    (jet : ThroatSpatialMultiindexJet2 Fiber) :
    programPT06T02RankOneScalarizeJet 2
        programPT06ActualPhysicalCanonicalLLScalarChannel
        (programPT06ActualPhysicalCanonicalJetDeckAction
          choice winding 2 jet) =
      programPT06T02RankOneScalarizeJet 2
        programPT06ActualPhysicalCanonicalLLScalarChannel jet :=
  programPT06ActualPhysicalCanonicalLLScalarizeJet_deck_invariant
    choice winding 2 jet

theorem programPT06ActualPhysicalCanonicalLLScalarizeJet3_deck_invariant
    (choice : NormalRootChoice) (winding : Int)
    (jet : ThroatSpatialMultiindexJet3 Fiber) :
    programPT06T02RankOneScalarizeJet 3
        programPT06ActualPhysicalCanonicalLLScalarChannel
        (programPT06ActualPhysicalCanonicalJetDeckAction
          choice winding 3 jet) =
      programPT06T02RankOneScalarizeJet 3
        programPT06ActualPhysicalCanonicalLLScalarChannel jet :=
  programPT06ActualPhysicalCanonicalLLScalarizeJet_deck_invariant
    choice winding 3 jet

theorem programPT06ActualPhysicalCanonicalLLScalarizeJet4_deck_invariant
    (choice : NormalRootChoice) (winding : Int)
    (jet : ThroatSpatialMultiindexJet4 Fiber) :
    programPT06T02RankOneScalarizeJet 4
        programPT06ActualPhysicalCanonicalLLScalarChannel
        (programPT06ActualPhysicalCanonicalJetDeckAction
          choice winding 4 jet) =
      programPT06T02RankOneScalarizeJet 4
        programPT06ActualPhysicalCanonicalLLScalarChannel jet :=
  programPT06ActualPhysicalCanonicalLLScalarizeJet_deck_invariant
    choice winding 4 jet

/-- Lift any Gate901 scalar coefficient package through the explicit
deck-fixed physical channel. -/
def programPT06ActualPhysicalCanonicalLLRankOneDensity
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    ProgramPT06T02RankOneDirectedQuadraticDensity4D where
  direction := density.direction
  channel := programPT06ActualPhysicalCanonicalLLScalarChannel
  channel_ne_zero :=
    programPT06ActualPhysicalCanonicalLLScalarChannel_ne_zero
  constant := density.constant
  valueLinear := density.valueLinear
  firstLinear := density.firstLinear
  valueSquare := density.valueSquare
  valueFirst := density.valueFirst
  firstSquare := density.firstSquare

@[simp] theorem programPT06ActualPhysicalCanonicalLLRankOneDensity_channel
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    (programPT06ActualPhysicalCanonicalLLRankOneDensity density).channel =
      programPT06ActualPhysicalCanonicalLLScalarChannel := by
  rfl

/-- Every rank-one density using the canonical channel is deck invariant. -/
theorem programPT06T02RankOneDirectedQuadraticDensity_deck_invariant
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (hChannel : density.channel =
      programPT06ActualPhysicalCanonicalLLScalarChannel)
    (choice : NormalRootChoice) (winding : Int)
    (jet : ThroatSpatialMultiindexJet2 Fiber) :
    programPT06T02RankOneDirectedQuadraticDensityEvaluation density
        (programPT06ActualPhysicalCanonicalJetDeckAction
          choice winding 2 jet) =
      programPT06T02RankOneDirectedQuadraticDensityEvaluation density jet := by
  have hScalar :
      programPT06T02RankOneScalarizeJet 2 density.channel
          (programPT06ActualPhysicalCanonicalJetDeckAction
            choice winding 2 jet) =
        programPT06T02RankOneScalarizeJet 2 density.channel jet := by
    simpa only [hChannel] using
      programPT06ActualPhysicalCanonicalLLScalarizeJet2_deck_invariant
        choice winding jet
  change
    programPT06ScalarDirectedQuadraticDensityEvaluation density.toScalarDensity
        (programPT06T02RankOneScalarizeJet 2 density.channel
          (programPT06ActualPhysicalCanonicalJetDeckAction
            choice winding 2 jet)) =
      programPT06ScalarDirectedQuadraticDensityEvaluation density.toScalarDensity
        (programPT06T02RankOneScalarizeJet 2 density.channel jet)
  rw [hScalar]

/-- Pointwise naturality of the Gate880 Euler covector under simultaneous
deck transport of the fourth jet and its variation. -/
theorem programPT06SecondOrderLocalEuler_t02RankOne_deck_invariant
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (hChannel : density.channel =
      programPT06ActualPhysicalCanonicalLLScalarChannel)
    (choice : NormalRootChoice) (winding : Int)
    (jet : ThroatSpatialMultiindexJet4 Fiber) (variation : Fiber) :
    programPT06SecondOrderLocalEuler
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
        (programPT06ActualPhysicalCanonicalJetDeckAction
          choice winding 4 jet)
        (programPT06ActualPhysicalCanonicalValueDeckAction
          choice winding variation) =
      programPT06SecondOrderLocalEuler
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
        jet variation := by
  rw [programPT06SecondOrderLocalEuler_t02RankOneDirectedQuadratic_formula,
    programPT06SecondOrderLocalEuler_t02RankOneDirectedQuadratic_formula,
    hChannel]
  simp only [
    programPT06ActualPhysicalCanonicalLLScalarChannel_jet_deck_invariant]
  change
    _ * programPT06ActualPhysicalCanonicalLLScalarChannel
        (programPT06ActualPhysicalCanonicalValueDeckAction
          choice winding variation) =
      _ * programPT06ActualPhysicalCanonicalLLScalarChannel variation
  rw [programPT06ActualPhysicalCanonicalLLScalarChannel_deck_invariant]

/-- In the Euler-null case, the displayed affine-plus-quadratic horizontal
differential is itself fixed by the canonical deck action. -/
theorem programPT06T02RankOne_divergenceRepresentative_deck_invariant
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (hChannel : density.channel =
      programPT06ActualPhysicalCanonicalLLScalarChannel)
    (hLinear : density.valueLinear = 0)
    (hValueSquare : density.valueSquare = 0)
    (hFirstSquare : density.firstSquare = 0)
    (choice : NormalRootChoice) (winding : Int)
    (jet : ThroatSpatialMultiindexJet2 Fiber) :
    programPT06AffineHorizontalCurrentDivergence
        (programPT06T02RankOneDirectedQuadraticAffineCurrent density)
        (programPT06ActualPhysicalCanonicalJetDeckAction
          choice winding 2 jet) +
      programPT06DirectedQuadraticValueCurrentDivergence
        (programPT06T02RankOneDirectedQuadraticNonlinearCurrent density)
        (programPT06ActualPhysicalCanonicalJetDeckAction
          choice winding 2 jet) =
      programPT06AffineHorizontalCurrentDivergence
          (programPT06T02RankOneDirectedQuadraticAffineCurrent density) jet +
        programPT06DirectedQuadraticValueCurrentDivergence
          (programPT06T02RankOneDirectedQuadraticNonlinearCurrent density) jet := by
  have hActed :=
    programPT06T02RankOneDirectedQuadratic_eq_constant_add_divergences
      density hLinear hValueSquare hFirstSquare
      (programPT06ActualPhysicalCanonicalJetDeckAction
        choice winding 2 jet)
  have hOriginal :=
    programPT06T02RankOneDirectedQuadratic_eq_constant_add_divergences
      density hLinear hValueSquare hFirstSquare jet
  have hEvaluation :=
    programPT06T02RankOneDirectedQuadraticDensity_deck_invariant
      density hChannel choice winding jet
  linarith

end
end P0EFTJanusProgramPT06CanonicalFixedFrameRankOneChannel4D
end JanusFormal
