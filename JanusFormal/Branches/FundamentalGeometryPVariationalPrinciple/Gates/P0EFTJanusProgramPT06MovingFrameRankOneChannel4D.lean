import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06MovingFrameDeckConjugation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFixedFrameRankOneChannel4D

/-!
# A deck-fixed rank-one channel in supplied moving frames

The canonical nonzero LL scalar channel of Gate913 is pulled back through the
pointwise linear trivialisations of Gate902.  The resulting dual channel at
the target deck point evaluates the moving-frame deck transform exactly as
the source channel evaluates the original value.  This holds coefficientwise
at every finite jet order.

The Gate901 rank-one quadratic density, its Gate880 Euler covector, and its
explicit affine-plus-quadratic divergence representative are transported by
the same identity.  As in Gate902, the supplied frames are spatially frozen:
there are no derivative corrections and no identification with T02
`coordChange`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06MovingFrameRankOneChannel4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06MovingFrameDeckConjugation4D
open P0EFTJanusProgramPT06CanonicalFixedFrameRankOneChannel4D
open P0EFTJanusProgramPT06ScalarDirectedQuadraticExactness4D
open P0EFTJanusProgramPT06T02RankOneDirectedQuadraticExactness4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D
open P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional

universe u

private abbrev Fiber := ActualPhysicalValueProductFiber
private abbrev Jet (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

local instance actualPhysicalValueProductFiniteDimensional :
    FiniteDimensional Real Fiber := by
  let injection : Fiber →ₗ[Real] Jet 2 :=
    (programPT06ThroatSpatialJetCoordinateInjection
      (Fiber := Fiber) programPT06SecondOrderZeroMultiIndex).toLinearMap
  exact FiniteDimensional.of_injective injection (by
    intro first second hEqual
    have hAtZero := congrArg
      (fun jet : Jet 2 => jet programPT06SecondOrderZeroMultiIndex) hEqual
    simpa [injection] using hAtZero)

variable {Base : Type u} [AddAction Int Base]

/-- The canonical LL covector expressed in the moving coefficient frame at
one base point. -/
noncomputable def programPT06ActualPhysicalMovingLLScalarChannel
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (point : Base) : Fiber →L[Real] Real :=
  programPT06ActualPhysicalCanonicalLLScalarChannel.comp
    (trivialization.toFixed point).toContinuousLinearEquiv.toContinuousLinearMap

omit [AddAction Int Base] in
@[simp] theorem programPT06ActualPhysicalMovingLLScalarChannel_apply
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (point : Base) (value : Fiber) :
    programPT06ActualPhysicalMovingLLScalarChannel trivialization point value =
      programPT06ActualPhysicalCanonicalLLScalarChannel
        (trivialization.toFixed point value) := by
  simp [programPT06ActualPhysicalMovingLLScalarChannel]

/-- Pull the fixed-frame unit witness back to the moving frame. -/
def programPT06ActualPhysicalMovingLLScalarChannelUnit
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (point : Base) : Fiber :=
  (trivialization.toFixed point).symm
    programPT06ActualPhysicalCanonicalLLScalarChannelUnit

omit [AddAction Int Base] in
@[simp] theorem programPT06ActualPhysicalMovingLLScalarChannel_unit
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (point : Base) :
    programPT06ActualPhysicalMovingLLScalarChannel trivialization point
        (programPT06ActualPhysicalMovingLLScalarChannelUnit
          trivialization point) = 1 := by
  rw [programPT06ActualPhysicalMovingLLScalarChannel_apply]
  change programPT06ActualPhysicalCanonicalLLScalarChannel
      ((trivialization.toFixed point)
        ((trivialization.toFixed point).symm
          programPT06ActualPhysicalCanonicalLLScalarChannelUnit)) = 1
  rw [LinearEquiv.apply_symm_apply]
  exact programPT06ActualPhysicalCanonicalLLScalarChannel_unit

omit [AddAction Int Base] in
/-- Every moving-frame LL channel is nonzero. -/
theorem programPT06ActualPhysicalMovingLLScalarChannel_ne_zero
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (point : Base) :
    programPT06ActualPhysicalMovingLLScalarChannel trivialization point ≠ 0 := by
  intro hZero
  have hAtUnit :
      programPT06ActualPhysicalMovingLLScalarChannel trivialization point
          (programPT06ActualPhysicalMovingLLScalarChannelUnit
            trivialization point) = 0 := by
    rw [hZero]
    rfl
  have hOne :=
    programPT06ActualPhysicalMovingLLScalarChannel_unit trivialization point
  exact one_ne_zero (hOne.symm.trans hAtUnit)

/-- Dual invariance under the conjugated moving-frame value action. -/
theorem programPT06ActualPhysicalMovingLLScalarChannel_deck_invariant
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base)
    (value : Fiber) :
    programPT06ActualPhysicalMovingLLScalarChannel trivialization
        (programPT06MovingFrameDeckPoint winding point)
        (programPT06ActualPhysicalMovingFrameValueDeckAction
          trivialization choice winding point value) =
      programPT06ActualPhysicalMovingLLScalarChannel trivialization point
        value := by
  rw [programPT06ActualPhysicalMovingLLScalarChannel_apply,
    programPT06ActualPhysicalMovingFrameValueDeckAction_toFixed,
    programPT06ActualPhysicalCanonicalLLScalarChannel_deck_invariant,
    programPT06ActualPhysicalMovingLLScalarChannel_apply]

/-- Coefficientwise dual invariance at every finite jet order. -/
theorem programPT06ActualPhysicalMovingLLScalarChannel_jet_deck_invariant
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base)
    (order : Nat) (jet : Jet order)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06ActualPhysicalMovingLLScalarChannel trivialization
        (programPT06MovingFrameDeckPoint winding point)
        (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
          choice winding point order jet index) =
      programPT06ActualPhysicalMovingLLScalarChannel trivialization point
        (jet index) := by
  change
    programPT06ActualPhysicalMovingLLScalarChannel trivialization
        (programPT06MovingFrameDeckPoint winding point)
        (programPT06ActualPhysicalMovingFrameValueDeckAction
          trivialization choice winding point (jet index)) = _
  exact programPT06ActualPhysicalMovingLLScalarChannel_deck_invariant
    trivialization choice winding point (jet index)

/-- Scalarisation of a moving jet is independent of the deck representative
when its point-dependent dual channel is transported with it. -/
theorem programPT06ActualPhysicalMovingLLScalarizeJet_deck_invariant
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base)
    (order : Nat) (jet : Jet order) :
    programPT06T02RankOneScalarizeJet order
        (programPT06ActualPhysicalMovingLLScalarChannel trivialization
          (programPT06MovingFrameDeckPoint winding point))
        (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
          choice winding point order jet) =
      programPT06T02RankOneScalarizeJet order
        (programPT06ActualPhysicalMovingLLScalarChannel trivialization point)
        jet := by
  funext index
  exact programPT06ActualPhysicalMovingLLScalarChannel_jet_deck_invariant
    trivialization choice winding point order jet index

/-- Lift Gate901 coefficients through the moving LL channel at one point. -/
def programPT06ActualPhysicalMovingLLRankOneDensity
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (point : Base)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    ProgramPT06T02RankOneDirectedQuadraticDensity4D where
  direction := density.direction
  channel := programPT06ActualPhysicalMovingLLScalarChannel trivialization point
  channel_ne_zero :=
    programPT06ActualPhysicalMovingLLScalarChannel_ne_zero
      trivialization point
  constant := density.constant
  valueLinear := density.valueLinear
  firstLinear := density.firstLinear
  valueSquare := density.valueSquare
  valueFirst := density.valueFirst
  firstSquare := density.firstSquare

omit [AddAction Int Base] in
@[simp] theorem programPT06ActualPhysicalMovingLLRankOneDensity_toScalar
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (point : Base)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    (programPT06ActualPhysicalMovingLLRankOneDensity
      trivialization point density).toScalarDensity = density := by
  rfl

/-- The point-dependent rank-one density is invariant under simultaneous
transport of its channel and second jet. -/
theorem programPT06ActualPhysicalMovingLLRankOneDensity_deck_invariant
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : Jet 2) :
    programPT06T02RankOneDirectedQuadraticDensityEvaluation
        (programPT06ActualPhysicalMovingLLRankOneDensity trivialization
          (programPT06MovingFrameDeckPoint winding point) density)
        (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
          choice winding point 2 jet) =
      programPT06T02RankOneDirectedQuadraticDensityEvaluation
        (programPT06ActualPhysicalMovingLLRankOneDensity trivialization point
          density) jet := by
  change
    programPT06ScalarDirectedQuadraticDensityEvaluation density
        (programPT06T02RankOneScalarizeJet 2
          (programPT06ActualPhysicalMovingLLScalarChannel trivialization
            (programPT06MovingFrameDeckPoint winding point))
          (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
            choice winding point 2 jet)) =
      programPT06ScalarDirectedQuadraticDensityEvaluation density
        (programPT06T02RankOneScalarizeJet 2
          (programPT06ActualPhysicalMovingLLScalarChannel trivialization point)
          jet)
  rw [programPT06ActualPhysicalMovingLLScalarizeJet_deck_invariant]

/-- Gate880 Euler naturality under simultaneous moving-frame transport of
the fourth jet, variation, and dual channel. -/
theorem programPT06SecondOrderLocalEuler_movingLLRankOne_deck_invariant
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : Jet 4) (variation : Fiber) :
    programPT06SecondOrderLocalEuler
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation
          (programPT06ActualPhysicalMovingLLRankOneDensity trivialization
            (programPT06MovingFrameDeckPoint winding point) density))
        (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
          choice winding point 4 jet)
        (programPT06ActualPhysicalMovingFrameValueDeckAction trivialization
          choice winding point variation) =
      programPT06SecondOrderLocalEuler
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation
          (programPT06ActualPhysicalMovingLLRankOneDensity trivialization point
            density)) jet variation := by
  rw [programPT06SecondOrderLocalEuler_t02RankOneDirectedQuadratic_formula,
    programPT06SecondOrderLocalEuler_t02RankOneDirectedQuadratic_formula]
  simp only [programPT06ActualPhysicalMovingLLRankOneDensity]
  rw [programPT06ActualPhysicalMovingLLScalarChannel_jet_deck_invariant,
    programPT06ActualPhysicalMovingLLScalarChannel_jet_deck_invariant]
  change
    _ * programPT06ActualPhysicalMovingLLScalarChannel trivialization
        (programPT06MovingFrameDeckPoint winding point)
        (programPT06ActualPhysicalMovingFrameValueDeckAction trivialization
          choice winding point variation) =
      _ * programPT06ActualPhysicalMovingLLScalarChannel trivialization point
        variation
  rw [programPT06ActualPhysicalMovingLLScalarChannel_deck_invariant]

/-- In the Euler-null coefficient sector, the explicit divergence
representative is invariant between the source and target moving frames. -/
theorem programPT06MovingLLRankOne_divergenceRepresentative_deck_invariant
    (trivialization : ProgramPT06MovingPhysicalTrivialization4D Base)
    (choice : NormalRootChoice) (winding : Int) (point : Base)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (hLinear : density.valueLinear = 0)
    (hValueSquare : density.valueSquare = 0)
    (hFirstSquare : density.firstSquare = 0)
    (jet : Jet 2) :
    let targetDensity :=
      programPT06ActualPhysicalMovingLLRankOneDensity trivialization
        (programPT06MovingFrameDeckPoint winding point) density
    let sourceDensity :=
      programPT06ActualPhysicalMovingLLRankOneDensity trivialization point
        density
    programPT06AffineHorizontalCurrentDivergence
        (programPT06T02RankOneDirectedQuadraticAffineCurrent targetDensity)
        (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
          choice winding point 2 jet) +
      programPT06DirectedQuadraticValueCurrentDivergence
        (programPT06T02RankOneDirectedQuadraticNonlinearCurrent targetDensity)
        (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
          choice winding point 2 jet) =
      programPT06AffineHorizontalCurrentDivergence
          (programPT06T02RankOneDirectedQuadraticAffineCurrent sourceDensity)
          jet +
        programPT06DirectedQuadraticValueCurrentDivergence
          (programPT06T02RankOneDirectedQuadraticNonlinearCurrent sourceDensity)
          jet := by
  dsimp only
  have hActed :=
    programPT06T02RankOneDirectedQuadratic_eq_constant_add_divergences
      (programPT06ActualPhysicalMovingLLRankOneDensity trivialization
        (programPT06MovingFrameDeckPoint winding point) density)
      hLinear hValueSquare hFirstSquare
      (programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
        choice winding point 2 jet)
  have hOriginal :=
    programPT06T02RankOneDirectedQuadratic_eq_constant_add_divergences
      (programPT06ActualPhysicalMovingLLRankOneDensity trivialization point
        density)
      hLinear hValueSquare hFirstSquare jet
  have hEvaluation :=
    programPT06ActualPhysicalMovingLLRankOneDensity_deck_invariant
      trivialization choice winding point density jet
  have hConstant :
      (programPT06ActualPhysicalMovingLLRankOneDensity trivialization
        (programPT06MovingFrameDeckPoint winding point) density).constant =
        (programPT06ActualPhysicalMovingLLRankOneDensity trivialization point
          density).constant := by
    rfl
  linarith

end
end P0EFTJanusProgramPT06MovingFrameRankOneChannel4D
end JanusFormal
