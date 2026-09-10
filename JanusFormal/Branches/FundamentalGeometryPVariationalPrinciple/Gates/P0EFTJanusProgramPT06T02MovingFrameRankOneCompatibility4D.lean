import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06MovingFrameRankOneChannel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02InvariantRankOneQuadraticBridge4D

/-!
# T02 compatibility of the moving-frame LL rank-one channel

This gate isolates the missing atlas input needed to turn Gate902's frozen
moving-frame transport into a genuine T02 transition statement.  On every
actual T02 overlap, the supplied data choose compatible cover lifts and an
integer winding, and require Gate881's inverse bridge to intertwine the
actual `coordChange` with the coefficientwise moving deck action.  The
moving LL covector is also required to agree with one anchor covector on
each valid chart lift.

These lower-level compatibility equations imply, rather than assume, the
linear and symmetric-bilinear transition-invariance witnesses required by
Gate910.  Hence every Gate901 scalar coefficient package yields an actual
`ProgramPT02AdmissibleInvariantLocalFunctional4D`.

The result remains conditional on constructing the displayed compatibility
data from the physical atlas.  In particular, this gate does not identify
Gate902's frozen prolongation with the derivative-corrected T02 transition,
and it does not assert the unrestricted T06 kernel classification.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02MovingFrameRankOneCompatibility4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuadraticFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06MovingFrameDeckConjugation4D
open P0EFTJanusProgramPT06MovingFrameRankOneChannel4D
open P0EFTJanusProgramPT06ScalarDirectedQuadraticExactness4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D
open P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06T02RankOneDirectedQuadraticExactness4D
open P0EFTJanusProgramPT06T02InvariantRankOneQuadraticBridge4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Cover :=
  ProgramPT06ActualFixedThroatCover4D period hPeriod

private abbrev Base :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev Chart :=
  ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod

private abbrev ValueFiber := ActualPhysicalValueProductFiber

private abbrev PhysicalSecondJet :=
  ActualPhysicalSecondOrderJetProductFiber

private abbrev FinsuppSecondJet :=
  ThroatSpatialMultiindexJet2 ValueFiber

private abbrev FinsuppFourthJet :=
  ThroatSpatialMultiindexJet4 ValueFiber

/-- Gate881's inverse bridge, used to compare an actual T02 transition with
the coefficientwise moving-frame action. -/
def programPT06T02MovingFramePullbackSecondJet
    (jet : PhysicalSecondJet) : FinsuppSecondJet :=
  programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv.symm
    jet

/-- Concrete atlas compatibility needed by the moving LL channel.

`coordChange_intertwines` is an equality of the raw second-jet transports;
`channel_eq_anchor` only identifies the pointwise LL covectors on valid
chart lifts.  Neither field states invariance of the resulting linear or
quadratic T02 functional. -/
structure ProgramPT06T02MovingFrameJetCompatibility4D where
  trivialization : ProgramPT06MovingPhysicalTrivialization4D
    (Cover period hPeriod)
  anchor : Cover period hPeriod
  chartLift : Chart period hPeriod -> Base period hPeriod ->
    Cover period hPeriod
  transitionWinding : Chart period hPeriod -> Chart period hPeriod ->
    Base period hPeriod -> Int
  target_point :
    forall (first second : Chart period hPeriod)
      (base : Base period hPeriod),
      base ∈
          (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
            .positiveQuarter).baseSet first ∩
          (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
            .positiveQuarter).baseSet second ->
        programPT06MovingFrameDeckPoint
            (transitionWinding first second base)
            (chartLift first base) =
          chartLift second base
  channel_eq_anchor :
    forall (chart : Chart period hPeriod) (base : Base period hPeriod),
      base ∈
          (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
            .positiveQuarter).baseSet chart ->
        programPT06ActualPhysicalMovingLLScalarChannel trivialization
            (chartLift chart base) =
          programPT06ActualPhysicalMovingLLScalarChannel trivialization anchor
  coordChange_intertwines :
    forall (first second : Chart period hPeriod)
      (base : Base period hPeriod),
      base ∈
          (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
            .positiveQuarter).baseSet first ∩
          (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
            .positiveQuarter).baseSet second ->
        forall jet : PhysicalSecondJet,
          programPT06T02MovingFramePullbackSecondJet
              ((actualPhysicalSecondOrderJetProductVectorBundleCore
                period hPeriod .positiveQuarter).coordChange
                first second base jet) =
            programPT06ActualPhysicalMovingFrameJetDeckAction trivialization
              .positiveQuarter (transitionWinding first second base)
              (chartLift first base) 2
              (programPT06T02MovingFramePullbackSecondJet jet)

/-- Every scalar coefficient of the Gate881 pullback is fixed by an actual
T02 transition once the raw transport compatibility is supplied. -/
theorem programPT06T02MovingLLScalarCoordinate_transitionInvariant
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : PhysicalSecondJet)
    (index : ThroatSpatialTruncatedIndex 2) :
    programPT06ActualPhysicalMovingLLScalarChannel
        compatibility.trivialization compatibility.anchor
        (programPT06T02MovingFramePullbackSecondJet
          ((actualPhysicalSecondOrderJetProductVectorBundleCore
            period hPeriod .positiveQuarter).coordChange
            first second base jet) index) =
      programPT06ActualPhysicalMovingLLScalarChannel
        compatibility.trivialization compatibility.anchor
        (programPT06T02MovingFramePullbackSecondJet jet index) := by
  rw [compatibility.coordChange_intertwines first second base hBase jet]
  have hDeck :=
    programPT06ActualPhysicalMovingLLScalarChannel_jet_deck_invariant
      compatibility.trivialization .positiveQuarter
      (compatibility.transitionWinding first second base)
      (compatibility.chartLift first base) 2
      (programPT06T02MovingFramePullbackSecondJet jet) index
  rw [compatibility.target_point first second base hBase] at hDeck
  rw [compatibility.channel_eq_anchor second base hBase.2,
    compatibility.channel_eq_anchor first base hBase.1] at hDeck
  exact hDeck

/-- Gate914's moving-frame density, anchored once so that it defines one
fixed model-fiber expression for T02. -/
def programPT06T02MovingFrameRankOneDensity
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    ProgramPT06T02RankOneDirectedQuadraticDensity4D :=
  programPT06ActualPhysicalMovingLLRankOneDensity
    compatibility.trivialization compatibility.anchor density

@[simp] theorem programPT06T02MovingFrameRankOneDensity_channel
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    (programPT06T02MovingFrameRankOneDensity
      period hPeriod compatibility density).channel =
      programPT06ActualPhysicalMovingLLScalarChannel
        compatibility.trivialization compatibility.anchor := by
  rfl

/-- The value coordinate used by Gate910 is fixed by every actual T02
transition. -/
theorem programPT06T02MovingFramePhysicalValueChannel_transitionInvariant
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : PhysicalSecondJet) :
    programPT06T02RankOnePhysicalValueChannel
        (programPT06T02MovingFrameRankOneDensity
          period hPeriod compatibility density)
        ((actualPhysicalSecondOrderJetProductVectorBundleCore
          period hPeriod .positiveQuarter).coordChange
          first second base jet) =
      programPT06T02RankOnePhysicalValueChannel
        (programPT06T02MovingFrameRankOneDensity
          period hPeriod compatibility density) jet := by
  change
    (programPT06T02MovingFrameRankOneDensity
      period hPeriod compatibility density).channel
        (programPT06T02MovingFramePullbackSecondJet
          ((actualPhysicalSecondOrderJetProductVectorBundleCore
            period hPeriod .positiveQuarter).coordChange
            first second base jet) programPT06SecondOrderZeroMultiIndex) =
      (programPT06T02MovingFrameRankOneDensity
        period hPeriod compatibility density).channel
        (programPT06T02MovingFramePullbackSecondJet jet
          programPT06SecondOrderZeroMultiIndex)
  rw [programPT06T02MovingFrameRankOneDensity_channel]
  exact programPT06T02MovingLLScalarCoordinate_transitionInvariant
    period hPeriod compatibility first second base hBase jet
    programPT06SecondOrderZeroMultiIndex

/-- The selected first-jet coordinate used by Gate910 is fixed by every
actual T02 transition. -/
theorem programPT06T02MovingFramePhysicalFirstChannel_transitionInvariant
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : PhysicalSecondJet) :
    programPT06T02RankOnePhysicalFirstChannel
        (programPT06T02MovingFrameRankOneDensity
          period hPeriod compatibility density)
        ((actualPhysicalSecondOrderJetProductVectorBundleCore
          period hPeriod .positiveQuarter).coordChange
          first second base jet) =
      programPT06T02RankOnePhysicalFirstChannel
        (programPT06T02MovingFrameRankOneDensity
          period hPeriod compatibility density) jet := by
  change
    (programPT06T02MovingFrameRankOneDensity
      period hPeriod compatibility density).channel
        (programPT06T02MovingFramePullbackSecondJet
          ((actualPhysicalSecondOrderJetProductVectorBundleCore
            period hPeriod .positiveQuarter).coordChange
            first second base jet)
          (programPT06SecondOrderFirstMultiIndex density.direction)) =
      (programPT06T02MovingFrameRankOneDensity
        period hPeriod compatibility density).channel
        (programPT06T02MovingFramePullbackSecondJet jet
          (programPT06SecondOrderFirstMultiIndex density.direction))
  rw [programPT06T02MovingFrameRankOneDensity_channel]
  exact programPT06T02MovingLLScalarCoordinate_transitionInvariant
    period hPeriod compatibility first second base hBase jet
    (programPT06SecondOrderFirstMultiIndex density.direction)

/-- First Gate910 witness, derived from the moving-frame compatibility. -/
theorem programPT06T02MovingFrameRankOneLinear_transitionInvariant
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    IsActualPhysicalSecondOrderJetTransitionInvariant period hPeriod
      (programPT06T02RankOnePhysicalLinearForm
        (programPT06T02MovingFrameRankOneDensity
          period hPeriod compatibility density)) := by
  intro first second base hBase jet
  simp only [programPT06T02RankOnePhysicalLinearForm, add_apply, smul_apply]
  rw [programPT06T02MovingFramePhysicalValueChannel_transitionInvariant
      period hPeriod compatibility density first second base hBase jet,
    programPT06T02MovingFramePhysicalFirstChannel_transitionInvariant
      period hPeriod compatibility density first second base hBase jet]

/-- Second Gate910 witness, derived from the same compatibility. -/
theorem programPT06T02MovingFrameRankOneQuadratic_transitionInvariant
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    IsActualPhysicalSecondOrderJetInvariantSymmetricBilinearForm
      period hPeriod
      (programPT06T02RankOnePhysicalQuadraticForm
        (programPT06T02MovingFrameRankOneDensity
          period hPeriod compatibility density)) := by
  constructor
  · exact programPT06T02RankOnePhysicalQuadraticForm_symmetric
      (programPT06T02MovingFrameRankOneDensity
        period hPeriod compatibility density)
  · intro first second base hBase firstJet secondJet
    simp only [programPT06T02RankOnePhysicalQuadraticForm, add_apply,
      smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    rw [programPT06T02MovingFramePhysicalValueChannel_transitionInvariant
        period hPeriod compatibility density first second base hBase firstJet,
      programPT06T02MovingFramePhysicalValueChannel_transitionInvariant
        period hPeriod compatibility density first second base hBase secondJet,
      programPT06T02MovingFramePhysicalFirstChannel_transitionInvariant
        period hPeriod compatibility density first second base hBase firstJet,
      programPT06T02MovingFramePhysicalFirstChannel_transitionInvariant
        period hPeriod compatibility density first second base hBase secondJet]

/-- The two derived witnesses packaged exactly in Gate910's input type. -/
def programPT06T02MovingFrameInvariantRankOneData
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    ProgramPT06T02InvariantRankOneQuadraticData4D period hPeriod where
  density := programPT06T02MovingFrameRankOneDensity
    period hPeriod compatibility density
  linear_transition_invariant :=
    programPT06T02MovingFrameRankOneLinear_transitionInvariant
      period hPeriod compatibility density
  quadratic_transition_invariant :=
    programPT06T02MovingFrameRankOneQuadratic_transitionInvariant
      period hPeriod compatibility density

/-- Actual admissible invariant T02 functional obtained from the supplied
moving-frame/T02 intertwining data. -/
def programPT06T02MovingFrameInvariantRankOneFunctional
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod :=
  programPT06T02InvariantRankOneQuadraticFunctional period hPeriod
    (programPT06T02MovingFrameInvariantRankOneData
      period hPeriod compatibility density)

/-- The constructed functional satisfies the genuine T02 transition law on
every actual overlap. -/
theorem programPT06T02MovingFrameInvariantRankOneFunctional_transitionInvariant
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : PhysicalSecondJet) :
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        (programPT06T02MovingFrameInvariantRankOneFunctional
          period hPeriod compatibility density)
        ((actualPhysicalSecondOrderJetProductVectorBundleCore
          period hPeriod .positiveQuarter).coordChange
          first second base jet) =
      actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        (programPT06T02MovingFrameInvariantRankOneFunctional
          period hPeriod compatibility density) jet := by
  exact
    programPT06T02InvariantRankOneQuadraticFunctional_transitionInvariant
      period hPeriod
      (programPT06T02MovingFrameInvariantRankOneData
        period hPeriod compatibility density)
      first second base hBase jet

/-- Pullback through Gate881 recovers the anchored moving-frame rank-one
density exactly. -/
@[simp] theorem programPT06T02MovingFrameInvariantRankOneLocalLagrangian_evaluation
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
        (programPT06T02MovingFrameInvariantRankOneFunctional
          period hPeriod compatibility density) jet =
      programPT06T02RankOneDirectedQuadraticDensityEvaluation
        (programPT06T02MovingFrameRankOneDensity
          period hPeriod compatibility density) jet := by
  exact programPT06T02InvariantRankOneLocalLagrangian_evaluation
    period hPeriod
    (programPT06T02MovingFrameInvariantRankOneData
      period hPeriod compatibility density) jet

/-- Function-level form of the exact local-Lagrangian identification. -/
theorem programPT06T02MovingFrameInvariantRankOneLocalLagrangian_eq
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
        (programPT06T02MovingFrameInvariantRankOneFunctional
          period hPeriod compatibility density) =
      programPT06T02RankOneDirectedQuadraticDensityEvaluation
        (programPT06T02MovingFrameRankOneDensity
          period hPeriod compatibility density) := by
  exact programPT06T02InvariantRankOneLocalLagrangian_eq
    period hPeriod
    (programPT06T02MovingFrameInvariantRankOneData
      period hPeriod compatibility density)

/-- Gate880 on the admissible T02 functional is exactly Gate880 on its
anchored moving-frame rank-one representative. -/
theorem programPT06SecondOrderLocalEuler_t02MovingFrameInvariantRankOne_eq
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : FinsuppFourthJet) :
    programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
          (programPT06T02MovingFrameInvariantRankOneFunctional
            period hPeriod compatibility density)) jet =
      programPT06SecondOrderLocalEuler
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation
          (programPT06T02MovingFrameRankOneDensity
            period hPeriod compatibility density)) jet := by
  exact programPT06SecondOrderLocalEuler_t02InvariantRankOne_eq
    period hPeriod
    (programPT06T02MovingFrameInvariantRankOneData
      period hPeriod compatibility density) jet

/-- Public fourth-jet value index used in the explicit Euler formula. -/
def programPT06T02MovingFrameFourthOrderZeroMultiIndex :
    ThroatSpatialTruncatedIndex 4 :=
  { val := 0, property := by simp }

/-- Public repeated-direction second-derivative index used in the explicit
Euler formula. -/
def programPT06T02MovingFrameFourthOrderSecondMultiIndex
    (direction : Fin 3) : ThroatSpatialTruncatedIndex 4 :=
  { val :=
      throatSpatialCoordinateMultiIndex direction +
        throatSpatialCoordinateMultiIndex direction
    property := by
      rw [throatSpatialMultiIndexOrder_add]
      simp }

/-- Public scalar multiple of a continuous covector. -/
def programPT06T02MovingFrameScaleCovector
    {Domain : Type} [SeminormedAddCommGroup Domain]
    [NormedSpace Real Domain]
    (coefficient : Real) (covector : Domain →L[Real] Real) :
    Domain →L[Real] Real :=
  (ContinuousLinearMap.lsmul Real Real coefficient).comp covector

/-- Explicit Gate880 formula for the anchored admissible T02 subclass. -/
theorem programPT06SecondOrderLocalEuler_t02MovingFrameInvariantRankOne_formula
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : FinsuppFourthJet) :
    let rankDensity := programPT06T02MovingFrameRankOneDensity
      period hPeriod compatibility density
    programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
          (programPT06T02MovingFrameInvariantRankOneFunctional
            period hPeriod compatibility density)) jet =
      programPT06T02MovingFrameScaleCovector
        (rankDensity.valueLinear +
          2 * rankDensity.valueSquare *
            rankDensity.channel
              (jet programPT06T02MovingFrameFourthOrderZeroMultiIndex) -
          2 * rankDensity.firstSquare *
            rankDensity.channel
              (jet (programPT06T02MovingFrameFourthOrderSecondMultiIndex
                rankDensity.direction)))
        rankDensity.channel := by
  dsimp only
  rw [programPT06SecondOrderLocalEuler_t02MovingFrameInvariantRankOne_eq
    period hPeriod compatibility density jet]
  rw [programPT06SecondOrderLocalEuler_t02RankOneDirectedQuadratic_formula]
  rfl

/-- Exact obstruction criterion for the moving-frame admissible T02
subclass. -/
theorem programPT06_t02MovingFrameInvariantRankOne_euler_eq_zero_iff
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    (forall jet : FinsuppFourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
          (programPT06T02MovingFrameInvariantRankOneFunctional
            period hPeriod compatibility density)) jet = 0) <->
      And (density.valueLinear = 0)
        (And (density.valueSquare = 0) (density.firstSquare = 0)) := by
  simpa only [programPT06T02MovingFrameInvariantRankOneFunctional,
    programPT06T02MovingFrameInvariantRankOneData,
    programPT06T02MovingFrameRankOneDensity,
    programPT06ActualPhysicalMovingLLRankOneDensity] using
    (programPT06_t02InvariantRankOne_euler_eq_zero_iff period hPeriod
      (programPT06T02MovingFrameInvariantRankOneData
        period hPeriod compatibility density))

/-- Vanishing of the three Euler obstructions gives the explicit constant
plus horizontal-divergence representative. -/
theorem programPT06T02MovingFrameInvariantRankOne_eq_constant_add_divergences
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (hLinear : density.valueLinear = 0)
    (hValueSquare : density.valueSquare = 0)
    (hFirstSquare : density.firstSquare = 0)
    (jet : FinsuppSecondJet) :
    let rankDensity := programPT06T02MovingFrameRankOneDensity
      period hPeriod compatibility density
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
        (programPT06T02MovingFrameInvariantRankOneFunctional
          period hPeriod compatibility density) jet =
      rankDensity.constant +
        programPT06AffineHorizontalCurrentDivergence
          (programPT06T02RankOneDirectedQuadraticAffineCurrent rankDensity)
          jet +
        programPT06DirectedQuadraticValueCurrentDivergence
          (programPT06T02RankOneDirectedQuadraticNonlinearCurrent rankDensity)
          jet := by
  dsimp only
  rw [programPT06T02MovingFrameInvariantRankOneLocalLagrangian_evaluation]
  exact programPT06T02RankOneDirectedQuadratic_eq_constant_add_divergences
    (programPT06T02MovingFrameRankOneDensity
      period hPeriod compatibility density)
    hLinear hValueSquare hFirstSquare jet

/-- Euler-nullity alone gives the same explicit representative through the
Gate910 obstruction converse. -/
theorem programPT06T02MovingFrameInvariantRankOne_eq_constant_add_divergences_of_euler
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (hEuler : forall jet : FinsuppFourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
          (programPT06T02MovingFrameInvariantRankOneFunctional
            period hPeriod compatibility density)) jet = 0)
    (jet : FinsuppSecondJet) :
    let rankDensity := programPT06T02MovingFrameRankOneDensity
      period hPeriod compatibility density
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
        (programPT06T02MovingFrameInvariantRankOneFunctional
          period hPeriod compatibility density) jet =
      rankDensity.constant +
        programPT06AffineHorizontalCurrentDivergence
          (programPT06T02RankOneDirectedQuadraticAffineCurrent rankDensity)
          jet +
        programPT06DirectedQuadraticValueCurrentDivergence
          (programPT06T02RankOneDirectedQuadraticNonlinearCurrent rankDensity)
          jet := by
  dsimp only
  exact
    programPT06T02InvariantRankOne_eq_constant_add_divergences_of_euler
      period hPeriod
      (programPT06T02MovingFrameInvariantRankOneData
        period hPeriod compatibility density)
      hEuler jet

end
end P0EFTJanusProgramPT06T02MovingFrameRankOneCompatibility4D
end JanusFormal
