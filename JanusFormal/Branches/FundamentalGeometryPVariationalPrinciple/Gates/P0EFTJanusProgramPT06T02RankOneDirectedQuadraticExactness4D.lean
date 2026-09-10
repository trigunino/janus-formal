import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ScalarDirectedQuadraticExactness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02AffineSecondOrderExactness4D

/-!
# Rank-one directed quadratic exactness on the physical T02 fiber

This gate lifts the scalar classification of Gate901 to the genuine
`ActualPhysicalValueProductFiber`.  A nonzero continuous real covector
selects one scalar channel in that fiber.  The density is exactly Gate901's
six-parameter directed quadratic density evaluated on the coefficientwise
scalarized physical jet.

The genuine Gate880 Euler covector is computed on the physical fourth-jet
carrier.  Nonvanishing of the channel makes it surjective onto `Real`, so
Euler vanishes exactly when the same three obstructing coefficients as in
Gate901 vanish.  The remaining terms are a constant plus genuine Gate879
horizontal divergences of explicit physical affine and quadratic currents.

This is a non-affine rank-one physical channel.  It does not classify
quadratic couplings between different physical channels or the full T02
degree-four Euler kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02RankOneDirectedQuadraticExactness4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D
open P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D
open P0EFTJanusProgramPT06ScalarDirectedQuadraticExactness4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

private abbrev Fiber := ActualPhysicalValueProductFiber
private abbrev FirstJet := ThroatSpatialMultiindexJet1 Fiber
private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- A six-parameter directed quadratic density in one nonzero physical
covector channel. -/
structure ProgramPT06T02RankOneDirectedQuadraticDensity4D where
  direction : Fin 3
  channel : Fiber →L[Real] Real
  channel_ne_zero : channel ≠ 0
  constant : Real
  valueLinear : Real
  firstLinear : Real
  valueSquare : Real
  valueFirst : Real
  firstSquare : Real

/-- Scalar Gate901 coefficient package underlying the physical channel. -/
def ProgramPT06T02RankOneDirectedQuadraticDensity4D.toScalarDensity
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    ProgramPT06ScalarDirectedQuadraticDensity4D where
  direction := density.direction
  constant := density.constant
  valueLinear := density.valueLinear
  firstLinear := density.firstLinear
  valueSquare := density.valueSquare
  valueFirst := density.valueFirst
  firstSquare := density.firstSquare

/-- Coefficientwise scalarization by the selected physical covector. -/
def programPT06T02RankOneScalarizeJet (order : Nat)
    (channel : Fiber →L[Real] Real) :
    TruncatedThroatSpatialMultiindexJet Fiber order →
      TruncatedThroatSpatialMultiindexJet Real order :=
  fun jet index => channel (jet index)

/-- Physical density obtained by evaluating the Gate901 scalar density after
coefficientwise scalarization. -/
def programPT06T02RankOneDirectedQuadraticDensityEvaluation
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    SecondJet → Real :=
  fun jet =>
    programPT06ScalarDirectedQuadraticDensityEvaluation
      density.toScalarDensity
      (programPT06T02RankOneScalarizeJet 2 density.channel jet)

private def firstOrderValueProjection :
    FirstJet →L[Real] Fiber :=
  ContinuousLinearMap.proj programPT06FirstOrderZeroMultiIndex

private def secondOrderValueProjection :
    SecondJet →L[Real] Fiber :=
  ContinuousLinearMap.proj programPT06SecondOrderZeroMultiIndex

private def secondOrderFirstProjection (direction : Fin 3) :
    SecondJet →L[Real] Fiber :=
  ContinuousLinearMap.proj
    (programPT06SecondOrderFirstMultiIndex direction)

private def scalarSecondOrderValueProjection
    (channel : Fiber →L[Real] Real) : SecondJet →L[Real] Real :=
  channel.comp secondOrderValueProjection

private def scalarSecondOrderFirstProjection
    (channel : Fiber →L[Real] Real) (direction : Fin 3) :
    SecondJet →L[Real] Real :=
  channel.comp (secondOrderFirstProjection direction)

private def thirdOrderSecondMultiIndex (direction : Fin 3) :
    ThroatSpatialTruncatedIndex 3 :=
  { val :=
      throatSpatialCoordinateMultiIndex direction +
        throatSpatialCoordinateMultiIndex direction
    property := by
      rw [throatSpatialMultiIndexOrder_add]
      simp }

private def fourthOrderZeroMultiIndex : ThroatSpatialTruncatedIndex 4 :=
  { val := 0, property := by simp }

private def fourthOrderFirstMultiIndex (direction : Fin 3) :
    ThroatSpatialTruncatedIndex 4 :=
  { val := throatSpatialCoordinateMultiIndex direction
    property := by simp }

private def fourthOrderSecondMultiIndex (direction : Fin 3) :
    ThroatSpatialTruncatedIndex 4 :=
  { val :=
      throatSpatialCoordinateMultiIndex direction +
        throatSpatialCoordinateMultiIndex direction
    property := by
      rw [throatSpatialMultiIndexOrder_add]
      simp }

private def realCovector (coefficient : Real) : Real →L[Real] Real :=
  ContinuousLinearMap.lsmul Real Real coefficient

private def scaleCovector
    {Domain : Type} [SeminormedAddCommGroup Domain] [NormedSpace Real Domain]
    (coefficient : Real) (covector : Domain →L[Real] Real) :
    Domain →L[Real] Real :=
  (realCovector coefficient).comp covector

private theorem secondOrderFirstMultiIndex_ne_zero (direction : Fin 3) :
    programPT06SecondOrderFirstMultiIndex direction ≠
      programPT06SecondOrderZeroMultiIndex := by
  intro hIndex
  have hOrder := congrArg
    (fun index : ThroatSpatialTruncatedIndex 2 =>
      throatSpatialMultiIndexOrder index.val) hIndex
  simp [programPT06SecondOrderFirstMultiIndex,
    programPT06SecondOrderZeroMultiIndex] at hOrder

private theorem throatSpatialCoordinateMultiIndex_injective :
    Function.Injective throatSpatialCoordinateMultiIndex := by
  intro first second hIndex
  by_contra hDirections
  have hCoordinate := congrArg
    (fun index : ThroatSpatialMultiIndex => index first) hIndex
  simp [throatSpatialCoordinateMultiIndex, hDirections] at hCoordinate

private theorem secondOrderFirstMultiIndex_injective :
    Function.Injective programPT06SecondOrderFirstMultiIndex := by
  intro first second hIndex
  apply throatSpatialCoordinateMultiIndex_injective
  exact congrArg Subtype.val hIndex

private theorem secondOrderSecondMultiIndex_ne_zero
    (first second : Fin 3) :
    programPT06SecondOrderSecondMultiIndex first second ≠
      programPT06SecondOrderZeroMultiIndex := by
  intro hIndex
  have hOrder := congrArg
    (fun index : ThroatSpatialTruncatedIndex 2 =>
      throatSpatialMultiIndexOrder index.val) hIndex
  simp [programPT06SecondOrderSecondMultiIndex,
    programPT06SecondOrderZeroMultiIndex,
    throatSpatialMultiIndexOrder_add] at hOrder

private theorem secondOrderSecondMultiIndex_ne_first
    (first second direction : Fin 3) :
    programPT06SecondOrderSecondMultiIndex first second ≠
      programPT06SecondOrderFirstMultiIndex direction := by
  intro hIndex
  have hOrder := congrArg
    (fun index : ThroatSpatialTruncatedIndex 2 =>
      throatSpatialMultiIndexOrder index.val) hIndex
  simp [programPT06SecondOrderSecondMultiIndex,
    programPT06SecondOrderFirstMultiIndex,
    throatSpatialMultiIndexOrder_add] at hOrder

private theorem fourthOrderSecondMultiIndex_ne_zero (direction : Fin 3) :
    fourthOrderSecondMultiIndex direction ≠ fourthOrderZeroMultiIndex := by
  intro hIndex
  have hOrder := congrArg
    (fun index : ThroatSpatialTruncatedIndex 4 =>
      throatSpatialMultiIndexOrder index.val) hIndex
  simp [fourthOrderSecondMultiIndex, fourthOrderZeroMultiIndex,
    throatSpatialMultiIndexOrder_add] at hOrder

@[simp] private theorem scalarSecondOrderValueProjection_truncate_fourth
    (channel : Fiber →L[Real] Real) (jet : FourthJet) :
    scalarSecondOrderValueProjection channel
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet) =
      channel (jet fourthOrderZeroMultiIndex) := by
  change channel (jet _) = channel (jet _)
  apply congrArg channel
  apply congrArg jet
  apply Subtype.ext
  rfl

@[simp] private theorem scalarSecondOrderFirstProjection_truncate_fourth
    (channel : Fiber →L[Real] Real) (direction : Fin 3) (jet : FourthJet) :
    scalarSecondOrderFirstProjection channel direction
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet) =
      channel (jet (fourthOrderFirstMultiIndex direction)) := by
  change channel (jet _) = channel (jet _)
  apply congrArg channel
  apply congrArg jet
  apply Subtype.ext
  rfl

@[simp] private theorem
    scalarSecondOrderValueProjection_totalDerivative_truncate_fourth
    (channel : Fiber →L[Real] Real) (direction : Fin 3) (jet : FourthJet) :
    scalarSecondOrderValueProjection channel
        (throatSpatialTotalDerivative direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)) =
      channel (jet (fourthOrderFirstMultiIndex direction)) := by
  change channel (jet _) = channel (jet _)
  apply congrArg channel
  apply congrArg jet
  apply Subtype.ext
  simp [programPT06SecondOrderZeroMultiIndex,
    fourthOrderFirstMultiIndex]

@[simp] private theorem
    scalarSecondOrderFirstProjection_totalDerivative_truncate_fourth_self
    (channel : Fiber →L[Real] Real) (direction : Fin 3) (jet : FourthJet) :
    scalarSecondOrderFirstProjection channel direction
        (throatSpatialTotalDerivative direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)) =
      channel (jet (fourthOrderSecondMultiIndex direction)) := by
  change channel (jet _) = channel (jet _)
  apply congrArg channel
  apply congrArg jet
  apply Subtype.ext
  simp [programPT06SecondOrderFirstMultiIndex,
    fourthOrderSecondMultiIndex]

@[simp] private theorem firstOrderValueProjection_totalDerivative
    (channel : Fiber →L[Real] Real) (direction : Fin 3) (jet : SecondJet) :
    channel
        (firstOrderValueProjection
          (throatSpatialTotalDerivative direction jet)) =
      scalarSecondOrderFirstProjection channel direction jet := by
  change channel (jet _) = channel (jet _)
  apply congrArg channel
  apply congrArg jet
  apply Subtype.ext
  simp [programPT06FirstOrderZeroMultiIndex,
    programPT06SecondOrderFirstMultiIndex]

@[simp] private theorem scalarSecondOrderValueProjection_totalDerivative
    (channel : Fiber →L[Real] Real) (direction : Fin 3) (jet : ThirdJet) :
    scalarSecondOrderValueProjection channel
        (throatSpatialTotalDerivative direction jet) =
      channel (jet
        { val := throatSpatialCoordinateMultiIndex direction
          property := by simp }) := by
  change channel (jet _) = channel (jet _)
  apply congrArg channel
  apply congrArg jet
  apply Subtype.ext
  simp [programPT06SecondOrderZeroMultiIndex]

@[simp] private theorem
    scalarSecondOrderFirstProjection_totalDerivative_self
    (channel : Fiber →L[Real] Real) (direction : Fin 3) (jet : ThirdJet) :
    scalarSecondOrderFirstProjection channel direction
        (throatSpatialTotalDerivative direction jet) =
      channel (jet (thirdOrderSecondMultiIndex direction)) := by
  change channel (jet _) = channel (jet _)
  apply congrArg channel
  apply congrArg jet
  apply Subtype.ext
  rfl

@[simp] theorem programPT06T02RankOneDirectedQuadraticDensityEvaluation_formula
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (jet : SecondJet) :
    programPT06T02RankOneDirectedQuadraticDensityEvaluation density jet =
      density.constant +
        density.valueLinear *
          scalarSecondOrderValueProjection density.channel jet +
        density.firstLinear *
          scalarSecondOrderFirstProjection density.channel density.direction jet +
        density.valueSquare *
          scalarSecondOrderValueProjection density.channel jet ^ 2 +
        density.valueFirst *
          scalarSecondOrderValueProjection density.channel jet *
          scalarSecondOrderFirstProjection density.channel density.direction jet +
        density.firstSquare *
          scalarSecondOrderFirstProjection density.channel density.direction jet ^ 2 := by
  rfl

private def programPT06T02RankOneDirectedQuadraticDensityDerivative
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (jet : SecondJet) : SecondJet →L[Real] Real :=
  scaleCovector
      (density.valueLinear +
        2 * density.valueSquare *
          scalarSecondOrderValueProjection density.channel jet +
        density.valueFirst *
          scalarSecondOrderFirstProjection density.channel density.direction jet)
      (scalarSecondOrderValueProjection density.channel) +
    scaleCovector
      (density.firstLinear +
        density.valueFirst *
          scalarSecondOrderValueProjection density.channel jet +
        2 * density.firstSquare *
          scalarSecondOrderFirstProjection density.channel density.direction jet)
      (scalarSecondOrderFirstProjection density.channel density.direction)

theorem programPT06T02RankOneDirectedQuadraticDensityEvaluation_hasFDerivAt
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (jet : SecondJet) :
    HasFDerivAt
      (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
      (programPT06T02RankOneDirectedQuadraticDensityDerivative density jet) jet := by
  let value := scalarSecondOrderValueProjection density.channel
  let first :=
    scalarSecondOrderFirstProjection density.channel density.direction
  have hValue := value.hasFDerivAt (x := jet)
  have hFirst := first.hasFDerivAt (x := jet)
  have hRaw :=
    (((((hasFDerivAt_const (x := jet) (c := density.constant)).add
      (hValue.const_mul density.valueLinear)).add
      (hFirst.const_mul density.firstLinear)).add
      ((hValue.pow 2).const_mul density.valueSquare)).add
      ((hValue.mul hFirst).const_mul density.valueFirst)).add
      ((hFirst.pow 2).const_mul density.firstSquare)
  convert hRaw using 1
  · funext candidate
    rw [programPT06T02RankOneDirectedQuadraticDensityEvaluation_formula]
    dsimp [value, first]
    ring
  · ext variation
    simp [programPT06T02RankOneDirectedQuadraticDensityDerivative,
      scaleCovector, realCovector, value, first]
    ring

private theorem programPT06T02RankOneVerticalPartialZero_apply
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (jet : SecondJet) (variation : Fiber) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
        jet variation =
      (density.valueLinear +
        2 * density.valueSquare *
          scalarSecondOrderValueProjection density.channel jet +
        density.valueFirst *
          scalarSecondOrderFirstProjection density.channel density.direction jet) *
        density.channel variation := by
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06T02RankOneDirectedQuadraticDensityEvaluation density) jet
      programPT06SecondOrderZeroMultiIndex variation = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06T02RankOneDirectedQuadraticDensityEvaluation density) jet
    programPT06SecondOrderZeroMultiIndex
    (programPT06T02RankOneDirectedQuadraticDensityDerivative density jet)
    (programPT06T02RankOneDirectedQuadraticDensityEvaluation_hasFDerivAt
      density jet)]
  simp [programPT06T02RankOneDirectedQuadraticDensityDerivative,
    scaleCovector, realCovector, scalarSecondOrderValueProjection,
    scalarSecondOrderFirstProjection, secondOrderValueProjection,
    secondOrderFirstProjection,
    secondOrderFirstMultiIndex_ne_zero density.direction]
  ring

private theorem programPT06T02RankOneVerticalPartialOne_self_apply
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (jet : SecondJet) (variation : Fiber) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
        density.direction jet variation =
      (density.firstLinear +
        density.valueFirst *
          scalarSecondOrderValueProjection density.channel jet +
        2 * density.firstSquare *
          scalarSecondOrderFirstProjection density.channel density.direction jet) *
        density.channel variation := by
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06T02RankOneDirectedQuadraticDensityEvaluation density) jet
      (programPT06SecondOrderFirstMultiIndex density.direction) variation = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06T02RankOneDirectedQuadraticDensityEvaluation density) jet
    (programPT06SecondOrderFirstMultiIndex density.direction)
    (programPT06T02RankOneDirectedQuadraticDensityDerivative density jet)
    (programPT06T02RankOneDirectedQuadraticDensityEvaluation_hasFDerivAt
      density jet)]
  simp [programPT06T02RankOneDirectedQuadraticDensityDerivative,
    scaleCovector, realCovector, scalarSecondOrderValueProjection,
    scalarSecondOrderFirstProjection, secondOrderValueProjection,
    secondOrderFirstProjection,
    Ne.symm (secondOrderFirstMultiIndex_ne_zero density.direction)]
  ring

private theorem programPT06T02RankOneVerticalPartialOne_of_ne
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (direction : Fin 3) (hDirection : direction ≠ density.direction) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
        direction = 0 := by
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06T02RankOneDirectedQuadraticDensityEvaluation density) jet
      (programPT06SecondOrderFirstMultiIndex direction) variation = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06T02RankOneDirectedQuadraticDensityEvaluation density) jet
    (programPT06SecondOrderFirstMultiIndex direction)
    (programPT06T02RankOneDirectedQuadraticDensityDerivative density jet)
    (programPT06T02RankOneDirectedQuadraticDensityEvaluation_hasFDerivAt
      density jet)]
  have hIndex :
      programPT06SecondOrderFirstMultiIndex density.direction ≠
        programPT06SecondOrderFirstMultiIndex direction := by
    intro hEqual
    exact hDirection (secondOrderFirstMultiIndex_injective hEqual.symm)
  simp [programPT06T02RankOneDirectedQuadraticDensityDerivative,
    scaleCovector, realCovector, scalarSecondOrderValueProjection,
    scalarSecondOrderFirstProjection, secondOrderValueProjection,
    secondOrderFirstProjection,
    Ne.symm (secondOrderFirstMultiIndex_ne_zero direction), hIndex]

private theorem programPT06T02RankOneVerticalPartialTwo
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
        first second = 0 := by
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06T02RankOneDirectedQuadraticDensityEvaluation density) jet
      (programPT06SecondOrderSecondMultiIndex first second) variation = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06T02RankOneDirectedQuadraticDensityEvaluation density) jet
    (programPT06SecondOrderSecondMultiIndex first second)
    (programPT06T02RankOneDirectedQuadraticDensityDerivative density jet)
    (programPT06T02RankOneDirectedQuadraticDensityEvaluation_hasFDerivAt
      density jet)]
  simp [programPT06T02RankOneDirectedQuadraticDensityDerivative,
    scaleCovector, realCovector, scalarSecondOrderValueProjection,
    scalarSecondOrderFirstProjection, secondOrderValueProjection,
    secondOrderFirstProjection,
    Ne.symm (secondOrderSecondMultiIndex_ne_zero first second),
    Ne.symm
      (secondOrderSecondMultiIndex_ne_first first second density.direction)]

private def programPT06T02RankOneFirstPartialLinearMap
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    SecondJet →L[Real] (Fiber →L[Real] Real) :=
  (scaleCovector density.valueFirst
      (scalarSecondOrderValueProjection density.channel) +
    scaleCovector (2 * density.firstSquare)
      (scalarSecondOrderFirstProjection density.channel density.direction)).smulRight
        density.channel

private theorem programPT06T02RankOneFirstPartial_hasFDerivAt
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (jet : SecondJet) :
    HasFDerivAt
      (fun candidate : SecondJet =>
        scaleCovector
          (density.firstLinear +
            density.valueFirst *
              scalarSecondOrderValueProjection density.channel candidate +
            2 * density.firstSquare *
              scalarSecondOrderFirstProjection
                density.channel density.direction candidate)
          density.channel)
      (programPT06T02RankOneFirstPartialLinearMap density) jet := by
  have hAffine : HasFDerivAt
      (fun candidate : SecondJet =>
        scaleCovector density.firstLinear density.channel +
          programPT06T02RankOneFirstPartialLinearMap density candidate)
      (programPT06T02RankOneFirstPartialLinearMap density) jet := by
    exact
      (hasFDerivAt_const_add_iff
        (scaleCovector density.firstLinear density.channel)).2
        (programPT06T02RankOneFirstPartialLinearMap density).hasFDerivAt
  convert hAffine using 1
  funext candidate
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06T02RankOneFirstPartialLinearMap,
    scaleCovector, realCovector]
  ring

private theorem programPT06T02RankOneFirstEulerTerm_self_apply
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (jet : ThirdJet) (variation : Fiber) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
        density.direction jet variation =
      (density.valueFirst *
          scalarSecondOrderValueProjection density.channel
            (throatSpatialTotalDerivative density.direction jet) +
        2 * density.firstSquare *
          scalarSecondOrderFirstProjection density.channel density.direction
            (throatSpatialTotalDerivative density.direction jet)) *
        density.channel variation := by
  rw [programPT06SecondOrderLocalEulerFirstTotalTerm]
  have hPartial :
      programPT06SecondOrderLocalVerticalPartialOne
          (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
          density.direction =
        fun candidate : SecondJet =>
          scaleCovector
            (density.firstLinear +
              density.valueFirst *
                scalarSecondOrderValueProjection density.channel candidate +
              2 * density.firstSquare *
                scalarSecondOrderFirstProjection
                  density.channel density.direction candidate)
            density.channel := by
    funext candidate
    apply ContinuousLinearMap.ext
    intro candidateVariation
    rw [programPT06T02RankOneVerticalPartialOne_self_apply]
    simp [scaleCovector, realCovector]
    ring
  rw [hPartial]
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    density.direction _ jet
    (programPT06T02RankOneFirstPartialLinearMap density)
    (programPT06T02RankOneFirstPartial_hasFDerivAt density
      (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet))]
  simp [programPT06T02RankOneFirstPartialLinearMap,
    scaleCovector, realCovector]

private theorem programPT06T02RankOneFirstEulerTerm_of_ne
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (direction : Fin 3) (hDirection : direction ≠ density.direction)
    (jet : ThirdJet) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
        direction jet = 0 := by
  rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
    programPT06T02RankOneVerticalPartialOne_of_ne
      density direction hDirection]
  simp

private theorem programPT06T02RankOneSecondEulerTerm
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (first second : Fin 3) (jet : FourthJet) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
        first second jet = 0 := by
  rw [programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06T02RankOneVerticalPartialTwo]
  simp

/-- Exact physical Gate880 formula for the rank-one directed quadratic
channel. -/
theorem programPT06SecondOrderLocalEuler_t02RankOneDirectedQuadratic_formula
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (jet : FourthJet) :
    programPT06SecondOrderLocalEuler
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation density) jet =
      scaleCovector
        (density.valueLinear +
          2 * density.valueSquare *
            density.channel (jet fourthOrderZeroMultiIndex) -
          2 * density.firstSquare *
            density.channel
              (jet (fourthOrderSecondMultiIndex density.direction)))
        density.channel := by
  apply ContinuousLinearMap.ext
  intro variation
  rw [programPT06SecondOrderLocalEuler_apply,
    programPT06T02RankOneVerticalPartialZero_apply]
  have hFirst :
      Finset.univ.sum
          (fun direction : Fin 3 =>
            programPT06SecondOrderLocalEulerFirstTotalTerm
              (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
              direction
              (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)
              variation) =
        (density.valueFirst *
            density.channel
              (jet (fourthOrderFirstMultiIndex density.direction)) +
          2 * density.firstSquare *
            density.channel
              (jet (fourthOrderSecondMultiIndex density.direction))) *
          density.channel variation := by
    calc
      Finset.univ.sum
          (fun direction : Fin 3 =>
            programPT06SecondOrderLocalEulerFirstTotalTerm
              (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
              direction
              (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)
              variation) =
          programPT06SecondOrderLocalEulerFirstTotalTerm
            (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
            density.direction
            (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)
            variation := by
              exact Finset.sum_eq_single density.direction
                (fun direction _ hDirection => by
                  rw [programPT06T02RankOneFirstEulerTerm_of_ne
                    density direction hDirection]
                  rfl)
                (by simp)
      _ =
          (density.valueFirst *
              density.channel
                (jet (fourthOrderFirstMultiIndex density.direction)) +
            2 * density.firstSquare *
              density.channel
                (jet (fourthOrderSecondMultiIndex density.direction))) *
            density.channel variation := by
              rw [programPT06T02RankOneFirstEulerTerm_self_apply]
              rw [scalarSecondOrderValueProjection_totalDerivative_truncate_fourth,
                scalarSecondOrderFirstProjection_totalDerivative_truncate_fourth_self]
  rw [hFirst, scalarSecondOrderValueProjection_truncate_fourth,
    scalarSecondOrderFirstProjection_truncate_fourth]
  simp [programPT06T02RankOneSecondEulerTerm,
    scaleCovector, realCovector]
  ring

/-- A nonzero real covector is onto; this supplies physical test values for
the converse coefficient extraction. -/
theorem programPT06T02RankOne_channel_surjective
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    Function.Surjective density.channel := by
  have hDetect : ∃ variation : Fiber, density.channel variation ≠ 0 := by
    by_contra hDetect
    push Not at hDetect
    apply density.channel_ne_zero
    apply ContinuousLinearMap.ext
    exact hDetect
  obtain ⟨probe, hProbe⟩ := hDetect
  intro target
  refine ⟨(target / density.channel probe) • probe, ?_⟩
  simp [div_eq_mul_inv, hProbe]

private def programPT06T02RankOneChannelUnit
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) : Fiber :=
  Classical.choose (programPT06T02RankOne_channel_surjective density 1)

@[simp] private theorem programPT06T02RankOneChannelUnit_spec
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    density.channel (programPT06T02RankOneChannelUnit density) = 1 :=
  Classical.choose_spec (programPT06T02RankOne_channel_surjective density 1)

/-- The physical Euler expression vanishes exactly when the scalar-channel
linear and two square obstructions vanish. -/
theorem programPT06_t02RankOneDirectedQuadratic_euler_eq_zero_iff
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    (forall jet : FourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
        jet = 0) <->
      And (density.valueLinear = 0)
        (And (density.valueSquare = 0) (density.firstSquare = 0)) := by
  constructor
  · intro hEuler
    let unit := programPT06T02RankOneChannelUnit density
    have hUnit : density.channel unit = 1 := by
      exact programPT06T02RankOneChannelUnit_spec density
    have hAtZero := congrArg
      (fun covector : Fiber →L[Real] Real => covector unit)
      (hEuler 0)
    rw [programPT06SecondOrderLocalEuler_t02RankOneDirectedQuadratic_formula]
      at hAtZero
    have hLinear : density.valueLinear = 0 := by
      simpa [scaleCovector, realCovector, hUnit] using hAtZero
    have hAtValue := congrArg
      (fun covector : Fiber →L[Real] Real => covector unit)
      (hEuler
        (programPT06ThroatSpatialJetCoordinateInjection
          fourthOrderZeroMultiIndex unit))
    rw [programPT06SecondOrderLocalEuler_t02RankOneDirectedQuadratic_formula]
      at hAtValue
    have hValueSquare : density.valueSquare = 0 := by
      simp [scaleCovector, realCovector, hLinear, hUnit,
        fourthOrderSecondMultiIndex_ne_zero,
        programPT06ThroatSpatialJetCoordinateInjection_same,
        programPT06ThroatSpatialJetCoordinateInjection_of_ne] at hAtValue
      linarith
    have hAtSecond := congrArg
      (fun covector : Fiber →L[Real] Real => covector unit)
      (hEuler
        (programPT06ThroatSpatialJetCoordinateInjection
          (fourthOrderSecondMultiIndex density.direction) unit))
    rw [programPT06SecondOrderLocalEuler_t02RankOneDirectedQuadratic_formula]
      at hAtSecond
    have hFirstSquare : density.firstSquare = 0 := by
      simp [scaleCovector, realCovector, hLinear, hValueSquare, hUnit,
        Ne.symm (fourthOrderSecondMultiIndex_ne_zero density.direction),
        programPT06ThroatSpatialJetCoordinateInjection_same,
        programPT06ThroatSpatialJetCoordinateInjection_of_ne] at hAtSecond
      linarith
    exact ⟨hLinear, hValueSquare, hFirstSquare⟩
  · rintro ⟨hLinear, hValueSquare, hFirstSquare⟩ jet
    rw [programPT06SecondOrderLocalEuler_t02RankOneDirectedQuadratic_formula]
    simp [hLinear, hValueSquare, hFirstSquare, scaleCovector, realCovector]

/-- Physical affine current producing the selected linear first-jet term. -/
def programPT06T02RankOneDirectedQuadraticAffineCurrent
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    ProgramPT06AffineHorizontalCurrent4D Fiber where
  constant := fun _ => 0
  linear := fun direction =>
    if direction = density.direction then
      scaleCovector density.firstLinear
        (density.channel.comp firstOrderValueProjection)
    else 0

/-- Physical quadratic current producing the mixed channel term. -/
def programPT06T02RankOneDirectedQuadraticNonlinearCurrent
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    ProgramPT06DirectedQuadraticValueCurrent4D Fiber where
  direction := density.direction
  left := scaleCovector (density.valueFirst / 2) density.channel
  right := density.channel

private theorem programPT06T02RankOneNonlinearDivergence_apply
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (jet : SecondJet) :
    programPT06DirectedQuadraticValueCurrentDivergence
        (programPT06T02RankOneDirectedQuadraticNonlinearCurrent density) jet =
      density.valueFirst *
        scalarSecondOrderValueProjection density.channel jet *
        scalarSecondOrderFirstProjection
          density.channel density.direction jet := by
  rw [programPT06DirectedQuadraticValueCurrentDivergence_eq_density]
  change
    (density.valueFirst / 2 *
          scalarSecondOrderFirstProjection
            density.channel density.direction jet) *
        scalarSecondOrderValueProjection density.channel jet +
      (density.valueFirst / 2 *
          scalarSecondOrderValueProjection density.channel jet) *
        scalarSecondOrderFirstProjection
          density.channel density.direction jet = _
  ring

/-- Once the three obstructions vanish, the rank-one physical density is
exactly a constant plus its displayed affine and quadratic `dH` terms. -/
theorem programPT06T02RankOneDirectedQuadratic_eq_constant_add_divergences
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D)
    (hLinear : density.valueLinear = 0)
    (hValueSquare : density.valueSquare = 0)
    (hFirstSquare : density.firstSquare = 0)
    (jet : SecondJet) :
    programPT06T02RankOneDirectedQuadraticDensityEvaluation density jet =
      density.constant +
        programPT06AffineHorizontalCurrentDivergence
          (programPT06T02RankOneDirectedQuadraticAffineCurrent density) jet +
        programPT06DirectedQuadraticValueCurrentDivergence
          (programPT06T02RankOneDirectedQuadraticNonlinearCurrent density) jet := by
  rw [programPT06T02RankOneNonlinearDivergence_apply]
  rw [programPT06AffineHorizontalCurrentDivergence_apply]
  have hAffine :
      Finset.univ.sum
          (fun direction : Fin 3 =>
            (programPT06T02RankOneDirectedQuadraticAffineCurrent density).linear
              direction (throatSpatialTotalDerivative direction jet)) =
        density.firstLinear *
          scalarSecondOrderFirstProjection
            density.channel density.direction jet := by
    calc
      Finset.univ.sum
          (fun direction : Fin 3 =>
            (programPT06T02RankOneDirectedQuadraticAffineCurrent density).linear
              direction (throatSpatialTotalDerivative direction jet)) =
          (programPT06T02RankOneDirectedQuadraticAffineCurrent density).linear
            density.direction
            (throatSpatialTotalDerivative density.direction jet) := by
              exact Finset.sum_eq_single density.direction
                (fun direction _ hDirection => by
                  simp [programPT06T02RankOneDirectedQuadraticAffineCurrent,
                    hDirection])
                (by simp)
      _ = density.firstLinear *
          scalarSecondOrderFirstProjection
            density.channel density.direction jet := by
            simp [programPT06T02RankOneDirectedQuadraticAffineCurrent,
              scaleCovector, realCovector,
              firstOrderValueProjection_totalDerivative]
  rw [hAffine,
    programPT06T02RankOneDirectedQuadraticDensityEvaluation_formula]
  simp [hLinear, hValueSquare, hFirstSquare]

/-- Exact divergence-form classification for this one physical rank-one
quadratic channel. -/
theorem programPT06_t02RankOneDirectedQuadratic_euler_eq_zero_iff_divergence_form
    (density : ProgramPT06T02RankOneDirectedQuadraticDensity4D) :
    (forall jet : FourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02RankOneDirectedQuadraticDensityEvaluation density)
        jet = 0) <->
      And (density.valueLinear = 0)
        (And (density.valueSquare = 0)
          (And (density.firstSquare = 0)
            (forall jet : SecondJet,
              programPT06T02RankOneDirectedQuadraticDensityEvaluation
                  density jet =
                density.constant +
                  programPT06AffineHorizontalCurrentDivergence
                    (programPT06T02RankOneDirectedQuadraticAffineCurrent density)
                    jet +
                  programPT06DirectedQuadraticValueCurrentDivergence
                    (programPT06T02RankOneDirectedQuadraticNonlinearCurrent
                      density) jet))) := by
  constructor
  · intro hEuler
    have hCoefficients :=
      (programPT06_t02RankOneDirectedQuadratic_euler_eq_zero_iff density).mp
        hEuler
    rcases hCoefficients with ⟨hLinear, hValueSquare, hFirstSquare⟩
    exact ⟨hLinear, hValueSquare, hFirstSquare,
      programPT06T02RankOneDirectedQuadratic_eq_constant_add_divergences
        density hLinear hValueSquare hFirstSquare⟩
  · rintro ⟨hLinear, hValueSquare, hFirstSquare, _hDivergence⟩
    exact
      (programPT06_t02RankOneDirectedQuadratic_euler_eq_zero_iff density).mpr
        ⟨hLinear, hValueSquare, hFirstSquare⟩

end
end P0EFTJanusProgramPT06T02RankOneDirectedQuadraticExactness4D
end JanusFormal
