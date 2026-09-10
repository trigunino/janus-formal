import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D

/-!
# Exact scalar directed quadratic subclass

This gate classifies an explicit six-parameter family of autonomous scalar
first-order quadratic densities on genuine spatial jets.  For one selected
direction the family contains a constant, linear value and first-jet terms,
value and first-jet squares, and the mixed value-first-jet monomial.

The genuine Gate880 Euler expression is computed exactly.  It vanishes if
and only if the three obstruction coefficients vanish.  The remaining
constant, linear first-jet term, and mixed quadratic term are then exactly a
constant plus genuine formal horizontal divergences of explicit affine and
quadratic currents.

The result is a complete converse on this directed scalar quadratic family.
It does not classify quadratic forms coupling several directions or the full
T02 degree-four carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ScalarDirectedQuadraticExactness4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D
open P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

private abbrev FirstJet := ThroatSpatialMultiindexJet1 Real
private abbrev SecondJet := ThroatSpatialMultiindexJet2 Real
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Real
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Real

/-- Coefficients of a directed scalar quadratic first-order density. -/
structure ProgramPT06ScalarDirectedQuadraticDensity4D where
  direction : Fin 3
  constant : Real
  valueLinear : Real
  firstLinear : Real
  valueSquare : Real
  valueFirst : Real
  firstSquare : Real

private def firstOrderValueProjection :
    ContinuousLinearMap (RingHom.id Real) FirstJet Real :=
  ContinuousLinearMap.proj programPT06FirstOrderZeroMultiIndex

private def secondOrderValueProjection :
    ContinuousLinearMap (RingHom.id Real) SecondJet Real :=
  ContinuousLinearMap.proj programPT06SecondOrderZeroMultiIndex

private def secondOrderFirstProjection (direction : Fin 3) :
    ContinuousLinearMap (RingHom.id Real) SecondJet Real :=
  ContinuousLinearMap.proj
    (programPT06SecondOrderFirstMultiIndex direction)

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

private def realCovector (coefficient : Real) :
    ContinuousLinearMap (RingHom.id Real) Real Real :=
  ContinuousLinearMap.lsmul Real Real coefficient

private def scaleCovector
    {Domain : Type} [SeminormedAddCommGroup Domain] [NormedSpace Real Domain]
    (coefficient : Real)
    (covector : ContinuousLinearMap (RingHom.id Real) Domain Real) :
    ContinuousLinearMap (RingHom.id Real) Domain Real :=
  (realCovector coefficient).comp covector

private theorem secondOrderFirstMultiIndex_ne_zero (direction : Fin 3) :
    Not (programPT06SecondOrderFirstMultiIndex direction =
      programPT06SecondOrderZeroMultiIndex) := by
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
    Not (programPT06SecondOrderSecondMultiIndex first second =
      programPT06SecondOrderZeroMultiIndex) := by
  intro hIndex
  have hOrder := congrArg
    (fun index : ThroatSpatialTruncatedIndex 2 =>
      throatSpatialMultiIndexOrder index.val) hIndex
  simp [programPT06SecondOrderSecondMultiIndex,
    programPT06SecondOrderZeroMultiIndex,
    throatSpatialMultiIndexOrder_add] at hOrder

private theorem secondOrderSecondMultiIndex_ne_first
    (first second direction : Fin 3) :
    Not (programPT06SecondOrderSecondMultiIndex first second =
      programPT06SecondOrderFirstMultiIndex direction) := by
  intro hIndex
  have hOrder := congrArg
    (fun index : ThroatSpatialTruncatedIndex 2 =>
      throatSpatialMultiIndexOrder index.val) hIndex
  simp [programPT06SecondOrderSecondMultiIndex,
    programPT06SecondOrderFirstMultiIndex,
    throatSpatialMultiIndexOrder_add] at hOrder

private theorem fourthOrderSecondMultiIndex_ne_zero (direction : Fin 3) :
    Not (fourthOrderSecondMultiIndex direction = fourthOrderZeroMultiIndex) := by
  intro hIndex
  have hOrder := congrArg
    (fun index : ThroatSpatialTruncatedIndex 4 =>
      throatSpatialMultiIndexOrder index.val) hIndex
  simp [fourthOrderSecondMultiIndex, fourthOrderZeroMultiIndex,
    throatSpatialMultiIndexOrder_add] at hOrder

@[simp] private theorem secondOrderValueProjection_truncate_fourth
    (jet : FourthJet) :
    secondOrderValueProjection
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet) =
      jet fourthOrderZeroMultiIndex := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

@[simp] private theorem secondOrderFirstProjection_truncate_fourth
    (direction : Fin 3) (jet : FourthJet) :
    secondOrderFirstProjection direction
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet) =
      jet (fourthOrderFirstMultiIndex direction) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

@[simp] private theorem
    secondOrderValueProjection_totalDerivative_truncate_fourth
    (direction : Fin 3) (jet : FourthJet) :
    secondOrderValueProjection
        (throatSpatialTotalDerivative direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)) =
      jet (fourthOrderFirstMultiIndex direction) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  simp [programPT06SecondOrderZeroMultiIndex,
    fourthOrderFirstMultiIndex]

@[simp] private theorem
    secondOrderFirstProjection_totalDerivative_truncate_fourth_self
    (direction : Fin 3) (jet : FourthJet) :
    secondOrderFirstProjection direction
        (throatSpatialTotalDerivative direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)) =
      jet (fourthOrderSecondMultiIndex direction) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  simp [programPT06SecondOrderFirstMultiIndex,
    fourthOrderSecondMultiIndex]

@[simp] private theorem firstOrderValueProjection_totalDerivative
    (direction : Fin 3) (jet : SecondJet) :
    firstOrderValueProjection
        (throatSpatialTotalDerivative direction jet) =
      secondOrderFirstProjection direction jet := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  simp [programPT06FirstOrderZeroMultiIndex,
    programPT06SecondOrderFirstMultiIndex]

@[simp] private theorem secondOrderValueProjection_totalDerivative
    (direction : Fin 3) (jet : ThirdJet) :
    secondOrderValueProjection
        (throatSpatialTotalDerivative direction jet) =
      jet
        { val := throatSpatialCoordinateMultiIndex direction
          property := by simp } := by
  change jet _ = jet _
  congr 1
  apply Subtype.ext
  simp [programPT06SecondOrderZeroMultiIndex]

@[simp] private theorem secondOrderFirstProjection_totalDerivative_self
    (direction : Fin 3) (jet : ThirdJet) :
    secondOrderFirstProjection direction
        (throatSpatialTotalDerivative direction jet) =
      jet (thirdOrderSecondMultiIndex direction) := by
  change jet _ = jet _
  congr 1

/-- Evaluation of the six-parameter density on a genuine second jet. -/
def programPT06ScalarDirectedQuadraticDensityEvaluation
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    SecondJet -> Real :=
  fun jet =>
    let value := secondOrderValueProjection jet
    let first := secondOrderFirstProjection density.direction jet
    density.constant + density.valueLinear * value +
      density.firstLinear * first + density.valueSquare * value ^ 2 +
      density.valueFirst * value * first + density.firstSquare * first ^ 2

private def programPT06ScalarDirectedQuadraticDensityDerivative
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : SecondJet) :
    ContinuousLinearMap (RingHom.id Real) SecondJet Real :=
  scaleCovector
      (density.valueLinear +
        2 * density.valueSquare * secondOrderValueProjection jet +
        density.valueFirst *
          secondOrderFirstProjection density.direction jet)
      secondOrderValueProjection +
    scaleCovector
      (density.firstLinear +
        density.valueFirst * secondOrderValueProjection jet +
        2 * density.firstSquare *
          secondOrderFirstProjection density.direction jet)
      (secondOrderFirstProjection density.direction)

theorem programPT06ScalarDirectedQuadraticDensityEvaluation_hasFDerivAt
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : SecondJet) :
    HasFDerivAt
      (programPT06ScalarDirectedQuadraticDensityEvaluation density)
      (programPT06ScalarDirectedQuadraticDensityDerivative density jet) jet := by
  let value := secondOrderValueProjection
  let first := secondOrderFirstProjection density.direction
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
    dsimp [programPT06ScalarDirectedQuadraticDensityEvaluation, value, first]
    ring
  · ext variation
    simp [programPT06ScalarDirectedQuadraticDensityDerivative,
      scaleCovector, realCovector, value, first]
    ring

private theorem programPT06ScalarDirectedQuadraticVerticalPartialZero_apply
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : SecondJet) (variation : Real) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06ScalarDirectedQuadraticDensityEvaluation density)
        jet variation =
      (density.valueLinear +
        2 * density.valueSquare * secondOrderValueProjection jet +
        density.valueFirst *
          secondOrderFirstProjection density.direction jet) * variation := by
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06ScalarDirectedQuadraticDensityEvaluation density) jet
      programPT06SecondOrderZeroMultiIndex variation = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06ScalarDirectedQuadraticDensityEvaluation density) jet
    programPT06SecondOrderZeroMultiIndex
    (programPT06ScalarDirectedQuadraticDensityDerivative density jet)
    (programPT06ScalarDirectedQuadraticDensityEvaluation_hasFDerivAt
      density jet)]
  simp [programPT06ScalarDirectedQuadraticDensityDerivative,
    scaleCovector, realCovector, secondOrderValueProjection,
    secondOrderFirstProjection,
    secondOrderFirstMultiIndex_ne_zero density.direction];
    ring

private theorem programPT06ScalarDirectedQuadraticVerticalPartialOne_self_apply
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : SecondJet) (variation : Real) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06ScalarDirectedQuadraticDensityEvaluation density)
        density.direction jet variation =
      (density.firstLinear +
        density.valueFirst * secondOrderValueProjection jet +
        2 * density.firstSquare *
          secondOrderFirstProjection density.direction jet) * variation := by
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06ScalarDirectedQuadraticDensityEvaluation density) jet
      (programPT06SecondOrderFirstMultiIndex density.direction) variation = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06ScalarDirectedQuadraticDensityEvaluation density) jet
    (programPT06SecondOrderFirstMultiIndex density.direction)
    (programPT06ScalarDirectedQuadraticDensityDerivative density jet)
    (programPT06ScalarDirectedQuadraticDensityEvaluation_hasFDerivAt
      density jet)]
  simp [programPT06ScalarDirectedQuadraticDensityDerivative,
    scaleCovector, realCovector, secondOrderValueProjection,
    secondOrderFirstProjection,
    Ne.symm (secondOrderFirstMultiIndex_ne_zero density.direction)];
    ring

private theorem programPT06ScalarDirectedQuadraticVerticalPartialOne_of_ne
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (direction : Fin 3) (hDirection : Not (direction = density.direction)) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06ScalarDirectedQuadraticDensityEvaluation density)
        direction = 0 := by
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06ScalarDirectedQuadraticDensityEvaluation density) jet
      (programPT06SecondOrderFirstMultiIndex direction) variation = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06ScalarDirectedQuadraticDensityEvaluation density) jet
    (programPT06SecondOrderFirstMultiIndex direction)
    (programPT06ScalarDirectedQuadraticDensityDerivative density jet)
    (programPT06ScalarDirectedQuadraticDensityEvaluation_hasFDerivAt
      density jet)]
  have hIndex : Not
      (programPT06SecondOrderFirstMultiIndex density.direction =
        programPT06SecondOrderFirstMultiIndex direction) := by
    intro hEqual
    exact hDirection (secondOrderFirstMultiIndex_injective hEqual.symm)
  simp [programPT06ScalarDirectedQuadraticDensityDerivative,
    scaleCovector, realCovector, secondOrderValueProjection,
    secondOrderFirstProjection,
    Ne.symm (secondOrderFirstMultiIndex_ne_zero direction), hIndex]

private theorem programPT06ScalarDirectedQuadraticVerticalPartialTwo
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06ScalarDirectedQuadraticDensityEvaluation density)
        first second = 0 := by
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06ScalarDirectedQuadraticDensityEvaluation density) jet
      (programPT06SecondOrderSecondMultiIndex first second) variation = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06ScalarDirectedQuadraticDensityEvaluation density) jet
    (programPT06SecondOrderSecondMultiIndex first second)
    (programPT06ScalarDirectedQuadraticDensityDerivative density jet)
    (programPT06ScalarDirectedQuadraticDensityEvaluation_hasFDerivAt
      density jet)]
  simp [programPT06ScalarDirectedQuadraticDensityDerivative,
    scaleCovector, realCovector, secondOrderValueProjection,
    secondOrderFirstProjection,
    Ne.symm (secondOrderSecondMultiIndex_ne_zero first second),
    Ne.symm
      (secondOrderSecondMultiIndex_ne_first first second density.direction)]

private def programPT06ScalarDirectedQuadraticFirstPartialLinearMap
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    ContinuousLinearMap (RingHom.id Real) SecondJet
      (ContinuousLinearMap (RingHom.id Real) Real Real) :=
  (ContinuousLinearMap.lsmul Real Real).comp
    (scaleCovector density.valueFirst secondOrderValueProjection +
      scaleCovector (2 * density.firstSquare)
        (secondOrderFirstProjection density.direction))

private theorem programPT06ScalarDirectedQuadraticFirstPartial_hasFDerivAt
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : SecondJet) :
    HasFDerivAt
      (fun candidate : SecondJet =>
        realCovector
          (density.firstLinear +
            density.valueFirst * secondOrderValueProjection candidate +
            2 * density.firstSquare *
              secondOrderFirstProjection density.direction candidate))
      (programPT06ScalarDirectedQuadraticFirstPartialLinearMap density) jet := by
  have hAffine : HasFDerivAt
      (fun candidate : SecondJet =>
        realCovector density.firstLinear +
          programPT06ScalarDirectedQuadraticFirstPartialLinearMap density
            candidate)
      (programPT06ScalarDirectedQuadraticFirstPartialLinearMap density) jet := by
    exact
      (hasFDerivAt_const_add_iff
        (realCovector density.firstLinear)).2
        (programPT06ScalarDirectedQuadraticFirstPartialLinearMap density).hasFDerivAt
  convert hAffine using 1
  funext candidate
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06ScalarDirectedQuadraticFirstPartialLinearMap,
    scaleCovector, realCovector]
  ring

private theorem programPT06ScalarDirectedQuadraticFirstEulerTerm_self_apply
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : ThirdJet) (variation : Real) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06ScalarDirectedQuadraticDensityEvaluation density)
        density.direction jet variation =
      (density.valueFirst *
          secondOrderValueProjection
            (throatSpatialTotalDerivative density.direction jet) +
        2 * density.firstSquare *
          secondOrderFirstProjection density.direction
            (throatSpatialTotalDerivative density.direction jet)) * variation := by
  rw [programPT06SecondOrderLocalEulerFirstTotalTerm]
  have hPartial :
      programPT06SecondOrderLocalVerticalPartialOne
          (programPT06ScalarDirectedQuadraticDensityEvaluation density)
          density.direction =
        fun candidate : SecondJet =>
          realCovector
            (density.firstLinear +
              density.valueFirst * secondOrderValueProjection candidate +
              2 * density.firstSquare *
                secondOrderFirstProjection density.direction candidate) := by
    funext candidate
    apply ContinuousLinearMap.ext
    intro variation
    rw [programPT06ScalarDirectedQuadraticVerticalPartialOne_self_apply]
    simp [realCovector]
    ring
  rw [hPartial]
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    density.direction _ jet
    (programPT06ScalarDirectedQuadraticFirstPartialLinearMap density)
    (programPT06ScalarDirectedQuadraticFirstPartial_hasFDerivAt density
      (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet))]
  simp [programPT06ScalarDirectedQuadraticFirstPartialLinearMap,
    scaleCovector, realCovector]
  ring

private theorem programPT06ScalarDirectedQuadraticFirstEulerTerm_of_ne
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (direction : Fin 3) (hDirection : Not (direction = density.direction))
    (jet : ThirdJet) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06ScalarDirectedQuadraticDensityEvaluation density)
        direction jet = 0 := by
  rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
    programPT06ScalarDirectedQuadraticVerticalPartialOne_of_ne
      density direction hDirection]
  simp

private theorem programPT06ScalarDirectedQuadraticSecondEulerTerm
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (first second : Fin 3) (jet : FourthJet) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06ScalarDirectedQuadraticDensityEvaluation density)
        first second jet = 0 := by
  rw [programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06ScalarDirectedQuadraticVerticalPartialTwo]
  simp

/-- Exact Gate880 Euler formula for the directed scalar quadratic family. -/
theorem programPT06SecondOrderLocalEuler_scalarDirectedQuadratic_formula
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : FourthJet) :
    programPT06SecondOrderLocalEuler
        (programPT06ScalarDirectedQuadraticDensityEvaluation density) jet =
      realCovector
        (density.valueLinear +
          2 * density.valueSquare * jet fourthOrderZeroMultiIndex -
          2 * density.firstSquare *
            jet (fourthOrderSecondMultiIndex density.direction)) := by
  apply ContinuousLinearMap.ext
  intro variation
  rw [programPT06SecondOrderLocalEuler_apply,
    programPT06ScalarDirectedQuadraticVerticalPartialZero_apply]
  have hFirst :
      Finset.univ.sum
          (fun direction : Fin 3 =>
            programPT06SecondOrderLocalEulerFirstTotalTerm
              (programPT06ScalarDirectedQuadraticDensityEvaluation density)
              direction
              (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)
              variation) =
        (density.valueFirst *
            jet (fourthOrderFirstMultiIndex density.direction) +
          2 * density.firstSquare *
            jet (fourthOrderSecondMultiIndex density.direction)) * variation := by
    calc
      Finset.univ.sum
          (fun direction : Fin 3 =>
            programPT06SecondOrderLocalEulerFirstTotalTerm
              (programPT06ScalarDirectedQuadraticDensityEvaluation density)
              direction
              (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)
              variation) =
          programPT06SecondOrderLocalEulerFirstTotalTerm
            (programPT06ScalarDirectedQuadraticDensityEvaluation density)
            density.direction
            (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)
            variation := by
              exact Finset.sum_eq_single density.direction
                (fun direction _ hDirection => by
                  rw [programPT06ScalarDirectedQuadraticFirstEulerTerm_of_ne
                    density direction hDirection]
                  rfl)
                (by simp)
      _ =
          (density.valueFirst *
              jet (fourthOrderFirstMultiIndex density.direction) +
            2 * density.firstSquare *
              jet (fourthOrderSecondMultiIndex density.direction)) *
            variation := by
              rw [programPT06ScalarDirectedQuadraticFirstEulerTerm_self_apply]
              rw [secondOrderValueProjection_totalDerivative_truncate_fourth,
                secondOrderFirstProjection_totalDerivative_truncate_fourth_self]
  rw [hFirst, secondOrderValueProjection_truncate_fourth,
    secondOrderFirstProjection_truncate_fourth]
  simp [programPT06ScalarDirectedQuadraticSecondEulerTerm,
    realCovector]
  ring

/-- The Euler expression vanishes exactly when the value-linear, value-square,
and selected first-jet-square coefficients vanish. -/
theorem programPT06_scalarDirectedQuadratic_euler_eq_zero_iff
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    (forall jet : FourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06ScalarDirectedQuadraticDensityEvaluation density) jet = 0) <->
      And (density.valueLinear = 0)
        (And (density.valueSquare = 0) (density.firstSquare = 0)) := by
  constructor
  · intro hEuler
    have hAtZero := congrArg
      (fun covector : ContinuousLinearMap (RingHom.id Real) Real Real =>
        covector 1)
      (hEuler 0)
    rw [programPT06SecondOrderLocalEuler_scalarDirectedQuadratic_formula] at hAtZero
    have hLinear : density.valueLinear = 0 := by
      simpa [realCovector] using hAtZero
    have hAtValue := congrArg
      (fun covector : ContinuousLinearMap (RingHom.id Real) Real Real =>
        covector 1)
      (hEuler
        (programPT06ThroatSpatialJetCoordinateInjection
          fourthOrderZeroMultiIndex 1))
    rw [programPT06SecondOrderLocalEuler_scalarDirectedQuadratic_formula] at hAtValue
    have hValueSquare : density.valueSquare = 0 := by
      simp [realCovector, hLinear, fourthOrderSecondMultiIndex_ne_zero,
        programPT06ThroatSpatialJetCoordinateInjection_same,
        programPT06ThroatSpatialJetCoordinateInjection_of_ne] at hAtValue
      linarith
    have hAtSecond := congrArg
      (fun covector : ContinuousLinearMap (RingHom.id Real) Real Real =>
        covector 1)
      (hEuler
        (programPT06ThroatSpatialJetCoordinateInjection
          (fourthOrderSecondMultiIndex density.direction) 1))
    rw [programPT06SecondOrderLocalEuler_scalarDirectedQuadratic_formula] at hAtSecond
    have hFirstSquare : density.firstSquare = 0 := by
      simp [realCovector, hLinear, hValueSquare,
        Ne.symm (fourthOrderSecondMultiIndex_ne_zero density.direction),
        programPT06ThroatSpatialJetCoordinateInjection_same,
        programPT06ThroatSpatialJetCoordinateInjection_of_ne] at hAtSecond
      linarith
    exact And.intro hLinear (And.intro hValueSquare hFirstSquare)
  · intro hCoefficients
    rcases hCoefficients with ⟨hLinear, hValueSquare, hFirstSquare⟩
    intro jet
    rw [programPT06SecondOrderLocalEuler_scalarDirectedQuadratic_formula]
    simp [hLinear, hValueSquare, hFirstSquare, realCovector]

/-- Explicit affine current producing the selected linear first-jet term. -/
def programPT06ScalarDirectedQuadraticAffineCurrent
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    ProgramPT06AffineHorizontalCurrent4D Real where
  constant := fun _ => 0
  linear := fun direction =>
    if direction = density.direction then
      scaleCovector density.firstLinear firstOrderValueProjection
    else 0

/-- Explicit quadratic current producing the mixed value-first-jet term. -/
def programPT06ScalarDirectedQuadraticNonlinearCurrent
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    ProgramPT06DirectedQuadraticValueCurrent4D Real where
  direction := density.direction
  left := realCovector (density.valueFirst / 2)
  right := ContinuousLinearMap.id Real Real

private theorem programPT06ScalarDirectedQuadraticNonlinearDivergence_apply
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (jet : SecondJet) :
    programPT06DirectedQuadraticValueCurrentDivergence
        (programPT06ScalarDirectedQuadraticNonlinearCurrent density) jet =
      density.valueFirst * secondOrderValueProjection jet *
        secondOrderFirstProjection density.direction jet := by
  rw [programPT06DirectedQuadraticValueCurrentDivergence_eq_density]
  change
    (density.valueFirst / 2 *
          secondOrderFirstProjection density.direction jet) *
        secondOrderValueProjection jet +
      (density.valueFirst / 2 * secondOrderValueProjection jet) *
        secondOrderFirstProjection density.direction jet = _
  ring

/-- With the three obstruction coefficients zero, the density is exactly its
constant plus the genuine divergences of the displayed affine and quadratic
currents. -/
theorem programPT06ScalarDirectedQuadratic_eq_constant_add_divergences
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D)
    (hLinear : density.valueLinear = 0)
    (hValueSquare : density.valueSquare = 0)
    (hFirstSquare : density.firstSquare = 0)
    (jet : SecondJet) :
    programPT06ScalarDirectedQuadraticDensityEvaluation density jet =
      density.constant +
        programPT06AffineHorizontalCurrentDivergence
          (programPT06ScalarDirectedQuadraticAffineCurrent density) jet +
        programPT06DirectedQuadraticValueCurrentDivergence
          (programPT06ScalarDirectedQuadraticNonlinearCurrent density) jet := by
  rw [programPT06ScalarDirectedQuadraticNonlinearDivergence_apply]
  rw [programPT06AffineHorizontalCurrentDivergence_apply]
  have hAffine :
      Finset.univ.sum
          (fun direction : Fin 3 =>
            (programPT06ScalarDirectedQuadraticAffineCurrent density).linear
              direction (throatSpatialTotalDerivative direction jet)) =
        density.firstLinear *
          secondOrderFirstProjection density.direction jet := by
    calc
      Finset.univ.sum
          (fun direction : Fin 3 =>
            (programPT06ScalarDirectedQuadraticAffineCurrent density).linear
              direction (throatSpatialTotalDerivative direction jet)) =
          (programPT06ScalarDirectedQuadraticAffineCurrent density).linear
            density.direction
            (throatSpatialTotalDerivative density.direction jet) := by
              exact Finset.sum_eq_single density.direction
                (fun direction _ hDirection => by
                  simp [programPT06ScalarDirectedQuadraticAffineCurrent,
                    hDirection])
                (by simp)
      _ = density.firstLinear *
          secondOrderFirstProjection density.direction jet := by
            simp [programPT06ScalarDirectedQuadraticAffineCurrent,
              scaleCovector, realCovector]
  rw [hAffine]
  simp [programPT06ScalarDirectedQuadraticDensityEvaluation,
    hLinear, hValueSquare, hFirstSquare]

/-- Exact classification in divergence form on this scalar quadratic class. -/
theorem programPT06_scalarDirectedQuadratic_euler_eq_zero_iff_divergence_form
    (density : ProgramPT06ScalarDirectedQuadraticDensity4D) :
    (forall jet : FourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06ScalarDirectedQuadraticDensityEvaluation density) jet = 0) <->
      And (density.valueLinear = 0)
        (And (density.valueSquare = 0)
          (And (density.firstSquare = 0)
            (forall jet : SecondJet,
              programPT06ScalarDirectedQuadraticDensityEvaluation density jet =
                density.constant +
                  programPT06AffineHorizontalCurrentDivergence
                    (programPT06ScalarDirectedQuadraticAffineCurrent density) jet +
                  programPT06DirectedQuadraticValueCurrentDivergence
                    (programPT06ScalarDirectedQuadraticNonlinearCurrent density)
                    jet))) := by
  constructor
  · intro hEuler
    have hCoefficients :=
      (programPT06_scalarDirectedQuadratic_euler_eq_zero_iff density).mp hEuler
    rcases hCoefficients with ⟨hLinear, hValueSquare, hFirstSquare⟩
    exact ⟨hLinear, hValueSquare, hFirstSquare,
      programPT06ScalarDirectedQuadratic_eq_constant_add_divergences
        density hLinear hValueSquare hFirstSquare⟩
  · intro hDivergenceForm
    rcases hDivergenceForm with
      ⟨hLinear, hValueSquare, hFirstSquare, _hDivergence⟩
    exact (programPT06_scalarDirectedQuadratic_euler_eq_zero_iff density).mpr
      (And.intro hLinear (And.intro hValueSquare hFirstSquare))

end
end P0EFTJanusProgramPT06ScalarDirectedQuadraticExactness4D
end JanusFormal
