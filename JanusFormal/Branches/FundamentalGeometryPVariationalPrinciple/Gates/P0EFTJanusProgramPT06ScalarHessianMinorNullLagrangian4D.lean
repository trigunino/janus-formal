import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderLocalEuler4D

/-!
# Scalar Hessian-minor null Lagrangian

For two distinct spatial directions this gate treats the second-order scalar
density `u_ii * u_jj - u_ij ^ 2`.  Its Gate880 Euler expression vanishes with
the off-diagonal `1 / 2` weight counted over both ordered direction pairs.

An explicit order-two current is also supplied.  Its two nonzero components
are `u_i * u_jj` and `-u_i * u_ij`; their genuine Gate879 total derivatives
cancel the third-order terms and leave exactly the Hessian minor.

The construction is limited to one scalar field and one two-direction minor.
It does not classify sums of minors, multifield minors, or the full T02
degree-four kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ScalarHessianMinorNullLagrangian4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

private abbrev SecondJet := ThroatSpatialMultiindexJet2 Real
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Real
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Real
private abbrev RealCovector := ContinuousLinearMap (RingHom.id Real) Real Real

/-- A choice of two distinct spatial directions. -/
structure ProgramPT06ScalarHessianMinor4D where
  first : Fin 3
  second : Fin 3
  distinct : first ≠ second

private def secondOrderFirstProjection (direction : Fin 3) :
    ContinuousLinearMap (RingHom.id Real) SecondJet Real :=
  ContinuousLinearMap.proj
    (programPT06SecondOrderFirstMultiIndex direction)

private def secondOrderSecondProjection (first second : Fin 3) :
    ContinuousLinearMap (RingHom.id Real) SecondJet Real :=
  ContinuousLinearMap.proj
    (programPT06SecondOrderSecondMultiIndex first second)

private def thirdOrderFirstMultiIndex (direction : Fin 3) :
    ThroatSpatialTruncatedIndex 3 :=
  ⟨throatSpatialCoordinateMultiIndex direction, by simp⟩

private def thirdOrderSecondMultiIndex (first second : Fin 3) :
    ThroatSpatialTruncatedIndex 3 :=
  ⟨throatSpatialCoordinateMultiIndex first +
      throatSpatialCoordinateMultiIndex second, by
    rw [throatSpatialMultiIndexOrder_add]
    simp⟩

private def thirdOrderThirdMultiIndex
    (first second third : Fin 3) : ThroatSpatialTruncatedIndex 3 :=
  ⟨(throatSpatialCoordinateMultiIndex first +
      throatSpatialCoordinateMultiIndex second) +
      throatSpatialCoordinateMultiIndex third, by
    rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex,
      throatSpatialMultiIndexOrder_add]
    simp⟩

private def fourthOrderMinorMultiIndex (first second : Fin 3) :
    ThroatSpatialTruncatedIndex 4 :=
  ⟨(throatSpatialCoordinateMultiIndex first +
      throatSpatialCoordinateMultiIndex first) +
      (throatSpatialCoordinateMultiIndex second +
        throatSpatialCoordinateMultiIndex second), by
    rw [throatSpatialMultiIndexOrder_add,
      throatSpatialMultiIndexOrder_add,
      throatSpatialMultiIndexOrder_add]
    simp⟩

private def realCovector (coefficient : Real) : RealCovector :=
  ContinuousLinearMap.lsmul Real Real coefficient

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

@[simp] private theorem secondOrderFirstProjection_truncate_third
    (direction : Fin 3) (jet : ThirdJet) :
    secondOrderFirstProjection direction
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) =
      jet (thirdOrderFirstMultiIndex direction) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

@[simp] private theorem secondOrderSecondProjection_truncate_third
    (first second : Fin 3) (jet : ThirdJet) :
    secondOrderSecondProjection first second
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) =
      jet (thirdOrderSecondMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

@[simp] private theorem secondOrderFirstProjection_totalDerivative
    (first second : Fin 3) (jet : ThirdJet) :
    secondOrderFirstProjection second
        (throatSpatialTotalDerivative first jet) =
      jet (thirdOrderSecondMultiIndex second first) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

@[simp] private theorem secondOrderSecondProjection_totalDerivative
    (first second direction : Fin 3) (jet : ThirdJet) :
    secondOrderSecondProjection first second
        (throatSpatialTotalDerivative direction jet) =
      jet (thirdOrderThirdMultiIndex first second direction) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

private theorem thirdOrderThirdMultiIndex_cancel
    (first second : Fin 3) :
    thirdOrderThirdMultiIndex second second first =
      thirdOrderThirdMultiIndex first second second := by
  apply Subtype.ext
  dsimp [thirdOrderThirdMultiIndex]
  ac_rfl

@[simp] private theorem throatSpatialTotalDerivative_third_jj_i
    (first second : Fin 3) (jet : FourthJet) :
    throatSpatialTotalDerivative first jet
        (thirdOrderThirdMultiIndex second second first) =
      jet (fourthOrderMinorMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [throatSpatialTotalDerivative, thirdOrderThirdMultiIndex,
    fourthOrderMinorMultiIndex]
  ac_rfl

@[simp] private theorem throatSpatialTotalDerivative_third_ij_j_i
    (first second : Fin 3) (jet : FourthJet) :
    throatSpatialTotalDerivative first jet
        (thirdOrderThirdMultiIndex first second second) =
      jet (fourthOrderMinorMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [throatSpatialTotalDerivative, thirdOrderThirdMultiIndex,
    fourthOrderMinorMultiIndex]
  ac_rfl

@[simp] private theorem throatSpatialTotalDerivative_third_ij_i_j
    (first second : Fin 3) (jet : FourthJet) :
    throatSpatialTotalDerivative second jet
        (thirdOrderThirdMultiIndex first second first) =
      jet (fourthOrderMinorMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [throatSpatialTotalDerivative, thirdOrderThirdMultiIndex,
    fourthOrderMinorMultiIndex]
  ac_rfl

@[simp] private theorem throatSpatialTotalDerivative_third_ii_j_j
    (first second : Fin 3) (jet : FourthJet) :
    throatSpatialTotalDerivative second jet
        (thirdOrderThirdMultiIndex first first second) =
      jet (fourthOrderMinorMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [throatSpatialTotalDerivative, thirdOrderThirdMultiIndex,
    fourthOrderMinorMultiIndex]
  ac_rfl

@[simp] private theorem secondOrderSecondProjection_iterated_jj_ii
    (first second : Fin 3) (jet : FourthJet) :
    secondOrderSecondProjection second second
        (throatSpatialTotalDerivative first
          (throatSpatialTotalDerivative first jet)) =
      jet (fourthOrderMinorMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [fourthOrderMinorMultiIndex,
    programPT06SecondOrderSecondMultiIndex]
  ac_rfl

@[simp] private theorem secondOrderSecondProjection_iterated_ii_jj
    (first second : Fin 3) (jet : FourthJet) :
    secondOrderSecondProjection first first
        (throatSpatialTotalDerivative second
          (throatSpatialTotalDerivative second jet)) =
      jet (fourthOrderMinorMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [fourthOrderMinorMultiIndex,
    programPT06SecondOrderSecondMultiIndex]
  ac_rfl

@[simp] private theorem secondOrderSecondProjection_iterated_ij_ij
    (first second : Fin 3) (jet : FourthJet) :
    secondOrderSecondProjection first second
        (throatSpatialTotalDerivative second
          (throatSpatialTotalDerivative first jet)) =
      jet (fourthOrderMinorMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [fourthOrderMinorMultiIndex,
    programPT06SecondOrderSecondMultiIndex]
  ac_rfl

@[simp] private theorem secondOrderSecondProjection_iterated_ij_ji
    (first second : Fin 3) (jet : FourthJet) :
    secondOrderSecondProjection first second
        (throatSpatialTotalDerivative first
          (throatSpatialTotalDerivative second jet)) =
      jet (fourthOrderMinorMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [fourthOrderMinorMultiIndex,
    programPT06SecondOrderSecondMultiIndex]
  ac_rfl

private theorem fourthOrderMinorMultiIndex_comm (first second : Fin 3) :
    fourthOrderMinorMultiIndex first second =
      fourthOrderMinorMultiIndex second first := by
  apply Subtype.ext
  dsimp [fourthOrderMinorMultiIndex]
  ac_rfl

@[simp] private theorem fourthOrderMinorMultiIndex_10_eq_01 :
    fourthOrderMinorMultiIndex 1 0 = fourthOrderMinorMultiIndex 0 1 :=
  fourthOrderMinorMultiIndex_comm 1 0

@[simp] private theorem fourthOrderMinorMultiIndex_20_eq_02 :
    fourthOrderMinorMultiIndex 2 0 = fourthOrderMinorMultiIndex 0 2 :=
  fourthOrderMinorMultiIndex_comm 2 0

@[simp] private theorem fourthOrderMinorMultiIndex_21_eq_12 :
    fourthOrderMinorMultiIndex 2 1 = fourthOrderMinorMultiIndex 1 2 :=
  fourthOrderMinorMultiIndex_comm 2 1

/-- The scalar two-by-two Hessian minor on genuine second jets. -/
def programPT06ScalarHessianMinorDensityEvaluation
    (minor : ProgramPT06ScalarHessianMinor4D) : SecondJet → Real :=
  fun jet =>
    secondOrderSecondProjection minor.first minor.first jet *
        secondOrderSecondProjection minor.second minor.second jet -
      secondOrderSecondProjection minor.first minor.second jet ^ 2

@[simp] theorem programPT06ScalarHessianMinorDensityEvaluation_apply
    (minor : ProgramPT06ScalarHessianMinor4D) (jet : SecondJet) :
    programPT06ScalarHessianMinorDensityEvaluation minor jet =
      jet (programPT06SecondOrderSecondMultiIndex minor.first minor.first) *
          jet (programPT06SecondOrderSecondMultiIndex minor.second minor.second) -
        jet (programPT06SecondOrderSecondMultiIndex minor.first minor.second) ^ 2 := by
  rfl

private def programPT06ScalarHessianMinorDensityDerivative
    (minor : ProgramPT06ScalarHessianMinor4D) (jet : SecondJet) :
    ContinuousLinearMap (RingHom.id Real) SecondJet Real :=
  (secondOrderSecondProjection minor.second minor.second jet) •
      secondOrderSecondProjection minor.first minor.first +
    (secondOrderSecondProjection minor.first minor.first jet) •
      secondOrderSecondProjection minor.second minor.second -
    (2 * secondOrderSecondProjection minor.first minor.second jet) •
      secondOrderSecondProjection minor.first minor.second

theorem programPT06ScalarHessianMinorDensityEvaluation_hasFDerivAt
    (minor : ProgramPT06ScalarHessianMinor4D) (jet : SecondJet) :
    HasFDerivAt
      (programPT06ScalarHessianMinorDensityEvaluation minor)
      (programPT06ScalarHessianMinorDensityDerivative minor jet) jet := by
  have hFirst :=
    (secondOrderSecondProjection minor.first minor.first).hasFDerivAt
      (x := jet)
  have hSecond :=
    (secondOrderSecondProjection minor.second minor.second).hasFDerivAt
      (x := jet)
  have hMixed :=
    (secondOrderSecondProjection minor.first minor.second).hasFDerivAt
      (x := jet)
  have hRaw := (hFirst.mul hSecond).sub (hMixed.pow 2)
  convert hRaw using 1
  · rfl
  · ext variation
    simp [programPT06ScalarHessianMinorDensityDerivative]
    ring

private theorem programPT06ScalarHessianMinorVerticalPartialZero
    (minor : ProgramPT06ScalarHessianMinor4D) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06ScalarHessianMinorDensityEvaluation minor) = 0 := by
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06ScalarHessianMinorDensityEvaluation minor) jet
      programPT06SecondOrderZeroMultiIndex variation = 0
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06ScalarHessianMinorDensityEvaluation minor) jet
    programPT06SecondOrderZeroMultiIndex
    (programPT06ScalarHessianMinorDensityDerivative minor jet)
    (programPT06ScalarHessianMinorDensityEvaluation_hasFDerivAt minor jet)]
  simp [programPT06ScalarHessianMinorDensityDerivative,
    secondOrderSecondProjection, secondOrderSecondMultiIndex_ne_zero]

private theorem programPT06ScalarHessianMinorVerticalPartialOne
    (minor : ProgramPT06ScalarHessianMinor4D) (direction : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06ScalarHessianMinorDensityEvaluation minor) direction = 0 := by
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06ScalarHessianMinorDensityEvaluation minor) jet
      (programPT06SecondOrderFirstMultiIndex direction) variation = 0
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06ScalarHessianMinorDensityEvaluation minor) jet
    (programPT06SecondOrderFirstMultiIndex direction)
    (programPT06ScalarHessianMinorDensityDerivative minor jet)
    (programPT06ScalarHessianMinorDensityEvaluation_hasFDerivAt minor jet)]
  simp [programPT06ScalarHessianMinorDensityDerivative,
    secondOrderSecondProjection,
    secondOrderSecondMultiIndex_ne_first]

private def programPT06ScalarHessianMinorCoordinateSelection
    (coordinate index : ThroatSpatialTruncatedIndex 2) : Real :=
  programPT06ThroatSpatialJetCoordinateInjection index (1 : Real) coordinate

@[simp] private theorem programPT06ScalarHessianMinorCoordinateSelection_same
    (index : ThroatSpatialTruncatedIndex 2) :
    programPT06ScalarHessianMinorCoordinateSelection index index = 1 := by
  unfold programPT06ScalarHessianMinorCoordinateSelection
  exact programPT06ThroatSpatialJetCoordinateInjection_same index 1

@[simp] private theorem programPT06ScalarHessianMinorCoordinateSelection_of_ne
    (coordinate index : ThroatSpatialTruncatedIndex 2)
    (hCoordinate : coordinate ≠ index) :
    programPT06ScalarHessianMinorCoordinateSelection coordinate index = 0 := by
  unfold programPT06ScalarHessianMinorCoordinateSelection
  exact programPT06ThroatSpatialJetCoordinateInjection_of_ne
    index coordinate hCoordinate 1

@[simp] private theorem programPT06ScalarHessianMinorCoordinateInjection_apply
    (index coordinate : ThroatSpatialTruncatedIndex 2)
    (variation : Real) :
    programPT06ThroatSpatialJetCoordinateInjection index variation coordinate =
      programPT06ScalarHessianMinorCoordinateSelection coordinate index *
        variation := by
  by_cases hCoordinate : coordinate = index
  · subst coordinate
    simp [programPT06ScalarHessianMinorCoordinateSelection]
  · simp [programPT06ScalarHessianMinorCoordinateSelection, hCoordinate]

private def programPT06ScalarHessianMinorVerticalTwoLinearMap
    (minor : ProgramPT06ScalarHessianMinor4D)
    (first second : Fin 3) :
    ContinuousLinearMap (RingHom.id Real) SecondJet RealCovector :=
  (secondOrderSecondProjection minor.second minor.second).smulRight
      (realCovector
        (programPT06ScalarHessianMinorCoordinateSelection
          (programPT06SecondOrderSecondMultiIndex minor.first minor.first)
          (programPT06SecondOrderSecondMultiIndex first second))) +
    (secondOrderSecondProjection minor.first minor.first).smulRight
      (realCovector
        (programPT06ScalarHessianMinorCoordinateSelection
          (programPT06SecondOrderSecondMultiIndex minor.second minor.second)
          (programPT06SecondOrderSecondMultiIndex first second))) -
    (secondOrderSecondProjection minor.first minor.second).smulRight
      (realCovector
        (2 * programPT06ScalarHessianMinorCoordinateSelection
          (programPT06SecondOrderSecondMultiIndex minor.first minor.second)
          (programPT06SecondOrderSecondMultiIndex first second)))

private theorem programPT06ScalarHessianMinorVerticalPartialTwo
    (minor : ProgramPT06ScalarHessianMinor4D)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06ScalarHessianMinorDensityEvaluation minor) first second =
      programPT06ScalarHessianMinorVerticalTwoLinearMap minor first second := by
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06ScalarHessianMinorDensityEvaluation minor) jet
      (programPT06SecondOrderSecondMultiIndex first second) variation = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06ScalarHessianMinorDensityEvaluation minor) jet
    (programPT06SecondOrderSecondMultiIndex first second)
    (programPT06ScalarHessianMinorDensityDerivative minor jet)
    (programPT06ScalarHessianMinorDensityEvaluation_hasFDerivAt minor jet)]
  simp [programPT06ScalarHessianMinorDensityDerivative,
    programPT06ScalarHessianMinorVerticalTwoLinearMap,
    secondOrderSecondProjection, realCovector]
  ring

private def programPT06ScalarHessianMinorFirstTotalLinearMap
    (direction : Fin 3)
    (linear : ContinuousLinearMap (RingHom.id Real) SecondJet RealCovector) :
    ContinuousLinearMap (RingHom.id Real) ThirdJet RealCovector :=
  (linear.toLinearMap.comp
    (throatSpatialTotalDerivativeLinear direction)).toContinuousLinearMap

private theorem programPT06ScalarHessianMinorFirstTotalDerivative_linear
    (direction : Fin 3)
    (linear : ContinuousLinearMap (RingHom.id Real) SecondJet RealCovector) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction linear =
      programPT06ScalarHessianMinorFirstTotalLinearMap direction linear := by
  funext jet
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_linear]
  rfl

private theorem programPT06ScalarHessianMinorIteratedTotalDerivative_linear
    (first second : Fin 3)
    (linear : ContinuousLinearMap (RingHom.id Real) SecondJet RealCovector)
    (jet : FourthJet) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative first
        (programPT06ThroatSpatialLocalFunctionTotalDerivative second linear)
        jet =
      linear
        (throatSpatialTotalDerivative second
          (throatSpatialTotalDerivative first jet)) := by
  rw [programPT06ScalarHessianMinorFirstTotalDerivative_linear]
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_linear]
  rfl

private theorem programPT06ScalarHessianMinorSecondEulerTerm
    (minor : ProgramPT06ScalarHessianMinor4D)
    (first second : Fin 3) (jet : FourthJet) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06ScalarHessianMinorDensityEvaluation minor)
        first second jet =
      programPT06ScalarHessianMinorVerticalTwoLinearMap minor first second
        (throatSpatialTotalDerivative second
          (throatSpatialTotalDerivative first jet)) := by
  rw [programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06ScalarHessianMinorVerticalPartialTwo]
  exact programPT06ScalarHessianMinorIteratedTotalDerivative_linear
    first second
    (programPT06ScalarHessianMinorVerticalTwoLinearMap minor first second) jet

private theorem programPT06ScalarHessianMinorSecondEulerTerm_apply
    (minor : ProgramPT06ScalarHessianMinor4D)
    (first second : Fin 3) (jet : FourthJet) (variation : Real) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06ScalarHessianMinorDensityEvaluation minor)
        first second jet variation =
      (secondOrderSecondProjection minor.second minor.second
            (throatSpatialTotalDerivative second
              (throatSpatialTotalDerivative first jet)) *
          programPT06ScalarHessianMinorCoordinateSelection
            (programPT06SecondOrderSecondMultiIndex minor.first minor.first)
            (programPT06SecondOrderSecondMultiIndex first second) +
        secondOrderSecondProjection minor.first minor.first
            (throatSpatialTotalDerivative second
              (throatSpatialTotalDerivative first jet)) *
          programPT06ScalarHessianMinorCoordinateSelection
            (programPT06SecondOrderSecondMultiIndex minor.second minor.second)
            (programPT06SecondOrderSecondMultiIndex first second) -
        2 * secondOrderSecondProjection minor.first minor.second
            (throatSpatialTotalDerivative second
              (throatSpatialTotalDerivative first jet)) *
          programPT06ScalarHessianMinorCoordinateSelection
            (programPT06SecondOrderSecondMultiIndex minor.first minor.second)
            (programPT06SecondOrderSecondMultiIndex first second)) *
        variation := by
  rw [programPT06ScalarHessianMinorSecondEulerTerm]
  simp [programPT06ScalarHessianMinorVerticalTwoLinearMap, realCovector]
  ring

private abbrev second00 : ThroatSpatialTruncatedIndex 2 :=
  programPT06SecondOrderSecondMultiIndex 0 0

private abbrev second01 : ThroatSpatialTruncatedIndex 2 :=
  programPT06SecondOrderSecondMultiIndex 0 1

private abbrev second02 : ThroatSpatialTruncatedIndex 2 :=
  programPT06SecondOrderSecondMultiIndex 0 2

private abbrev second11 : ThroatSpatialTruncatedIndex 2 :=
  programPT06SecondOrderSecondMultiIndex 1 1

private abbrev second12 : ThroatSpatialTruncatedIndex 2 :=
  programPT06SecondOrderSecondMultiIndex 1 2

private abbrev second22 : ThroatSpatialTruncatedIndex 2 :=
  programPT06SecondOrderSecondMultiIndex 2 2

@[simp] private theorem second10_eq_second01 :
    programPT06SecondOrderSecondMultiIndex 1 0 = second01 :=
  programPT06SecondOrderSecondMultiIndex_comm 1 0

@[simp] private theorem second20_eq_second02 :
    programPT06SecondOrderSecondMultiIndex 2 0 = second02 :=
  programPT06SecondOrderSecondMultiIndex_comm 2 0

@[simp] private theorem second21_eq_second12 :
    programPT06SecondOrderSecondMultiIndex 2 1 = second12 :=
  programPT06SecondOrderSecondMultiIndex_comm 2 1

private theorem secondOrderSecondMultiIndex_ne_of_coordinate
    (first second otherFirst otherSecond coordinate : Fin 3)
    (hCoordinate :
      (throatSpatialCoordinateMultiIndex first +
          throatSpatialCoordinateMultiIndex second) coordinate ≠
        (throatSpatialCoordinateMultiIndex otherFirst +
          throatSpatialCoordinateMultiIndex otherSecond) coordinate) :
    programPT06SecondOrderSecondMultiIndex first second ≠
      programPT06SecondOrderSecondMultiIndex otherFirst otherSecond := by
  intro hIndex
  apply hCoordinate
  exact congrArg
    (fun index : ThroatSpatialTruncatedIndex 2 => index.val coordinate) hIndex

@[simp] private theorem second00_ne_second01 : second00 ≠ second01 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 0 0 1 1
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second00_ne_second02 : second00 ≠ second02 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 0 0 2 2
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second00_ne_second11 : second00 ≠ second11 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 0 1 1 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second00_ne_second12 : second00 ≠ second12 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 0 1 2 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second00_ne_second22 : second00 ≠ second22 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 0 2 2 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second01_ne_second02 : second01 ≠ second02 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 1 0 2 1
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second01_ne_second11 : second01 ≠ second11 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 1 1 1 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second01_ne_second12 : second01 ≠ second12 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 1 1 2 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second01_ne_second22 : second01 ≠ second22 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 1 2 2 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second02_ne_second11 : second02 ≠ second11 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 2 1 1 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second02_ne_second12 : second02 ≠ second12 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 2 1 2 1
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second02_ne_second22 : second02 ≠ second22 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 2 2 2 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second11_ne_second12 : second11 ≠ second12 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 1 1 1 2 2
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second11_ne_second22 : second11 ≠ second22 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 1 1 2 2 1
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second12_ne_second22 : second12 ≠ second22 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 1 2 2 2 1
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second01_ne_second00 : second01 ≠ second00 :=
  Ne.symm second00_ne_second01

@[simp] private theorem second02_ne_second00 : second02 ≠ second00 :=
  Ne.symm second00_ne_second02

@[simp] private theorem second11_ne_second00 : second11 ≠ second00 :=
  Ne.symm second00_ne_second11

@[simp] private theorem second12_ne_second00 : second12 ≠ second00 :=
  Ne.symm second00_ne_second12

@[simp] private theorem second22_ne_second00 : second22 ≠ second00 :=
  Ne.symm second00_ne_second22

@[simp] private theorem second02_ne_second01 : second02 ≠ second01 :=
  Ne.symm second01_ne_second02

@[simp] private theorem second11_ne_second01 : second11 ≠ second01 :=
  Ne.symm second01_ne_second11

@[simp] private theorem second12_ne_second01 : second12 ≠ second01 :=
  Ne.symm second01_ne_second12

@[simp] private theorem second22_ne_second01 : second22 ≠ second01 :=
  Ne.symm second01_ne_second22

@[simp] private theorem second11_ne_second02 : second11 ≠ second02 :=
  Ne.symm second02_ne_second11

@[simp] private theorem second12_ne_second02 : second12 ≠ second02 :=
  Ne.symm second02_ne_second12

@[simp] private theorem second22_ne_second02 : second22 ≠ second02 :=
  Ne.symm second02_ne_second22

@[simp] private theorem second12_ne_second11 : second12 ≠ second11 :=
  Ne.symm second11_ne_second12

@[simp] private theorem second22_ne_second11 : second22 ≠ second11 :=
  Ne.symm second11_ne_second22

@[simp] private theorem second22_ne_second12 : second22 ≠ second12 :=
  Ne.symm second12_ne_second22

@[simp] private theorem totalDerivative_third_ssf_f
    (first second : Fin 3) (jet : FourthJet) :
    throatSpatialTotalDerivative first jet
        (thirdOrderThirdMultiIndex second second first) =
      jet (fourthOrderMinorMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [throatSpatialTotalDerivative, thirdOrderThirdMultiIndex,
    fourthOrderMinorMultiIndex]
  ac_rfl

@[simp] private theorem totalDerivative_third_fss_f
    (first second : Fin 3) (jet : FourthJet) :
    throatSpatialTotalDerivative first jet
        (thirdOrderThirdMultiIndex first second second) =
      jet (fourthOrderMinorMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [throatSpatialTotalDerivative, thirdOrderThirdMultiIndex,
    fourthOrderMinorMultiIndex]
  ac_rfl

@[simp] private theorem totalDerivative_third_fsf_s
    (first second : Fin 3) (jet : FourthJet) :
    throatSpatialTotalDerivative second jet
        (thirdOrderThirdMultiIndex first second first) =
      jet (fourthOrderMinorMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [throatSpatialTotalDerivative, thirdOrderThirdMultiIndex,
    fourthOrderMinorMultiIndex]
  ac_rfl

@[simp] private theorem totalDerivative_third_ffs_s
    (first second : Fin 3) (jet : FourthJet) :
    throatSpatialTotalDerivative second jet
        (thirdOrderThirdMultiIndex first first second) =
      jet (fourthOrderMinorMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [throatSpatialTotalDerivative, thirdOrderThirdMultiIndex,
    fourthOrderMinorMultiIndex]
  ac_rfl

private theorem programPT06ScalarHessianMinorSecondEulerSum_apply
    (minor : ProgramPT06ScalarHessianMinor4D)
    (jet : FourthJet) (variation : Real) :
    (∑ first : Fin 3, ∑ second : Fin 3,
      programPT06SecondOrderEulerSymmetryWeight first second •
        programPT06SecondOrderLocalEulerSecondTotalTerm
          (programPT06ScalarHessianMinorDensityEvaluation minor)
          first second jet variation) = 0 := by
  rcases minor with ⟨minorFirst, minorSecond, hDistinct⟩
  fin_cases minorFirst <;> fin_cases minorSecond
  all_goals try exact (hDistinct rfl).elim
  all_goals
    simp [Fin.sum_univ_three,
      programPT06ScalarHessianMinorSecondEulerTerm_apply,
      programPT06SecondOrderEulerSymmetryWeight]
    ring

/-- Gate880 annihilates the scalar Hessian minor.  The two ordered mixed
entries each carry the off-diagonal weight `1 / 2`. -/
theorem programPT06SecondOrderLocalEuler_scalarHessianMinor_eq_zero
    (minor : ProgramPT06ScalarHessianMinor4D) (jet : FourthJet) :
    programPT06SecondOrderLocalEuler
        (programPT06ScalarHessianMinorDensityEvaluation minor) jet = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  rw [programPT06SecondOrderLocalEuler_apply,
    programPT06ScalarHessianMinorVerticalPartialZero]
  have hFirst :
      (∑ direction : Fin 3,
        programPT06SecondOrderLocalEulerFirstTotalTerm
          (programPT06ScalarHessianMinorDensityEvaluation minor)
          direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)
          variation) = 0 := by
    apply Finset.sum_eq_zero
    intro direction _
    rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
      programPT06ScalarHessianMinorVerticalPartialOne]
    simp
  rw [hFirst,
    programPT06ScalarHessianMinorSecondEulerSum_apply minor jet variation]
  simp

/-- First nonzero component `u_i * u_jj` of the order-two current. -/
def programPT06ScalarHessianMinorCurrentFirstComponent
    (minor : ProgramPT06ScalarHessianMinor4D) : SecondJet → Real :=
  fun jet =>
    secondOrderFirstProjection minor.first jet *
      secondOrderSecondProjection minor.second minor.second jet

/-- Second nonzero component `-u_i * u_ij` of the order-two current. -/
def programPT06ScalarHessianMinorCurrentSecondComponent
    (minor : ProgramPT06ScalarHessianMinor4D) : SecondJet → Real :=
  fun jet =>
    -(secondOrderFirstProjection minor.first jet *
      secondOrderSecondProjection minor.first minor.second jet)

/-- Gate879 horizontal differential of the explicit two-component current. -/
def programPT06ScalarHessianMinorCurrentDH
    (minor : ProgramPT06ScalarHessianMinor4D) : ThirdJet → Real :=
  fun jet =>
    programPT06ThroatSpatialLocalFunctionTotalDerivative minor.first
        (programPT06ScalarHessianMinorCurrentFirstComponent minor) jet +
      programPT06ThroatSpatialLocalFunctionTotalDerivative minor.second
        (programPT06ScalarHessianMinorCurrentSecondComponent minor) jet

private def programPT06ScalarHessianMinorCurrentFirstDerivative
    (minor : ProgramPT06ScalarHessianMinor4D) (jet : SecondJet) :
    ContinuousLinearMap (RingHom.id Real) SecondJet Real :=
  (secondOrderSecondProjection minor.second minor.second jet) •
      secondOrderFirstProjection minor.first +
    (secondOrderFirstProjection minor.first jet) •
      secondOrderSecondProjection minor.second minor.second

private def programPT06ScalarHessianMinorCurrentSecondDerivative
    (minor : ProgramPT06ScalarHessianMinor4D) (jet : SecondJet) :
    ContinuousLinearMap (RingHom.id Real) SecondJet Real :=
  -((secondOrderSecondProjection minor.first minor.second jet) •
        secondOrderFirstProjection minor.first +
      (secondOrderFirstProjection minor.first jet) •
        secondOrderSecondProjection minor.first minor.second)

private theorem programPT06ScalarHessianMinorCurrentFirst_hasFDerivAt
    (minor : ProgramPT06ScalarHessianMinor4D) (jet : SecondJet) :
    HasFDerivAt
      (programPT06ScalarHessianMinorCurrentFirstComponent minor)
      (programPT06ScalarHessianMinorCurrentFirstDerivative minor jet) jet := by
  have hFirst :=
    (secondOrderFirstProjection minor.first).hasFDerivAt (x := jet)
  have hSecond :=
    (secondOrderSecondProjection minor.second minor.second).hasFDerivAt
      (x := jet)
  have hRaw := hFirst.mul hSecond
  change HasFDerivAt
    (fun candidate : SecondJet =>
      secondOrderFirstProjection minor.first candidate *
        secondOrderSecondProjection minor.second minor.second candidate)
    (programPT06ScalarHessianMinorCurrentFirstDerivative minor jet) jet
  apply hRaw.congr_fderiv
  ext variation
  simp [programPT06ScalarHessianMinorCurrentFirstDerivative]
  ring

private theorem programPT06ScalarHessianMinorCurrentSecond_hasFDerivAt
    (minor : ProgramPT06ScalarHessianMinor4D) (jet : SecondJet) :
    HasFDerivAt
      (programPT06ScalarHessianMinorCurrentSecondComponent minor)
      (programPT06ScalarHessianMinorCurrentSecondDerivative minor jet) jet := by
  have hFirst :=
    (secondOrderFirstProjection minor.first).hasFDerivAt (x := jet)
  have hMixed :=
    (secondOrderSecondProjection minor.first minor.second).hasFDerivAt
      (x := jet)
  have hRaw := (hFirst.mul hMixed).neg
  change HasFDerivAt
    (fun candidate : SecondJet =>
      -(secondOrderFirstProjection minor.first candidate *
        secondOrderSecondProjection minor.first minor.second candidate))
    (programPT06ScalarHessianMinorCurrentSecondDerivative minor jet) jet
  apply hRaw.congr_fderiv
  ext variation
  simp [programPT06ScalarHessianMinorCurrentSecondDerivative]
  ring

private theorem programPT06ScalarHessianMinorCurrentFirstTotalDerivative
    (minor : ProgramPT06ScalarHessianMinor4D) (jet : ThirdJet) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative minor.first
        (programPT06ScalarHessianMinorCurrentFirstComponent minor) jet =
      jet (thirdOrderSecondMultiIndex minor.first minor.first) *
          jet (thirdOrderSecondMultiIndex minor.second minor.second) +
        jet (thirdOrderFirstMultiIndex minor.first) *
          jet (thirdOrderThirdMultiIndex
            minor.second minor.second minor.first) := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    minor.first _ jet
    (programPT06ScalarHessianMinorCurrentFirstDerivative minor
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))
    (programPT06ScalarHessianMinorCurrentFirst_hasFDerivAt minor
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  simp [programPT06ScalarHessianMinorCurrentFirstDerivative]
  ring

private theorem programPT06ScalarHessianMinorCurrentSecondTotalDerivative
    (minor : ProgramPT06ScalarHessianMinor4D) (jet : ThirdJet) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative minor.second
        (programPT06ScalarHessianMinorCurrentSecondComponent minor) jet =
      -(jet (thirdOrderSecondMultiIndex minor.first minor.second) ^ 2 +
        jet (thirdOrderFirstMultiIndex minor.first) *
          jet (thirdOrderThirdMultiIndex
            minor.first minor.second minor.second)) := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    minor.second _ jet
    (programPT06ScalarHessianMinorCurrentSecondDerivative minor
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))
    (programPT06ScalarHessianMinorCurrentSecond_hasFDerivAt minor
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  simp [programPT06ScalarHessianMinorCurrentSecondDerivative]
  ring

/-- The two third-order current terms cancel, leaving exactly the pullback of
the Hessian-minor density to third jets. -/
theorem programPT06ScalarHessianMinorCurrentDH_eq_density
    (minor : ProgramPT06ScalarHessianMinor4D) (jet : ThirdJet) :
    programPT06ScalarHessianMinorCurrentDH minor jet =
      programPT06ScalarHessianMinorDensityEvaluation minor
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) := by
  rw [programPT06ScalarHessianMinorCurrentDH,
    programPT06ScalarHessianMinorCurrentFirstTotalDerivative,
    programPT06ScalarHessianMinorCurrentSecondTotalDerivative,
    thirdOrderThirdMultiIndex_cancel minor.first minor.second]
  simp [programPT06ScalarHessianMinorDensityEvaluation]
  ring

end
end P0EFTJanusProgramPT06ScalarHessianMinorNullLagrangian4D
end JanusFormal
