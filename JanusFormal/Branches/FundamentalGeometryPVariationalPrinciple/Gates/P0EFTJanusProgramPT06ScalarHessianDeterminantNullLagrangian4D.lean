import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderLocalEuler4D

/-!
# Scalar Hessian-determinant null Lagrangian

This gate treats the determinant of the scalar Hessian in the three throat
directions.  The density is written on genuine second jets with one copy of
each symmetric off-diagonal coordinate.  Gate880 therefore uses its prescribed
`1 / 2` weight on both ordered copies of every mixed coordinate.

The proof of Euler annihilation is direct: the six weighted vertical second
partials are differentiated once, the three rows satisfy the Piola identities,
and differentiating those identities gives the nine Gate880 second-total
terms.  No null-Lagrangian certificate is assumed.

An explicit order-two current is the first-row cofactor current.  Its three
Gate879 total derivatives cancel all third-order jets and leave the determinant.
The result concerns one scalar field and its unique three-direction Hessian
determinant; it is not a classification of the full T02 kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ScalarHessianDeterminantNullLagrangian4D

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

private def secondOrderFirstProjection (direction : Fin 3) :
    SecondJet →L[Real] Real :=
  ContinuousLinearMap.proj
    (programPT06SecondOrderFirstMultiIndex direction)

private def secondOrderSecondProjection (first second : Fin 3) :
    SecondJet →L[Real] Real :=
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

private def realCovector (coefficient : Real) : RealCovector :=
  ContinuousLinearMap.lsmul Real Real coefficient

private def realCovectorLift : Real →L[Real] RealCovector :=
  ContinuousLinearMap.lsmul Real Real

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

private theorem thirdOrderThirdMultiIndex_perm
    (first second third otherFirst otherSecond otherThird : Fin 3)
    (hPermutation :
      (throatSpatialCoordinateMultiIndex first +
          throatSpatialCoordinateMultiIndex second) +
          throatSpatialCoordinateMultiIndex third =
        (throatSpatialCoordinateMultiIndex otherFirst +
          throatSpatialCoordinateMultiIndex otherSecond) +
          throatSpatialCoordinateMultiIndex otherThird) :
    thirdOrderThirdMultiIndex first second third =
      thirdOrderThirdMultiIndex otherFirst otherSecond otherThird := by
  apply Subtype.ext
  exact hPermutation

@[simp] private theorem third110_eq_third011 :
    thirdOrderThirdMultiIndex 1 1 0 = thirdOrderThirdMultiIndex 0 1 1 := by
  apply thirdOrderThirdMultiIndex_perm
  ac_rfl

@[simp] private theorem third220_eq_third022 :
    thirdOrderThirdMultiIndex 2 2 0 = thirdOrderThirdMultiIndex 0 2 2 := by
  apply thirdOrderThirdMultiIndex_perm
  ac_rfl

@[simp] private theorem third120_eq_third012 :
    thirdOrderThirdMultiIndex 1 2 0 = thirdOrderThirdMultiIndex 0 1 2 := by
  apply thirdOrderThirdMultiIndex_perm
  ac_rfl

@[simp] private theorem third021_eq_third012 :
    thirdOrderThirdMultiIndex 0 2 1 = thirdOrderThirdMultiIndex 0 1 2 := by
  apply thirdOrderThirdMultiIndex_perm
  ac_rfl

@[simp] private theorem third121_eq_third112 :
    thirdOrderThirdMultiIndex 1 2 1 = thirdOrderThirdMultiIndex 1 1 2 := by
  apply thirdOrderThirdMultiIndex_perm
  ac_rfl

@[simp] private theorem third221_eq_third122 :
    thirdOrderThirdMultiIndex 2 2 1 = thirdOrderThirdMultiIndex 1 2 2 := by
  apply thirdOrderThirdMultiIndex_perm
  ac_rfl

@[simp] private theorem third020_eq_third002 :
    thirdOrderThirdMultiIndex 0 2 0 = thirdOrderThirdMultiIndex 0 0 2 := by
  apply thirdOrderThirdMultiIndex_perm
  ac_rfl

@[simp] private theorem third010_eq_third001 :
    thirdOrderThirdMultiIndex 0 1 0 = thirdOrderThirdMultiIndex 0 0 1 := by
  apply thirdOrderThirdMultiIndex_perm
  ac_rfl

/-- The explicit symmetric formula for the three-direction scalar Hessian
determinant. -/
def programPT06ScalarHessianDeterminantDensityEvaluation : SecondJet → Real :=
  fun jet =>
    secondOrderSecondProjection 0 0 jet *
          secondOrderSecondProjection 1 1 jet *
          secondOrderSecondProjection 2 2 jet +
      2 * secondOrderSecondProjection 0 1 jet *
          secondOrderSecondProjection 0 2 jet *
          secondOrderSecondProjection 1 2 jet -
      secondOrderSecondProjection 0 0 jet *
          secondOrderSecondProjection 1 2 jet ^ 2 -
      secondOrderSecondProjection 1 1 jet *
          secondOrderSecondProjection 0 2 jet ^ 2 -
      secondOrderSecondProjection 2 2 jet *
          secondOrderSecondProjection 0 1 jet ^ 2

private def cofactor00 (jet : SecondJet) : Real :=
  secondOrderSecondProjection 1 1 jet *
      secondOrderSecondProjection 2 2 jet -
    secondOrderSecondProjection 1 2 jet ^ 2

private def cofactor01 (jet : SecondJet) : Real :=
  secondOrderSecondProjection 0 2 jet *
      secondOrderSecondProjection 1 2 jet -
    secondOrderSecondProjection 0 1 jet *
      secondOrderSecondProjection 2 2 jet

private def cofactor02 (jet : SecondJet) : Real :=
  secondOrderSecondProjection 0 1 jet *
      secondOrderSecondProjection 1 2 jet -
    secondOrderSecondProjection 0 2 jet *
      secondOrderSecondProjection 1 1 jet

private def cofactor11 (jet : SecondJet) : Real :=
  secondOrderSecondProjection 0 0 jet *
      secondOrderSecondProjection 2 2 jet -
    secondOrderSecondProjection 0 2 jet ^ 2

private def cofactor12 (jet : SecondJet) : Real :=
  secondOrderSecondProjection 0 1 jet *
      secondOrderSecondProjection 0 2 jet -
    secondOrderSecondProjection 0 0 jet *
      secondOrderSecondProjection 1 2 jet

private def cofactor22 (jet : SecondJet) : Real :=
  secondOrderSecondProjection 0 0 jet *
      secondOrderSecondProjection 1 1 jet -
    secondOrderSecondProjection 0 1 jet ^ 2

private def partial00 : SecondJet → Real := cofactor00
private def partial01 : SecondJet → Real := fun jet => 2 * cofactor01 jet
private def partial02 : SecondJet → Real := fun jet => 2 * cofactor02 jet
private def partial11 : SecondJet → Real := cofactor11
private def partial12 : SecondJet → Real := fun jet => 2 * cofactor12 jet
private def partial22 : SecondJet → Real := cofactor22

private def programPT06ScalarHessianDeterminantDensityDerivative
    (jet : SecondJet) : SecondJet →L[Real] Real :=
  partial00 jet • secondOrderSecondProjection 0 0 +
    partial01 jet • secondOrderSecondProjection 0 1 +
    partial02 jet • secondOrderSecondProjection 0 2 +
    partial11 jet • secondOrderSecondProjection 1 1 +
    partial12 jet • secondOrderSecondProjection 1 2 +
    partial22 jet • secondOrderSecondProjection 2 2

theorem programPT06ScalarHessianDeterminantDensityEvaluation_hasFDerivAt
    (jet : SecondJet) :
    HasFDerivAt programPT06ScalarHessianDeterminantDensityEvaluation
      (programPT06ScalarHessianDeterminantDensityDerivative jet) jet := by
  have h00 := (secondOrderSecondProjection 0 0).hasFDerivAt (x := jet)
  have h01 := (secondOrderSecondProjection 0 1).hasFDerivAt (x := jet)
  have h02 := (secondOrderSecondProjection 0 2).hasFDerivAt (x := jet)
  have h11 := (secondOrderSecondProjection 1 1).hasFDerivAt (x := jet)
  have h12 := (secondOrderSecondProjection 1 2).hasFDerivAt (x := jet)
  have h22 := (secondOrderSecondProjection 2 2).hasFDerivAt (x := jet)
  have hRaw :=
    (((h00.mul h11).mul h22).add
      (((h01.mul h02).mul h12).const_mul 2)).sub
      (((h00.mul (h12.pow 2)).add (h11.mul (h02.pow 2))).add
        (h22.mul (h01.pow 2)))
  convert hRaw using 1
  · funext candidate
    dsimp [programPT06ScalarHessianDeterminantDensityEvaluation]
    ring
  · ext variation
    simp [programPT06ScalarHessianDeterminantDensityDerivative,
      partial00, partial01, partial02, partial11, partial12, partial22,
      cofactor00, cofactor01, cofactor02, cofactor11, cofactor12,
      cofactor22]
    ring

private theorem programPT06ScalarHessianDeterminantVerticalPartialZero :
    programPT06SecondOrderLocalVerticalPartialZero
        programPT06ScalarHessianDeterminantDensityEvaluation = 0 := by
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  change programPT06ThroatSpatialVerticalPartialDerivative
    programPT06ScalarHessianDeterminantDensityEvaluation jet
      programPT06SecondOrderZeroMultiIndex variation = 0
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    programPT06ScalarHessianDeterminantDensityEvaluation jet
    programPT06SecondOrderZeroMultiIndex
    (programPT06ScalarHessianDeterminantDensityDerivative jet)
    (programPT06ScalarHessianDeterminantDensityEvaluation_hasFDerivAt jet)]
  simp [programPT06ScalarHessianDeterminantDensityDerivative,
    secondOrderSecondProjection, secondOrderSecondMultiIndex_ne_zero]

private theorem programPT06ScalarHessianDeterminantVerticalPartialOne
    (direction : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialOne
        programPT06ScalarHessianDeterminantDensityEvaluation direction = 0 := by
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  change programPT06ThroatSpatialVerticalPartialDerivative
    programPT06ScalarHessianDeterminantDensityEvaluation jet
      (programPT06SecondOrderFirstMultiIndex direction) variation = 0
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    programPT06ScalarHessianDeterminantDensityEvaluation jet
    (programPT06SecondOrderFirstMultiIndex direction)
    (programPT06ScalarHessianDeterminantDensityDerivative jet)
    (programPT06ScalarHessianDeterminantDensityEvaluation_hasFDerivAt jet)]
  simp [programPT06ScalarHessianDeterminantDensityDerivative,
    secondOrderSecondProjection, secondOrderSecondMultiIndex_ne_first]

private def coordinateSelection
    (coordinate index : ThroatSpatialTruncatedIndex 2) : Real :=
  programPT06ThroatSpatialJetCoordinateInjection index (1 : Real) coordinate

@[simp] private theorem coordinateSelection_same
    (index : ThroatSpatialTruncatedIndex 2) :
    coordinateSelection index index = 1 := by
  unfold coordinateSelection
  exact programPT06ThroatSpatialJetCoordinateInjection_same index 1

@[simp] private theorem coordinateSelection_of_ne
    (coordinate index : ThroatSpatialTruncatedIndex 2)
    (hCoordinate : coordinate ≠ index) :
    coordinateSelection coordinate index = 0 := by
  unfold coordinateSelection
  exact programPT06ThroatSpatialJetCoordinateInjection_of_ne
    index coordinate hCoordinate 1

@[simp] private theorem coordinateInjection_apply
    (index coordinate : ThroatSpatialTruncatedIndex 2) (variation : Real) :
    programPT06ThroatSpatialJetCoordinateInjection index variation coordinate =
      coordinateSelection coordinate index * variation := by
  by_cases hCoordinate : coordinate = index
  · subst coordinate
    simp [coordinateSelection]
  · simp [coordinateSelection, hCoordinate]

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

private def verticalTwoMap (first second : Fin 3) :
    SecondJet → RealCovector :=
  fun jet =>
    realCovector
      (partial00 jet * coordinateSelection second00
          (programPT06SecondOrderSecondMultiIndex first second) +
        partial01 jet * coordinateSelection second01
          (programPT06SecondOrderSecondMultiIndex first second) +
        partial02 jet * coordinateSelection second02
          (programPT06SecondOrderSecondMultiIndex first second) +
        partial11 jet * coordinateSelection second11
          (programPT06SecondOrderSecondMultiIndex first second) +
        partial12 jet * coordinateSelection second12
          (programPT06SecondOrderSecondMultiIndex first second) +
        partial22 jet * coordinateSelection second22
          (programPT06SecondOrderSecondMultiIndex first second))

private theorem verticalPartialTwo (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        programPT06ScalarHessianDeterminantDensityEvaluation first second =
      verticalTwoMap first second := by
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  change programPT06ThroatSpatialVerticalPartialDerivative
    programPT06ScalarHessianDeterminantDensityEvaluation jet
      (programPT06SecondOrderSecondMultiIndex first second) variation = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    programPT06ScalarHessianDeterminantDensityEvaluation jet
    (programPT06SecondOrderSecondMultiIndex first second)
    (programPT06ScalarHessianDeterminantDensityDerivative jet)
    (programPT06ScalarHessianDeterminantDensityEvaluation_hasFDerivAt jet)]
  simp [programPT06ScalarHessianDeterminantDensityDerivative,
    verticalTwoMap, secondOrderSecondProjection, realCovector]
  ring

private theorem verticalPartialTwo_00 :
    programPT06SecondOrderLocalVerticalPartialTwo
        programPT06ScalarHessianDeterminantDensityEvaluation 0 0 =
      fun jet => realCovector (partial00 jet) := by
  rw [verticalPartialTwo]
  funext jet
  simp [verticalTwoMap]

private theorem verticalPartialTwo_01 :
    programPT06SecondOrderLocalVerticalPartialTwo
        programPT06ScalarHessianDeterminantDensityEvaluation 0 1 =
      fun jet => realCovector (partial01 jet) := by
  rw [verticalPartialTwo]
  funext jet
  simp [verticalTwoMap]

private theorem verticalPartialTwo_02 :
    programPT06SecondOrderLocalVerticalPartialTwo
        programPT06ScalarHessianDeterminantDensityEvaluation 0 2 =
      fun jet => realCovector (partial02 jet) := by
  rw [verticalPartialTwo]
  funext jet
  simp [verticalTwoMap]

private theorem verticalPartialTwo_10 :
    programPT06SecondOrderLocalVerticalPartialTwo
        programPT06ScalarHessianDeterminantDensityEvaluation 1 0 =
      fun jet => realCovector (partial01 jet) := by
  rw [verticalPartialTwo]
  funext jet
  simp [verticalTwoMap]

private theorem verticalPartialTwo_11 :
    programPT06SecondOrderLocalVerticalPartialTwo
        programPT06ScalarHessianDeterminantDensityEvaluation 1 1 =
      fun jet => realCovector (partial11 jet) := by
  rw [verticalPartialTwo]
  funext jet
  simp [verticalTwoMap]

private theorem verticalPartialTwo_12 :
    programPT06SecondOrderLocalVerticalPartialTwo
        programPT06ScalarHessianDeterminantDensityEvaluation 1 2 =
      fun jet => realCovector (partial12 jet) := by
  rw [verticalPartialTwo]
  funext jet
  simp [verticalTwoMap]

private theorem verticalPartialTwo_20 :
    programPT06SecondOrderLocalVerticalPartialTwo
        programPT06ScalarHessianDeterminantDensityEvaluation 2 0 =
      fun jet => realCovector (partial02 jet) := by
  rw [verticalPartialTwo]
  funext jet
  simp [verticalTwoMap]

private theorem verticalPartialTwo_21 :
    programPT06SecondOrderLocalVerticalPartialTwo
        programPT06ScalarHessianDeterminantDensityEvaluation 2 1 =
      fun jet => realCovector (partial12 jet) := by
  rw [verticalPartialTwo]
  funext jet
  simp [verticalTwoMap]

private theorem verticalPartialTwo_22 :
    programPT06SecondOrderLocalVerticalPartialTwo
        programPT06ScalarHessianDeterminantDensityEvaluation 2 2 =
      fun jet => realCovector (partial22 jet) := by
  rw [verticalPartialTwo]
  funext jet
  simp [verticalTwoMap]

private def partial00Derivative (jet : SecondJet) : SecondJet →L[Real] Real :=
  secondOrderSecondProjection 2 2 jet • secondOrderSecondProjection 1 1 +
    secondOrderSecondProjection 1 1 jet • secondOrderSecondProjection 2 2 -
    (2 * secondOrderSecondProjection 1 2 jet) •
      secondOrderSecondProjection 1 2

private def partial01Derivative (jet : SecondJet) : SecondJet →L[Real] Real :=
  2 •
    (secondOrderSecondProjection 1 2 jet • secondOrderSecondProjection 0 2 +
      secondOrderSecondProjection 0 2 jet • secondOrderSecondProjection 1 2 -
      (secondOrderSecondProjection 2 2 jet • secondOrderSecondProjection 0 1 +
        secondOrderSecondProjection 0 1 jet • secondOrderSecondProjection 2 2))

private def partial02Derivative (jet : SecondJet) : SecondJet →L[Real] Real :=
  2 •
    (secondOrderSecondProjection 1 2 jet • secondOrderSecondProjection 0 1 +
      secondOrderSecondProjection 0 1 jet • secondOrderSecondProjection 1 2 -
      (secondOrderSecondProjection 1 1 jet • secondOrderSecondProjection 0 2 +
        secondOrderSecondProjection 0 2 jet • secondOrderSecondProjection 1 1))

private def partial11Derivative (jet : SecondJet) : SecondJet →L[Real] Real :=
  secondOrderSecondProjection 2 2 jet • secondOrderSecondProjection 0 0 +
    secondOrderSecondProjection 0 0 jet • secondOrderSecondProjection 2 2 -
    (2 * secondOrderSecondProjection 0 2 jet) •
      secondOrderSecondProjection 0 2

private def partial12Derivative (jet : SecondJet) : SecondJet →L[Real] Real :=
  2 •
    (secondOrderSecondProjection 0 2 jet • secondOrderSecondProjection 0 1 +
      secondOrderSecondProjection 0 1 jet • secondOrderSecondProjection 0 2 -
      (secondOrderSecondProjection 1 2 jet • secondOrderSecondProjection 0 0 +
        secondOrderSecondProjection 0 0 jet • secondOrderSecondProjection 1 2))

private def partial22Derivative (jet : SecondJet) : SecondJet →L[Real] Real :=
  secondOrderSecondProjection 1 1 jet • secondOrderSecondProjection 0 0 +
    secondOrderSecondProjection 0 0 jet • secondOrderSecondProjection 1 1 -
    (2 * secondOrderSecondProjection 0 1 jet) •
      secondOrderSecondProjection 0 1

private theorem partial00_hasFDerivAt (jet : SecondJet) :
    HasFDerivAt partial00 (partial00Derivative jet) jet := by
  have h11 := (secondOrderSecondProjection 1 1).hasFDerivAt (x := jet)
  have h12 := (secondOrderSecondProjection 1 2).hasFDerivAt (x := jet)
  have h22 := (secondOrderSecondProjection 2 2).hasFDerivAt (x := jet)
  have hRaw := (h11.mul h22).sub (h12.pow 2)
  convert hRaw using 1
  · rfl
  · ext variation
    simp [partial00Derivative]
    ring

private theorem partial01_hasFDerivAt (jet : SecondJet) :
    HasFDerivAt partial01 (partial01Derivative jet) jet := by
  have h01 := (secondOrderSecondProjection 0 1).hasFDerivAt (x := jet)
  have h02 := (secondOrderSecondProjection 0 2).hasFDerivAt (x := jet)
  have h12 := (secondOrderSecondProjection 1 2).hasFDerivAt (x := jet)
  have h22 := (secondOrderSecondProjection 2 2).hasFDerivAt (x := jet)
  have hRaw := ((h02.mul h12).sub (h01.mul h22)).const_mul 2
  change HasFDerivAt
    (fun candidate : SecondJet =>
      2 * (secondOrderSecondProjection 0 2 candidate *
          secondOrderSecondProjection 1 2 candidate -
        secondOrderSecondProjection 0 1 candidate *
          secondOrderSecondProjection 2 2 candidate))
    (partial01Derivative jet) jet
  apply hRaw.congr_fderiv
  ext variation
  simp [partial01Derivative]
  ring

private theorem partial02_hasFDerivAt (jet : SecondJet) :
    HasFDerivAt partial02 (partial02Derivative jet) jet := by
  have h01 := (secondOrderSecondProjection 0 1).hasFDerivAt (x := jet)
  have h02 := (secondOrderSecondProjection 0 2).hasFDerivAt (x := jet)
  have h11 := (secondOrderSecondProjection 1 1).hasFDerivAt (x := jet)
  have h12 := (secondOrderSecondProjection 1 2).hasFDerivAt (x := jet)
  have hRaw := ((h01.mul h12).sub (h02.mul h11)).const_mul 2
  change HasFDerivAt
    (fun candidate : SecondJet =>
      2 * (secondOrderSecondProjection 0 1 candidate *
          secondOrderSecondProjection 1 2 candidate -
        secondOrderSecondProjection 0 2 candidate *
          secondOrderSecondProjection 1 1 candidate))
    (partial02Derivative jet) jet
  apply hRaw.congr_fderiv
  ext variation
  simp [partial02Derivative]
  ring

private theorem partial11_hasFDerivAt (jet : SecondJet) :
    HasFDerivAt partial11 (partial11Derivative jet) jet := by
  have h00 := (secondOrderSecondProjection 0 0).hasFDerivAt (x := jet)
  have h02 := (secondOrderSecondProjection 0 2).hasFDerivAt (x := jet)
  have h22 := (secondOrderSecondProjection 2 2).hasFDerivAt (x := jet)
  have hRaw := (h00.mul h22).sub (h02.pow 2)
  convert hRaw using 1
  · rfl
  · ext variation
    simp [partial11Derivative]
    ring

private theorem partial12_hasFDerivAt (jet : SecondJet) :
    HasFDerivAt partial12 (partial12Derivative jet) jet := by
  have h00 := (secondOrderSecondProjection 0 0).hasFDerivAt (x := jet)
  have h01 := (secondOrderSecondProjection 0 1).hasFDerivAt (x := jet)
  have h02 := (secondOrderSecondProjection 0 2).hasFDerivAt (x := jet)
  have h12 := (secondOrderSecondProjection 1 2).hasFDerivAt (x := jet)
  have hRaw := ((h01.mul h02).sub (h00.mul h12)).const_mul 2
  change HasFDerivAt
    (fun candidate : SecondJet =>
      2 * (secondOrderSecondProjection 0 1 candidate *
          secondOrderSecondProjection 0 2 candidate -
        secondOrderSecondProjection 0 0 candidate *
          secondOrderSecondProjection 1 2 candidate))
    (partial12Derivative jet) jet
  apply hRaw.congr_fderiv
  ext variation
  simp [partial12Derivative]
  ring

private theorem partial22_hasFDerivAt (jet : SecondJet) :
    HasFDerivAt partial22 (partial22Derivative jet) jet := by
  have h00 := (secondOrderSecondProjection 0 0).hasFDerivAt (x := jet)
  have h01 := (secondOrderSecondProjection 0 1).hasFDerivAt (x := jet)
  have h11 := (secondOrderSecondProjection 1 1).hasFDerivAt (x := jet)
  have hRaw := (h00.mul h11).sub (h01.pow 2)
  convert hRaw using 1
  · rfl
  · ext variation
    simp [partial22Derivative]
    ring

private theorem totalDerivative_realCovector
    (function : SecondJet → Real) (derivative : SecondJet →L[Real] Real)
    (direction : Fin 3) (jet : ThirdJet)
    (hDerivative : HasFDerivAt function derivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun candidate => realCovector (function candidate)) jet =
      realCovector (derivative (throatSpatialTotalDerivative direction jet)) := by
  have hComposed := realCovectorLift.hasFDerivAt.comp
    (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) hDerivative
  change HasFDerivAt (fun candidate => realCovector (function candidate))
    (realCovectorLift.comp derivative)
    (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) at hComposed
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    direction _ jet (realCovectorLift.comp derivative) hComposed]
  rfl

private def inner00 (jet : ThirdJet) : RealCovector :=
  realCovector
    (jet (thirdOrderThirdMultiIndex 0 1 1) *
          jet (thirdOrderSecondMultiIndex 2 2) +
      jet (thirdOrderSecondMultiIndex 1 1) *
          jet (thirdOrderThirdMultiIndex 0 2 2) -
      2 * jet (thirdOrderSecondMultiIndex 1 2) *
          jet (thirdOrderThirdMultiIndex 0 1 2))

private def inner01 (jet : ThirdJet) : RealCovector :=
  realCovector
    (2 * (jet (thirdOrderThirdMultiIndex 0 1 2) *
            jet (thirdOrderSecondMultiIndex 1 2) +
        jet (thirdOrderSecondMultiIndex 0 2) *
            jet (thirdOrderThirdMultiIndex 1 1 2) -
        jet (thirdOrderThirdMultiIndex 0 1 1) *
            jet (thirdOrderSecondMultiIndex 2 2) -
        jet (thirdOrderSecondMultiIndex 0 1) *
            jet (thirdOrderThirdMultiIndex 1 2 2)))

private def inner02 (jet : ThirdJet) : RealCovector :=
  realCovector
    (2 * (jet (thirdOrderThirdMultiIndex 0 1 2) *
            jet (thirdOrderSecondMultiIndex 1 2) +
        jet (thirdOrderSecondMultiIndex 0 1) *
            jet (thirdOrderThirdMultiIndex 1 2 2) -
        jet (thirdOrderThirdMultiIndex 0 2 2) *
            jet (thirdOrderSecondMultiIndex 1 1) -
        jet (thirdOrderSecondMultiIndex 0 2) *
            jet (thirdOrderThirdMultiIndex 1 1 2)))

private def inner10 (jet : ThirdJet) : RealCovector :=
  realCovector
    (2 * (jet (thirdOrderThirdMultiIndex 0 0 2) *
            jet (thirdOrderSecondMultiIndex 1 2) +
        jet (thirdOrderSecondMultiIndex 0 2) *
            jet (thirdOrderThirdMultiIndex 0 1 2) -
        jet (thirdOrderThirdMultiIndex 0 0 1) *
            jet (thirdOrderSecondMultiIndex 2 2) -
        jet (thirdOrderSecondMultiIndex 0 1) *
            jet (thirdOrderThirdMultiIndex 0 2 2)))

private def inner11 (jet : ThirdJet) : RealCovector :=
  realCovector
    (jet (thirdOrderThirdMultiIndex 0 0 1) *
          jet (thirdOrderSecondMultiIndex 2 2) +
      jet (thirdOrderSecondMultiIndex 0 0) *
          jet (thirdOrderThirdMultiIndex 1 2 2) -
      2 * jet (thirdOrderSecondMultiIndex 0 2) *
          jet (thirdOrderThirdMultiIndex 0 1 2))

private def inner12 (jet : ThirdJet) : RealCovector :=
  realCovector
    (2 * (jet (thirdOrderThirdMultiIndex 0 1 2) *
            jet (thirdOrderSecondMultiIndex 0 2) +
        jet (thirdOrderSecondMultiIndex 0 1) *
            jet (thirdOrderThirdMultiIndex 0 2 2) -
        jet (thirdOrderThirdMultiIndex 0 0 2) *
            jet (thirdOrderSecondMultiIndex 1 2) -
        jet (thirdOrderSecondMultiIndex 0 0) *
            jet (thirdOrderThirdMultiIndex 1 2 2)))

private def inner20 (jet : ThirdJet) : RealCovector :=
  realCovector
    (2 * (jet (thirdOrderThirdMultiIndex 0 0 1) *
            jet (thirdOrderSecondMultiIndex 1 2) +
        jet (thirdOrderSecondMultiIndex 0 1) *
            jet (thirdOrderThirdMultiIndex 0 1 2) -
        jet (thirdOrderThirdMultiIndex 0 0 2) *
            jet (thirdOrderSecondMultiIndex 1 1) -
        jet (thirdOrderSecondMultiIndex 0 2) *
            jet (thirdOrderThirdMultiIndex 0 1 1)))

private def inner21 (jet : ThirdJet) : RealCovector :=
  realCovector
    (2 * (jet (thirdOrderThirdMultiIndex 0 1 1) *
            jet (thirdOrderSecondMultiIndex 0 2) +
        jet (thirdOrderSecondMultiIndex 0 1) *
            jet (thirdOrderThirdMultiIndex 0 1 2) -
        jet (thirdOrderThirdMultiIndex 0 0 1) *
            jet (thirdOrderSecondMultiIndex 1 2) -
        jet (thirdOrderSecondMultiIndex 0 0) *
            jet (thirdOrderThirdMultiIndex 1 1 2)))

private def inner22 (jet : ThirdJet) : RealCovector :=
  realCovector
    (jet (thirdOrderThirdMultiIndex 0 0 2) *
          jet (thirdOrderSecondMultiIndex 1 1) +
      jet (thirdOrderSecondMultiIndex 0 0) *
          jet (thirdOrderThirdMultiIndex 1 1 2) -
      2 * jet (thirdOrderSecondMultiIndex 0 1) *
          jet (thirdOrderThirdMultiIndex 0 1 2))

private theorem firstTotal00 :
    programPT06ThroatSpatialLocalFunctionTotalDerivative 0
        (programPT06SecondOrderLocalVerticalPartialTwo
          programPT06ScalarHessianDeterminantDensityEvaluation 0 0) =
      inner00 := by
  rw [verticalPartialTwo_00]
  funext jet
  rw [totalDerivative_realCovector partial00
    (partial00Derivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) 0 jet
    (partial00_hasFDerivAt
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  apply ContinuousLinearMap.ext
  intro variation
  simp [partial00Derivative, inner00, realCovector]
  exact Or.inl (by ring)

private theorem firstTotal01 :
    programPT06ThroatSpatialLocalFunctionTotalDerivative 1
        (programPT06SecondOrderLocalVerticalPartialTwo
          programPT06ScalarHessianDeterminantDensityEvaluation 0 1) =
      inner01 := by
  rw [verticalPartialTwo_01]
  funext jet
  rw [totalDerivative_realCovector partial01
    (partial01Derivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) 1 jet
    (partial01_hasFDerivAt
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  apply ContinuousLinearMap.ext
  intro variation
  simp [partial01Derivative, inner01, realCovector]
  exact Or.inl (by ring)

private theorem firstTotal02 :
    programPT06ThroatSpatialLocalFunctionTotalDerivative 2
        (programPT06SecondOrderLocalVerticalPartialTwo
          programPT06ScalarHessianDeterminantDensityEvaluation 0 2) =
      inner02 := by
  rw [verticalPartialTwo_02]
  funext jet
  rw [totalDerivative_realCovector partial02
    (partial02Derivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) 2 jet
    (partial02_hasFDerivAt
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  apply ContinuousLinearMap.ext
  intro variation
  simp [partial02Derivative, inner02, realCovector]
  exact Or.inl (by ring)

private theorem firstTotal10 :
    programPT06ThroatSpatialLocalFunctionTotalDerivative 0
        (programPT06SecondOrderLocalVerticalPartialTwo
          programPT06ScalarHessianDeterminantDensityEvaluation 1 0) =
      inner10 := by
  rw [verticalPartialTwo_10]
  funext jet
  rw [totalDerivative_realCovector partial01
    (partial01Derivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) 0 jet
    (partial01_hasFDerivAt
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  apply ContinuousLinearMap.ext
  intro variation
  simp [partial01Derivative, inner10, realCovector]
  exact Or.inl (by ring)

private theorem firstTotal11 :
    programPT06ThroatSpatialLocalFunctionTotalDerivative 1
        (programPT06SecondOrderLocalVerticalPartialTwo
          programPT06ScalarHessianDeterminantDensityEvaluation 1 1) =
      inner11 := by
  rw [verticalPartialTwo_11]
  funext jet
  rw [totalDerivative_realCovector partial11
    (partial11Derivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) 1 jet
    (partial11_hasFDerivAt
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  apply ContinuousLinearMap.ext
  intro variation
  simp [partial11Derivative, inner11, realCovector]
  exact Or.inl (by ring)

private theorem firstTotal12 :
    programPT06ThroatSpatialLocalFunctionTotalDerivative 2
        (programPT06SecondOrderLocalVerticalPartialTwo
          programPT06ScalarHessianDeterminantDensityEvaluation 1 2) =
      inner12 := by
  rw [verticalPartialTwo_12]
  funext jet
  rw [totalDerivative_realCovector partial12
    (partial12Derivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) 2 jet
    (partial12_hasFDerivAt
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  apply ContinuousLinearMap.ext
  intro variation
  simp [partial12Derivative, inner12, realCovector]
  exact Or.inl (by ring)

private theorem firstTotal20 :
    programPT06ThroatSpatialLocalFunctionTotalDerivative 0
        (programPT06SecondOrderLocalVerticalPartialTwo
          programPT06ScalarHessianDeterminantDensityEvaluation 2 0) =
      inner20 := by
  rw [verticalPartialTwo_20]
  funext jet
  rw [totalDerivative_realCovector partial02
    (partial02Derivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) 0 jet
    (partial02_hasFDerivAt
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  apply ContinuousLinearMap.ext
  intro variation
  simp [partial02Derivative, inner20, realCovector]
  exact Or.inl (by ring)

private theorem firstTotal21 :
    programPT06ThroatSpatialLocalFunctionTotalDerivative 1
        (programPT06SecondOrderLocalVerticalPartialTwo
          programPT06ScalarHessianDeterminantDensityEvaluation 2 1) =
      inner21 := by
  rw [verticalPartialTwo_21]
  funext jet
  rw [totalDerivative_realCovector partial12
    (partial12Derivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) 1 jet
    (partial12_hasFDerivAt
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  apply ContinuousLinearMap.ext
  intro variation
  simp [partial12Derivative, inner21, realCovector]
  exact Or.inl (by ring)

private theorem firstTotal22 :
    programPT06ThroatSpatialLocalFunctionTotalDerivative 2
        (programPT06SecondOrderLocalVerticalPartialTwo
          programPT06ScalarHessianDeterminantDensityEvaluation 2 2) =
      inner22 := by
  rw [verticalPartialTwo_22]
  funext jet
  rw [totalDerivative_realCovector partial22
    (partial22Derivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) 2 jet
    (partial22_hasFDerivAt
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  apply ContinuousLinearMap.ext
  intro variation
  simp [partial22Derivative, inner22, realCovector]
  exact Or.inl (by ring)

private theorem inner00_differentiable : Differentiable Real inner00 := by
  unfold inner00 realCovector
  fun_prop

private theorem inner01_differentiable : Differentiable Real inner01 := by
  unfold inner01 realCovector
  fun_prop

private theorem inner02_differentiable : Differentiable Real inner02 := by
  unfold inner02 realCovector
  fun_prop

private theorem inner10_differentiable : Differentiable Real inner10 := by
  unfold inner10 realCovector
  fun_prop

private theorem inner11_differentiable : Differentiable Real inner11 := by
  unfold inner11 realCovector
  fun_prop

private theorem inner12_differentiable : Differentiable Real inner12 := by
  unfold inner12 realCovector
  fun_prop

private theorem inner20_differentiable : Differentiable Real inner20 := by
  unfold inner20 realCovector
  fun_prop

private theorem inner21_differentiable : Differentiable Real inner21 := by
  unfold inner21 realCovector
  fun_prop

private theorem inner22_differentiable : Differentiable Real inner22 := by
  unfold inner22 realCovector
  fun_prop

private theorem piolaRow0 (jet : ThirdJet) :
    inner00 jet + (1 / 2 : Real) • inner01 jet +
      (1 / 2 : Real) • inner02 jet = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  simp [inner00, inner01, inner02, realCovector]
  ring

private theorem piolaRow1 (jet : ThirdJet) :
    (1 / 2 : Real) • inner10 jet + inner11 jet +
      (1 / 2 : Real) • inner12 jet = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  simp [inner10, inner11, inner12, realCovector]
  ring

private theorem piolaRow2 (jet : ThirdJet) :
    (1 / 2 : Real) • inner20 jet +
      (1 / 2 : Real) • inner21 jet + inner22 jet = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  simp [inner20, inner21, inner22, realCovector]
  ring

private theorem weightedTotalDerivative_three_eq_zero
    (a b c : Real) (first second third : ThirdJet → RealCovector)
    (hFirst : Differentiable Real first)
    (hSecond : Differentiable Real second)
    (hThird : Differentiable Real third)
    (hZero : ∀ jet, a • first jet + b • second jet + c • third jet = 0)
    (direction : Fin 3) (jet : FourthJet) :
    a • programPT06ThroatSpatialLocalFunctionTotalDerivative direction first jet +
        b • programPT06ThroatSpatialLocalFunctionTotalDerivative direction second jet +
        c • programPT06ThroatSpatialLocalFunctionTotalDerivative direction third jet =
      0 := by
  let base : ThirdJet :=
    truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet
  have hWeighted :=
    ((((hFirst base).hasFDerivAt.const_smul a).add
      ((hSecond base).hasFDerivAt.const_smul b)).add
      ((hThird base).hasFDerivAt.const_smul c))
  have hFunction :
      a • first + b • second + c • third =
        (0 : ThirdJet → RealCovector) := by
    funext candidate
    exact hZero candidate
  rw [hFunction] at hWeighted
  have hUnique := hWeighted.unique
    (hasFDerivAt_const (x := base) (c := (0 : RealCovector)))
  have hApply := congrArg
    (fun derivative : ThirdJet →L[Real] RealCovector =>
      derivative (throatSpatialTotalDerivative direction jet)) hUnique
  change
    a • fderiv Real first base
          (throatSpatialTotalDerivative direction jet) +
        b • fderiv Real second base
          (throatSpatialTotalDerivative direction jet) +
        c • fderiv Real third base
          (throatSpatialTotalDerivative direction jet) = 0
  simpa only [add_apply, smul_apply, zero_apply] using hApply

private theorem secondEulerRow0 (jet : FourthJet) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
          programPT06ScalarHessianDeterminantDensityEvaluation 0 0 jet +
        (1 / 2 : Real) •
          programPT06SecondOrderLocalEulerSecondTotalTerm
            programPT06ScalarHessianDeterminantDensityEvaluation 0 1 jet +
        (1 / 2 : Real) •
          programPT06SecondOrderLocalEulerSecondTotalTerm
            programPT06ScalarHessianDeterminantDensityEvaluation 0 2 jet =
      0 := by
  simp only [programPT06SecondOrderLocalEulerSecondTotalTerm]
  rw [firstTotal00, firstTotal01, firstTotal02]
  simpa using weightedTotalDerivative_three_eq_zero
    1 (1 / 2) (1 / 2) inner00 inner01 inner02
    inner00_differentiable inner01_differentiable inner02_differentiable
    (fun thirdJet => by simpa using piolaRow0 thirdJet) 0 jet

private theorem secondEulerRow1 (jet : FourthJet) :
    (1 / 2 : Real) •
          programPT06SecondOrderLocalEulerSecondTotalTerm
            programPT06ScalarHessianDeterminantDensityEvaluation 1 0 jet +
        programPT06SecondOrderLocalEulerSecondTotalTerm
          programPT06ScalarHessianDeterminantDensityEvaluation 1 1 jet +
        (1 / 2 : Real) •
          programPT06SecondOrderLocalEulerSecondTotalTerm
            programPT06ScalarHessianDeterminantDensityEvaluation 1 2 jet =
      0 := by
  simp only [programPT06SecondOrderLocalEulerSecondTotalTerm]
  rw [firstTotal10, firstTotal11, firstTotal12]
  simpa using weightedTotalDerivative_three_eq_zero
    (1 / 2) 1 (1 / 2) inner10 inner11 inner12
    inner10_differentiable inner11_differentiable inner12_differentiable
    (fun thirdJet => by simpa using piolaRow1 thirdJet) 1 jet

private theorem secondEulerRow2 (jet : FourthJet) :
    (1 / 2 : Real) •
          programPT06SecondOrderLocalEulerSecondTotalTerm
            programPT06ScalarHessianDeterminantDensityEvaluation 2 0 jet +
        (1 / 2 : Real) •
          programPT06SecondOrderLocalEulerSecondTotalTerm
            programPT06ScalarHessianDeterminantDensityEvaluation 2 1 jet +
        programPT06SecondOrderLocalEulerSecondTotalTerm
          programPT06ScalarHessianDeterminantDensityEvaluation 2 2 jet =
      0 := by
  simp only [programPT06SecondOrderLocalEulerSecondTotalTerm]
  rw [firstTotal20, firstTotal21, firstTotal22]
  simpa using weightedTotalDerivative_three_eq_zero
    (1 / 2) (1 / 2) 1 inner20 inner21 inner22
    inner20_differentiable inner21_differentiable inner22_differentiable
    (fun thirdJet => by simpa using piolaRow2 thirdJet) 2 jet

private theorem secondEulerSum_apply
    (jet : FourthJet) (variation : Real) :
    (∑ first : Fin 3, ∑ second : Fin 3,
      programPT06SecondOrderEulerSymmetryWeight first second •
        programPT06SecondOrderLocalEulerSecondTotalTerm
          programPT06ScalarHessianDeterminantDensityEvaluation
          first second jet variation) = 0 := by
  calc
    _ =
        (programPT06SecondOrderLocalEulerSecondTotalTerm
              programPT06ScalarHessianDeterminantDensityEvaluation 0 0 jet +
            (1 / 2 : Real) •
              programPT06SecondOrderLocalEulerSecondTotalTerm
                programPT06ScalarHessianDeterminantDensityEvaluation 0 1 jet +
            (1 / 2 : Real) •
              programPT06SecondOrderLocalEulerSecondTotalTerm
                programPT06ScalarHessianDeterminantDensityEvaluation 0 2 jet)
            variation +
          ((1 / 2 : Real) •
              programPT06SecondOrderLocalEulerSecondTotalTerm
                programPT06ScalarHessianDeterminantDensityEvaluation 1 0 jet +
            programPT06SecondOrderLocalEulerSecondTotalTerm
              programPT06ScalarHessianDeterminantDensityEvaluation 1 1 jet +
            (1 / 2 : Real) •
              programPT06SecondOrderLocalEulerSecondTotalTerm
                programPT06ScalarHessianDeterminantDensityEvaluation 1 2 jet)
            variation +
          ((1 / 2 : Real) •
              programPT06SecondOrderLocalEulerSecondTotalTerm
                programPT06ScalarHessianDeterminantDensityEvaluation 2 0 jet +
            (1 / 2 : Real) •
              programPT06SecondOrderLocalEulerSecondTotalTerm
                programPT06ScalarHessianDeterminantDensityEvaluation 2 1 jet +
            programPT06SecondOrderLocalEulerSecondTotalTerm
              programPT06ScalarHessianDeterminantDensityEvaluation 2 2 jet)
            variation := by
      simp [Fin.sum_univ_three,
        programPT06SecondOrderEulerSymmetryWeight]
    _ = 0 := by
      rw [secondEulerRow0 jet, secondEulerRow1 jet, secondEulerRow2 jet]
      simp

/-- Gate880 directly annihilates the scalar three-direction Hessian
determinant. -/
theorem programPT06SecondOrderLocalEuler_scalarHessianDeterminant_eq_zero
    (jet : FourthJet) :
    programPT06SecondOrderLocalEuler
        programPT06ScalarHessianDeterminantDensityEvaluation jet = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  rw [programPT06SecondOrderLocalEuler_apply,
    programPT06ScalarHessianDeterminantVerticalPartialZero]
  have hFirst :
      (∑ direction : Fin 3,
        programPT06SecondOrderLocalEulerFirstTotalTerm
          programPT06ScalarHessianDeterminantDensityEvaluation direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)
          variation) = 0 := by
    apply Finset.sum_eq_zero
    intro direction _
    rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
      programPT06ScalarHessianDeterminantVerticalPartialOne]
    simp
  rw [hFirst, secondEulerSum_apply jet variation]
  simp

/-- Direction-zero component `u_0 C_00` of the first-row cofactor current. -/
def programPT06ScalarHessianDeterminantCurrentZeroComponent :
    SecondJet → Real :=
  fun jet => secondOrderFirstProjection 0 jet * cofactor00 jet

/-- Direction-one component `u_0 C_01` of the first-row cofactor current. -/
def programPT06ScalarHessianDeterminantCurrentOneComponent :
    SecondJet → Real :=
  fun jet => secondOrderFirstProjection 0 jet * cofactor01 jet

/-- Direction-two component `u_0 C_02` of the first-row cofactor current. -/
def programPT06ScalarHessianDeterminantCurrentTwoComponent :
    SecondJet → Real :=
  fun jet => secondOrderFirstProjection 0 jet * cofactor02 jet

/-- Genuine Gate879 horizontal differential of the explicit cofactor current. -/
def programPT06ScalarHessianDeterminantCurrentDH : ThirdJet → Real :=
  fun jet =>
    programPT06ThroatSpatialLocalFunctionTotalDerivative 0
        programPT06ScalarHessianDeterminantCurrentZeroComponent jet +
      programPT06ThroatSpatialLocalFunctionTotalDerivative 1
        programPT06ScalarHessianDeterminantCurrentOneComponent jet +
      programPT06ThroatSpatialLocalFunctionTotalDerivative 2
        programPT06ScalarHessianDeterminantCurrentTwoComponent jet

private def currentZeroDerivative (jet : SecondJet) :
    SecondJet →L[Real] Real :=
  cofactor00 jet • secondOrderFirstProjection 0 +
    secondOrderFirstProjection 0 jet • partial00Derivative jet

private def cofactor01Derivative (jet : SecondJet) :
    SecondJet →L[Real] Real :=
  secondOrderSecondProjection 1 2 jet • secondOrderSecondProjection 0 2 +
    secondOrderSecondProjection 0 2 jet • secondOrderSecondProjection 1 2 -
    (secondOrderSecondProjection 2 2 jet • secondOrderSecondProjection 0 1 +
      secondOrderSecondProjection 0 1 jet • secondOrderSecondProjection 2 2)

private def currentOneDerivative (jet : SecondJet) :
    SecondJet →L[Real] Real :=
  cofactor01 jet • secondOrderFirstProjection 0 +
    secondOrderFirstProjection 0 jet • cofactor01Derivative jet

private def cofactor02Derivative (jet : SecondJet) :
    SecondJet →L[Real] Real :=
  secondOrderSecondProjection 1 2 jet • secondOrderSecondProjection 0 1 +
    secondOrderSecondProjection 0 1 jet • secondOrderSecondProjection 1 2 -
    (secondOrderSecondProjection 1 1 jet • secondOrderSecondProjection 0 2 +
      secondOrderSecondProjection 0 2 jet • secondOrderSecondProjection 1 1)

private def currentTwoDerivative (jet : SecondJet) :
    SecondJet →L[Real] Real :=
  cofactor02 jet • secondOrderFirstProjection 0 +
    secondOrderFirstProjection 0 jet • cofactor02Derivative jet

private theorem currentZero_hasFDerivAt (jet : SecondJet) :
    HasFDerivAt programPT06ScalarHessianDeterminantCurrentZeroComponent
      (currentZeroDerivative jet) jet := by
  have hFirst := (secondOrderFirstProjection 0).hasFDerivAt (x := jet)
  have hCofactor := partial00_hasFDerivAt jet
  have hRaw := hFirst.mul hCofactor
  change HasFDerivAt
    (fun candidate : SecondJet =>
      secondOrderFirstProjection 0 candidate * cofactor00 candidate)
    (currentZeroDerivative jet) jet
  apply hRaw.congr_fderiv
  ext variation
  simp [currentZeroDerivative, partial00Derivative, partial00]
  ring

private theorem currentOne_hasFDerivAt (jet : SecondJet) :
    HasFDerivAt programPT06ScalarHessianDeterminantCurrentOneComponent
      (currentOneDerivative jet) jet := by
  have hFirst := (secondOrderFirstProjection 0).hasFDerivAt (x := jet)
  have h01 := (secondOrderSecondProjection 0 1).hasFDerivAt (x := jet)
  have h02 := (secondOrderSecondProjection 0 2).hasFDerivAt (x := jet)
  have h12 := (secondOrderSecondProjection 1 2).hasFDerivAt (x := jet)
  have h22 := (secondOrderSecondProjection 2 2).hasFDerivAt (x := jet)
  have hCofactor := (h02.mul h12).sub (h01.mul h22)
  have hRaw := hFirst.mul hCofactor
  change HasFDerivAt
    (fun candidate : SecondJet =>
      secondOrderFirstProjection 0 candidate * cofactor01 candidate)
    (currentOneDerivative jet) jet
  apply hRaw.congr_fderiv
  ext variation
  simp [currentOneDerivative, cofactor01Derivative, cofactor01]
  ring

private theorem currentTwo_hasFDerivAt (jet : SecondJet) :
    HasFDerivAt programPT06ScalarHessianDeterminantCurrentTwoComponent
      (currentTwoDerivative jet) jet := by
  have hFirst := (secondOrderFirstProjection 0).hasFDerivAt (x := jet)
  have h01 := (secondOrderSecondProjection 0 1).hasFDerivAt (x := jet)
  have h02 := (secondOrderSecondProjection 0 2).hasFDerivAt (x := jet)
  have h11 := (secondOrderSecondProjection 1 1).hasFDerivAt (x := jet)
  have h12 := (secondOrderSecondProjection 1 2).hasFDerivAt (x := jet)
  have hCofactor := (h01.mul h12).sub (h02.mul h11)
  have hRaw := hFirst.mul hCofactor
  change HasFDerivAt
    (fun candidate : SecondJet =>
      secondOrderFirstProjection 0 candidate * cofactor02 candidate)
    (currentTwoDerivative jet) jet
  apply hRaw.congr_fderiv
  ext variation
  simp [currentTwoDerivative, cofactor02Derivative, cofactor02]
  ring

private theorem currentZero_totalDerivative (jet : ThirdJet) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative 0
        programPT06ScalarHessianDeterminantCurrentZeroComponent jet =
      jet (thirdOrderSecondMultiIndex 0 0) *
          (jet (thirdOrderSecondMultiIndex 1 1) *
              jet (thirdOrderSecondMultiIndex 2 2) -
            jet (thirdOrderSecondMultiIndex 1 2) ^ 2) +
        jet (thirdOrderFirstMultiIndex 0) *
          (jet (thirdOrderThirdMultiIndex 0 1 1) *
                jet (thirdOrderSecondMultiIndex 2 2) +
            jet (thirdOrderSecondMultiIndex 1 1) *
                jet (thirdOrderThirdMultiIndex 0 2 2) -
            2 * jet (thirdOrderSecondMultiIndex 1 2) *
                jet (thirdOrderThirdMultiIndex 0 1 2)) := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    0 _ jet
    (currentZeroDerivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))
    (currentZero_hasFDerivAt
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  simp [currentZeroDerivative, partial00Derivative, cofactor00]
  ring

private theorem currentOne_totalDerivative (jet : ThirdJet) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative 1
        programPT06ScalarHessianDeterminantCurrentOneComponent jet =
      jet (thirdOrderSecondMultiIndex 0 1) *
          (jet (thirdOrderSecondMultiIndex 0 2) *
              jet (thirdOrderSecondMultiIndex 1 2) -
            jet (thirdOrderSecondMultiIndex 0 1) *
              jet (thirdOrderSecondMultiIndex 2 2)) +
        jet (thirdOrderFirstMultiIndex 0) *
          (jet (thirdOrderThirdMultiIndex 0 1 2) *
                jet (thirdOrderSecondMultiIndex 1 2) +
            jet (thirdOrderSecondMultiIndex 0 2) *
                jet (thirdOrderThirdMultiIndex 1 1 2) -
            jet (thirdOrderThirdMultiIndex 0 1 1) *
                jet (thirdOrderSecondMultiIndex 2 2) -
            jet (thirdOrderSecondMultiIndex 0 1) *
                jet (thirdOrderThirdMultiIndex 1 2 2)) := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    1 _ jet
    (currentOneDerivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))
    (currentOne_hasFDerivAt
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  simp [currentOneDerivative, cofactor01Derivative, cofactor01]
  ring

private theorem currentTwo_totalDerivative (jet : ThirdJet) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative 2
        programPT06ScalarHessianDeterminantCurrentTwoComponent jet =
      jet (thirdOrderSecondMultiIndex 0 2) *
          (jet (thirdOrderSecondMultiIndex 0 1) *
              jet (thirdOrderSecondMultiIndex 1 2) -
            jet (thirdOrderSecondMultiIndex 0 2) *
              jet (thirdOrderSecondMultiIndex 1 1)) +
        jet (thirdOrderFirstMultiIndex 0) *
          (jet (thirdOrderThirdMultiIndex 0 1 2) *
                jet (thirdOrderSecondMultiIndex 1 2) +
            jet (thirdOrderSecondMultiIndex 0 1) *
                jet (thirdOrderThirdMultiIndex 1 2 2) -
            jet (thirdOrderThirdMultiIndex 0 2 2) *
                jet (thirdOrderSecondMultiIndex 1 1) -
            jet (thirdOrderSecondMultiIndex 0 2) *
                jet (thirdOrderThirdMultiIndex 1 1 2)) := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    2 _ jet
    (currentTwoDerivative
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))
    (currentTwo_hasFDerivAt
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  simp [currentTwoDerivative, cofactor02Derivative, cofactor02]
  ring

/-- All order-three terms in the first-row cofactor current cancel, and its
Gate879 horizontal differential is exactly the pulled-back determinant. -/
theorem programPT06ScalarHessianDeterminantCurrentDH_eq_density
    (jet : ThirdJet) :
    programPT06ScalarHessianDeterminantCurrentDH jet =
      programPT06ScalarHessianDeterminantDensityEvaluation
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) := by
  rw [programPT06ScalarHessianDeterminantCurrentDH,
    currentZero_totalDerivative, currentOne_totalDerivative,
    currentTwo_totalDerivative]
  simp [programPT06ScalarHessianDeterminantDensityEvaluation]
  ring

end
end P0EFTJanusProgramPT06ScalarHessianDeterminantNullLagrangian4D
end JanusFormal
