import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderHorizontalDivergenceEulerSoundness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06FullHorizontalDivergenceMultiindexEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderMultiindexEulerComparison4D

/-!
# Second-order horizontal-divergence Euler soundness

The order-four horizontal-divergence telescope descends to the specialized
second-order Euler operator.  Thus a second-order density represented on
fourth jets by a smooth third-jet current has vanishing Gate880 Euler
expression.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06SecondOrderHorizontalDivergenceEulerClosure4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06SecondOrderEulerHigherFrechetFormula4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
open P0EFTJanusProgramPT06SecondOrderHorizontalDivergenceEulerSoundness4D
open P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D
open P0EFTJanusProgramPT06MultiindexLocalEulerLinearity4D
open P0EFTJanusProgramPT06AmbientMultiindexTotalDerivativeCommutation4D
open P0EFTJanusProgramPT06AmbientLocalFunctionLiftNaturality4D
open P0EFTJanusProgramPT06FullHorizontalDivergenceMultiindexEuler4D
open P0EFTJanusProgramPT06SecondOrderMultiindexEulerComparison4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev SpatialJet (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

private abbrev AmbientCovector := Fiber →L[Real] Real

private def programPT06SecondOrderDensityFourthLift
    (density : SpatialJet (Fiber := Fiber) 2 → Real) :
    SpatialJet (Fiber := Fiber) 4 → Real :=
  programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4) density

private def programPT06SecondOrderDensityVerticalPartial
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (index : ThroatSpatialTruncatedIndex 2) :
    SpatialJet (Fiber := Fiber) 2 → AmbientCovector (Fiber := Fiber) :=
  fun jet ↦
    programPT06ThroatSpatialVerticalPartialDerivative density jet index

private theorem programPT06SecondOrderDensityVerticalPartial_contDiff
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (hDensity : ContDiff Real ∞ density)
    (index : ThroatSpatialTruncatedIndex 2) :
    ContDiff Real ∞
      (programPT06SecondOrderDensityVerticalPartial density index) := by
  exact programPT06ThroatSpatialVerticalPartialDerivative_contDiff_top
    density hDensity index

private theorem programPT06SecondOrderDensityFourthDoubleLift
    (density : SpatialJet (Fiber := Fiber) 2 → Real) :
    programPT06LocalDensityDoubleOrderLift 4
        (programPT06SecondOrderDensityFourthLift density) =
      programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8) density := by
  funext jet
  simp [programPT06LocalDensityDoubleOrderLift,
    programPT06SecondOrderDensityFourthLift,
    programPT06AmbientLocalFunctionLift, Function.comp_def,
    programPT06TruncateThroatSpatialMultiindexJet_trans]

private theorem programPT06SecondOrderEulerTwoVerticalPartial_eq_lift
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (hDensity : Differentiable Real density)
    (index : ThroatSpatialTruncatedIndex 2) :
    programPT06MultiindexLocalVerticalPartial 2 density index =
      programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
        (programPT06SecondOrderDensityVerticalPartial density index) := by
  funext jet
  change
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4) density)
        jet (programPT06TruncatedIndexOfLE (by omega : 2 ≤ 4) index) =
      programPT06ThroatSpatialVerticalPartialDerivative density
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) index
  exact programPT06AmbientLocalFunctionLift_verticalPartial_ofLE
    (by omega : 2 ≤ 4) density hDensity jet index

private theorem programPT06SecondOrderEulerFourVerticalPartial_eq_lift
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (hDensity : Differentiable Real density)
    (index : ThroatSpatialTruncatedIndex 2) :
    programPT06MultiindexLocalVerticalPartial 4
        (programPT06SecondOrderDensityFourthLift density)
        (programPT06TruncatedIndexOfLE (by omega : 2 ≤ 4) index) =
      programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8)
        (programPT06SecondOrderDensityVerticalPartial density index) := by
  funext jet
  change
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06LocalDensityDoubleOrderLift 4
          (programPT06SecondOrderDensityFourthLift density)) jet
        (programPT06TruncatedIndexOfLE (by omega : 4 ≤ 8)
          (programPT06TruncatedIndexOfLE (by omega : 2 ≤ 4) index)) = _
  rw [show programPT06LocalDensityDoubleOrderLift 4
      (programPT06SecondOrderDensityFourthLift density) =
        programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8) density from
    programPT06SecondOrderDensityFourthDoubleLift density]
  exact programPT06AmbientLocalFunctionLift_verticalPartial_ofLE
    (by omega : 2 ≤ 8) density hDensity jet index

private theorem programPT06SecondOrderEulerFourVerticalPartial_eq_zero
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (hDensity : Differentiable Real density)
    (index : ThroatSpatialTruncatedIndex 4)
    (hIndex : 2 < throatSpatialMultiIndexOrder index.1) :
    programPT06MultiindexLocalVerticalPartial 4
        (programPT06SecondOrderDensityFourthLift density) index = 0 := by
  funext jet
  change
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06LocalDensityDoubleOrderLift 4
          (programPT06SecondOrderDensityFourthLift density)) jet
        (programPT06TruncatedIndexOfLE (by omega : 4 ≤ 8) index) = 0
  rw [show programPT06LocalDensityDoubleOrderLift 4
      (programPT06SecondOrderDensityFourthLift density) =
        programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8) density from
    programPT06SecondOrderDensityFourthDoubleLift density]
  exact programPT06AmbientLocalFunctionLift_verticalPartial_eq_zero
    (by omega : 2 ≤ 8) density hDensity jet
    (programPT06TruncatedIndexOfLE (by omega : 4 ≤ 8) index)
    (by
      simpa only [programPT06TruncatedIndexOfLE_value] using hIndex)

private theorem programPT06SecondOrderFirstMultiindexDerivative_lift
    (localFunction : SpatialJet (Fiber := Fiber) 2 →
      AmbientCovector (Fiber := Fiber))
    (hLocalFunction : ContDiff Real ∞ localFunction)
    (direction : Fin 3) (jet : SpatialJet (Fiber := Fiber) 8) :
    programPT06AmbientMultiindexTotalDerivative 8
        (programPT06SecondOrderFirstMultiIndex direction).1
        (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8)
          localFunction) jet =
      programPT06AmbientMultiindexTotalDerivative 4
        (programPT06SecondOrderFirstMultiIndex direction).1
        (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
          localFunction)
        (truncateThroatSpatialMultiindexJet (by omega : 4 ≤ 8) jet) := by
  have hLiftEight : ContDiff Real ∞
      (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8)
        localFunction) :=
    programPT06AmbientLocalFunctionLift_contDiff
      (by omega : 2 ≤ 8) localFunction hLocalFunction
  have hLiftFour : ContDiff Real ∞
      (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
        localFunction) :=
    programPT06AmbientLocalFunctionLift_contDiff
      (by omega : 2 ≤ 4) localFunction hLocalFunction
  have hEight :
      programPT06AmbientMultiindexTotalDerivative 8
          (programPT06SecondOrderFirstMultiIndex direction).1
          (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8)
            localFunction) =
        programPT06AmbientLocalFunctionTotalDerivative 8 direction
          (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8)
            localFunction) := by
    change
      programPT06AmbientMultiindexTotalDerivative 8
          (throatSpatialCoordinateMultiIndex direction) _ = _
    rw [show throatSpatialCoordinateMultiIndex direction =
        0 + throatSpatialCoordinateMultiIndex direction by simp]
    rw [programPT06AmbientMultiindexTotalDerivative_add_coordinate
      8 0 direction _ hLiftEight]
    rw [programPT06AmbientMultiindexTotalDerivative_zero_index]
  have hFour :
      programPT06AmbientMultiindexTotalDerivative 4
          (programPT06SecondOrderFirstMultiIndex direction).1
          (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
            localFunction) =
        programPT06AmbientLocalFunctionTotalDerivative 4 direction
          (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
            localFunction) := by
    change
      programPT06AmbientMultiindexTotalDerivative 4
          (throatSpatialCoordinateMultiIndex direction) _ = _
    rw [show throatSpatialCoordinateMultiIndex direction =
        0 + throatSpatialCoordinateMultiIndex direction by simp]
    rw [programPT06AmbientMultiindexTotalDerivative_add_coordinate
      4 0 direction _ hLiftFour]
    rw [programPT06AmbientMultiindexTotalDerivative_zero_index]
  rw [hEight, hFour]
  rw [programPT06AmbientLocalFunctionLift_totalDerivative
      (by omega : 2 + 1 ≤ 8) direction localFunction
      (hLocalFunction.differentiable (by simp)),
    programPT06AmbientLocalFunctionLift_totalDerivative
      (by omega : 2 + 1 ≤ 4) direction localFunction
      (hLocalFunction.differentiable (by simp))]
  simp [programPT06AmbientLocalFunctionLift,
    programPT06TruncateThroatSpatialMultiindexJet_trans]

private theorem programPT06SecondOrderSecondMultiindexDerivative_lift
    (localFunction : SpatialJet (Fiber := Fiber) 2 →
      AmbientCovector (Fiber := Fiber))
    (hLocalFunction : ContDiff Real ∞ localFunction)
    (first second : Fin 3) (jet : SpatialJet (Fiber := Fiber) 8) :
    programPT06AmbientMultiindexTotalDerivative 8
        (programPT06SecondOrderSecondMultiIndex first second).1
        (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8)
          localFunction) jet =
      programPT06AmbientMultiindexTotalDerivative 4
        (programPT06SecondOrderSecondMultiIndex first second).1
        (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
          localFunction)
        (truncateThroatSpatialMultiindexJet (by omega : 4 ≤ 8) jet) := by
  have hLiftEight : ContDiff Real ∞
      (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8)
        localFunction) :=
    programPT06AmbientLocalFunctionLift_contDiff
      (by omega : 2 ≤ 8) localFunction hLocalFunction
  have hLiftFour : ContDiff Real ∞
      (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
        localFunction) :=
    programPT06AmbientLocalFunctionLift_contDiff
      (by omega : 2 ≤ 4) localFunction hLocalFunction
  have hSecondEight : ContDiff Real ∞
      (programPT06AmbientLocalFunctionTotalDerivative 8 second
        (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8)
          localFunction)) :=
    programPT06AmbientLocalFunctionTotalDerivative_contDiff
      8 second _ hLiftEight
  have hSecondFour : ContDiff Real ∞
      (programPT06AmbientLocalFunctionTotalDerivative 4 second
        (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
          localFunction)) :=
    programPT06AmbientLocalFunctionTotalDerivative_contDiff
      4 second _ hLiftFour
  have hEight :
      programPT06AmbientMultiindexTotalDerivative 8
          (programPT06SecondOrderSecondMultiIndex first second).1
          (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8)
            localFunction) =
        programPT06AmbientLocalFunctionTotalDerivative 8 first
          (programPT06AmbientLocalFunctionTotalDerivative 8 second
            (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 8)
              localFunction)) := by
    change
      programPT06AmbientMultiindexTotalDerivative 8
          (throatSpatialCoordinateMultiIndex first +
            throatSpatialCoordinateMultiIndex second) _ = _
    rw [programPT06AmbientMultiindexTotalDerivative_add_coordinate
      8 (throatSpatialCoordinateMultiIndex first) second _ hLiftEight]
    rw [show throatSpatialCoordinateMultiIndex first =
        0 + throatSpatialCoordinateMultiIndex first by simp]
    rw [programPT06AmbientMultiindexTotalDerivative_add_coordinate
      8 0 first _ hSecondEight]
    rw [programPT06AmbientMultiindexTotalDerivative_zero_index]
  have hFour :
      programPT06AmbientMultiindexTotalDerivative 4
          (programPT06SecondOrderSecondMultiIndex first second).1
          (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
            localFunction) =
        programPT06AmbientLocalFunctionTotalDerivative 4 first
          (programPT06AmbientLocalFunctionTotalDerivative 4 second
            (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
              localFunction)) := by
    change
      programPT06AmbientMultiindexTotalDerivative 4
          (throatSpatialCoordinateMultiIndex first +
            throatSpatialCoordinateMultiIndex second) _ = _
    rw [programPT06AmbientMultiindexTotalDerivative_add_coordinate
      4 (throatSpatialCoordinateMultiIndex first) second _ hLiftFour]
    rw [show throatSpatialCoordinateMultiIndex first =
        0 + throatSpatialCoordinateMultiIndex first by simp]
    rw [programPT06AmbientMultiindexTotalDerivative_add_coordinate
      4 0 first _ hSecondFour]
    rw [programPT06AmbientMultiindexTotalDerivative_zero_index]
  rw [hEight, hFour]
  rw [programPT06AmbientLocalFunctionLift_totalDerivative
      (by omega : 2 + 1 ≤ 8) second localFunction
      (hLocalFunction.differentiable (by simp)),
    programPT06AmbientLocalFunctionLift_totalDerivative
      (by omega : 2 + 1 ≤ 4) second localFunction
      (hLocalFunction.differentiable (by simp))]
  have hFirstTotal : ContDiff Real ∞
      (programPT06ThroatSpatialLocalFunctionTotalDerivative
        second localFunction) :=
    programPT06ThroatSpatialLocalFunctionTotalDerivative_contDiff_top
      localFunction hLocalFunction second
  rw [programPT06AmbientLocalFunctionLift_totalDerivative
      (by omega : 3 + 1 ≤ 8) first
      (programPT06ThroatSpatialLocalFunctionTotalDerivative
        second localFunction)
      (hFirstTotal.differentiable (by simp)),
    programPT06AmbientLocalFunctionLift_totalDerivative
      (by omega : 3 + 1 ≤ 4) first
      (programPT06ThroatSpatialLocalFunctionTotalDerivative
        second localFunction)
      (hFirstTotal.differentiable (by simp))]
  simp [programPT06AmbientLocalFunctionLift,
    programPT06TruncateThroatSpatialMultiindexJet_trans]

private def programPT06SecondOrderEulerFourLiftSummand
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (jet : SpatialJet (Fiber := Fiber) 8)
    (index : ThroatSpatialTruncatedIndex 4) :
    AmbientCovector (Fiber := Fiber) :=
  ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
    programPT06AmbientMultiindexTotalDerivative 8 index.1
      (programPT06MultiindexLocalVerticalPartial 4
        (programPT06SecondOrderDensityFourthLift density) index) jet

private def programPT06SecondOrderEulerTwoSummand
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (jet : SpatialJet (Fiber := Fiber) 4)
    (index : ThroatSpatialTruncatedIndex 2) :
    AmbientCovector (Fiber := Fiber) :=
  ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
    programPT06AmbientMultiindexTotalDerivative 4 index.1
      (programPT06MultiindexLocalVerticalPartial 2 density index) jet

private def programPT06SecondOrderIndexEmbedding
    (index : ThroatSpatialTruncatedIndex 2) :
    ThroatSpatialTruncatedIndex 4 :=
  programPT06TruncatedIndexOfLE (by omega : 2 ≤ 4) index

private theorem programPT06SecondOrderEulerLiftSummand_zero
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (hDensity : ContDiff Real ∞ density)
    (jet : SpatialJet (Fiber := Fiber) 8) :
    programPT06SecondOrderEulerFourLiftSummand density jet
        (programPT06SecondOrderIndexEmbedding
          programPT06SecondOrderZeroMultiIndex) =
      programPT06SecondOrderEulerTwoSummand density
        (truncateThroatSpatialMultiindexJet (by omega : 4 ≤ 8) jet)
        programPT06SecondOrderZeroMultiIndex := by
  rw [programPT06SecondOrderEulerFourLiftSummand,
    programPT06SecondOrderEulerTwoSummand,
    programPT06SecondOrderIndexEmbedding,
    programPT06SecondOrderEulerFourVerticalPartial_eq_lift
      density (hDensity.differentiable (by simp)),
    programPT06SecondOrderEulerTwoVerticalPartial_eq_lift
      density (hDensity.differentiable (by simp))]
  simp [programPT06SecondOrderZeroMultiIndex,
    programPT06AmbientLocalFunctionLift,
    programPT06TruncateThroatSpatialMultiindexJet_trans]

private theorem programPT06SecondOrderEulerLiftSummand_one
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (hDensity : ContDiff Real ∞ density)
    (direction : Fin 3) (jet : SpatialJet (Fiber := Fiber) 8) :
    programPT06SecondOrderEulerFourLiftSummand density jet
        (programPT06SecondOrderIndexEmbedding
          (programPT06SecondOrderFirstMultiIndex direction)) =
      programPT06SecondOrderEulerTwoSummand density
        (truncateThroatSpatialMultiindexJet (by omega : 4 ≤ 8) jet)
        (programPT06SecondOrderFirstMultiIndex direction) := by
  rw [programPT06SecondOrderEulerFourLiftSummand,
    programPT06SecondOrderEulerTwoSummand,
    programPT06SecondOrderIndexEmbedding,
    programPT06SecondOrderEulerFourVerticalPartial_eq_lift
      density (hDensity.differentiable (by simp)),
    programPT06SecondOrderEulerTwoVerticalPartial_eq_lift
      density (hDensity.differentiable (by simp))]
  simp only [programPT06TruncatedIndexOfLE_value]
  rw [programPT06SecondOrderFirstMultiindexDerivative_lift
    (programPT06SecondOrderDensityVerticalPartial density
      (programPT06SecondOrderFirstMultiIndex direction))
    (programPT06SecondOrderDensityVerticalPartial_contDiff
      density hDensity (programPT06SecondOrderFirstMultiIndex direction))]

private theorem programPT06SecondOrderEulerLiftSummand_two
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (hDensity : ContDiff Real ∞ density)
    (first second : Fin 3) (jet : SpatialJet (Fiber := Fiber) 8) :
    programPT06SecondOrderEulerFourLiftSummand density jet
        (programPT06SecondOrderIndexEmbedding
          (programPT06SecondOrderSecondMultiIndex first second)) =
      programPT06SecondOrderEulerTwoSummand density
        (truncateThroatSpatialMultiindexJet (by omega : 4 ≤ 8) jet)
        (programPT06SecondOrderSecondMultiIndex first second) := by
  rw [programPT06SecondOrderEulerFourLiftSummand,
    programPT06SecondOrderEulerTwoSummand,
    programPT06SecondOrderIndexEmbedding,
    programPT06SecondOrderEulerFourVerticalPartial_eq_lift
      density (hDensity.differentiable (by simp)),
    programPT06SecondOrderEulerTwoVerticalPartial_eq_lift
      density (hDensity.differentiable (by simp))]
  simp only [programPT06TruncatedIndexOfLE_value]
  rw [programPT06SecondOrderSecondMultiindexDerivative_lift
    (programPT06SecondOrderDensityVerticalPartial density
      (programPT06SecondOrderSecondMultiIndex first second))
    (programPT06SecondOrderDensityVerticalPartial_contDiff density hDensity
      (programPT06SecondOrderSecondMultiIndex first second))]

private theorem programPT06SecondOrderEulerFourLiftSummand_eq_zero_of_high
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (hDensity : ContDiff Real ∞ density)
    (jet : SpatialJet (Fiber := Fiber) 8)
    (index : ThroatSpatialTruncatedIndex 4)
    (hIndex : ¬ throatSpatialMultiIndexOrder index.1 ≤ 2) :
    programPT06SecondOrderEulerFourLiftSummand density jet index = 0 := by
  rw [programPT06SecondOrderEulerFourLiftSummand,
    programPT06SecondOrderEulerFourVerticalPartial_eq_zero
      density (hDensity.differentiable (by simp)) index
      (Nat.lt_of_not_ge hIndex)]
  simp

private theorem programPT06Fintype_sum_eq_subtype_of_eq_zero
    {Index M : Type*} [Fintype Index] [AddCommMonoid M]
    (predicate : Index → Prop) [DecidablePred predicate]
    (summand : Index → M)
    (hZero : ∀ index, ¬ predicate index → summand index = 0) :
    (∑ index : Index, summand index) =
      ∑ index : { bounded : Index // predicate bounded }, summand index := by
  classical
  calc
    (∑ index : Index, summand index) =
        (∑ index : { bounded : Index // predicate bounded }, summand index) +
          ∑ index : { bounded : Index // ¬ predicate bounded },
            summand index :=
      (Fintype.sum_subtype_add_sum_subtype predicate summand).symm
    _ = ∑ index : { bounded : Index // predicate bounded }, summand index := by
      have hComplement :
          (∑ index : { bounded : Index // ¬ predicate bounded },
            summand index) = 0 :=
        Fintype.sum_eq_zero _ (fun index ↦ hZero index.1 index.2)
      rw [hComplement, add_zero]

private def programPT06SecondOrderLowIndexEquiv :
    ThroatSpatialTruncatedIndex 2 ≃
      { index : ThroatSpatialTruncatedIndex 4 //
        throatSpatialMultiIndexOrder index.1 ≤ 2 } where
  toFun index :=
    ⟨programPT06SecondOrderIndexEmbedding index, index.2⟩
  invFun index := ⟨index.1.1, index.2⟩
  left_inv := by
    intro index
    apply Subtype.ext
    rfl
  right_inv := by
    intro index
    apply Subtype.ext
    apply Subtype.ext
    rfl

private theorem programPT06SecondOrderEulerFourLiftSum_reindex
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (hDensity : ContDiff Real ∞ density)
    (jet : SpatialJet (Fiber := Fiber) 8) :
    (∑ index : ThroatSpatialTruncatedIndex 4,
        programPT06SecondOrderEulerFourLiftSummand density jet index) =
      ∑ index : ThroatSpatialTruncatedIndex 2,
        programPT06SecondOrderEulerFourLiftSummand density jet
          (programPT06SecondOrderIndexEmbedding index) := by
  rw [programPT06Fintype_sum_eq_subtype_of_eq_zero
    (fun index : ThroatSpatialTruncatedIndex 4 ↦
      throatSpatialMultiIndexOrder index.1 ≤ 2)
    (programPT06SecondOrderEulerFourLiftSummand density jet)
    (programPT06SecondOrderEulerFourLiftSummand_eq_zero_of_high
      density hDensity jet)]
  exact (programPT06SecondOrderLowIndexEquiv.sum_comp
    (fun index ↦
      programPT06SecondOrderEulerFourLiftSummand density jet index.1)).symm

/-- Pulling a smooth order-two density first to `J4` does not change its
Euler expression: the order-four presentation on `J8` is the pullback of
the order-two presentation on `J4`. -/
theorem programPT06MultiindexLocalEuler_four_lift_two_eq
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (hDensity : ContDiff Real ∞ density)
    (jet : SpatialJet (Fiber := Fiber) 8) :
    programPT06MultiindexLocalEuler 4
        (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4) density)
        jet =
      programPT06MultiindexLocalEuler 2 density
        (truncateThroatSpatialMultiindexJet (by omega : 4 ≤ 8) jet) := by
  change
    (∑ index : ThroatSpatialTruncatedIndex 4,
      programPT06SecondOrderEulerFourLiftSummand density jet index) =
      ∑ index : ThroatSpatialTruncatedIndex 2,
        programPT06SecondOrderEulerTwoSummand density
          (truncateThroatSpatialMultiindexJet (by omega : 4 ≤ 8) jet)
          index
  rw [programPT06SecondOrderEulerFourLiftSum_reindex density hDensity jet]
  calc
    (∑ index : ThroatSpatialTruncatedIndex 2,
        programPT06SecondOrderEulerFourLiftSummand density jet
          (programPT06SecondOrderIndexEmbedding index)) =
        programPT06SecondOrderEulerFourLiftSummand density jet
            (programPT06SecondOrderIndexEmbedding
              programPT06SecondOrderZeroMultiIndex) +
          (∑ direction : Fin 3,
            programPT06SecondOrderEulerFourLiftSummand density jet
              (programPT06SecondOrderIndexEmbedding
                (programPT06SecondOrderFirstMultiIndex direction))) +
          ∑ first : Fin 3, ∑ second : Fin 3,
            programPT06SecondOrderEulerSymmetryWeight first second •
              programPT06SecondOrderEulerFourLiftSummand density jet
                (programPT06SecondOrderIndexEmbedding
                  (programPT06SecondOrderSecondMultiIndex first second)) :=
      programPT06SecondOrderIndexSum_eq_weightedCoordinates _
    _ =
        programPT06SecondOrderEulerTwoSummand density
            (truncateThroatSpatialMultiindexJet (by omega : 4 ≤ 8) jet)
            programPT06SecondOrderZeroMultiIndex +
          (∑ direction : Fin 3,
            programPT06SecondOrderEulerTwoSummand density
              (truncateThroatSpatialMultiindexJet (by omega : 4 ≤ 8) jet)
              (programPT06SecondOrderFirstMultiIndex direction)) +
          ∑ first : Fin 3, ∑ second : Fin 3,
            programPT06SecondOrderEulerSymmetryWeight first second •
              programPT06SecondOrderEulerTwoSummand density
                (truncateThroatSpatialMultiindexJet (by omega : 4 ≤ 8) jet)
                (programPT06SecondOrderSecondMultiIndex first second) := by
      simp_rw [programPT06SecondOrderEulerLiftSummand_zero density hDensity jet,
        programPT06SecondOrderEulerLiftSummand_one density hDensity,
        programPT06SecondOrderEulerLiftSummand_two density hDensity]
    _ =
        ∑ index : ThroatSpatialTruncatedIndex 2,
          programPT06SecondOrderEulerTwoSummand density
            (truncateThroatSpatialMultiindexJet (by omega : 4 ≤ 8) jet)
            index :=
      (programPT06SecondOrderIndexSum_eq_weightedCoordinates _).symm

private def programPT06FourthJetZeroExtension
    (jet : SpatialJet (Fiber := Fiber) 4) :
    SpatialJet (Fiber := Fiber) 8 :=
  fun index ↦
    if hIndex : throatSpatialMultiIndexOrder index.1 ≤ 4 then
      jet ⟨index.1, hIndex⟩
    else
      0

omit [NormedSpace Real Fiber] in
private theorem programPT06FourthJetZeroExtension_truncate
    (jet : SpatialJet (Fiber := Fiber) 4) :
    truncateThroatSpatialMultiindexJet (by omega : 4 ≤ 8)
        (programPT06FourthJetZeroExtension jet) = jet := by
  funext index
  change
    (if hIndex : throatSpatialMultiIndexOrder index.1 ≤ 4 then
      jet ⟨index.1, hIndex⟩
    else
      0) = jet index
  rw [dif_pos index.2]

private def programPT06SecondJetZeroExtensionContinuousLinearMap :
    SpatialJet (Fiber := Fiber) 2 →L[Real] SpatialJet (Fiber := Fiber) 4 :=
  ContinuousLinearMap.pi fun index : ThroatSpatialTruncatedIndex 4 ↦
    if hIndex : throatSpatialMultiIndexOrder index.1 ≤ 2 then
      ContinuousLinearMap.proj ⟨index.1, hIndex⟩
    else
      0

@[simp] private theorem
    programPT06SecondJetZeroExtensionContinuousLinearMap_apply
    (jet : SpatialJet (Fiber := Fiber) 2) :
    programPT06SecondJetZeroExtensionContinuousLinearMap
        (Fiber := Fiber) jet =
      programPT06SecondJetZeroExtension jet := by
  funext index
  by_cases hIndex : throatSpatialMultiIndexOrder index.1 ≤ 2
  · simp [programPT06SecondJetZeroExtensionContinuousLinearMap,
      programPT06SecondJetZeroExtension, hIndex]
  · simp [programPT06SecondJetZeroExtensionContinuousLinearMap,
      programPT06SecondJetZeroExtension, hIndex]

private theorem programPT06SecondOrderHorizontalCurrentDH_contDiff_top
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (hCurrent : ∀ direction, ContDiff Real ∞ (current direction)) :
    ContDiff Real ∞
      (programPT06SecondOrderHorizontalCurrentDH current) := by
  apply ContDiff.sum
  intro direction _
  exact programPT06ThroatSpatialLocalFunctionTotalDerivative_contDiff_top
    (current direction) (hCurrent direction) direction

private theorem programPT06SecondOrderDensity_contDiff_top_of_factors
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (hFactor : ProgramPT06SecondOrderHorizontalCurrentFactorsDensity4D
      density current)
    (hCurrent : ∀ direction, ContDiff Real ∞ (current direction)) :
    ContDiff Real ∞ density := by
  have hDensity : density =
      programPT06SecondOrderHorizontalCurrentDH current ∘
        programPT06SecondJetZeroExtensionContinuousLinearMap
          (Fiber := Fiber) := by
    funext jet
    rw [programPT06SecondOrderHorizontalCurrentFactorsDensity_reconstruct
      density current hFactor jet]
    rw [Function.comp_apply,
      programPT06SecondJetZeroExtensionContinuousLinearMap_apply]
  rw [hDensity]
  exact (programPT06SecondOrderHorizontalCurrentDH_contDiff_top
    current hCurrent).comp
      (programPT06SecondJetZeroExtensionContinuousLinearMap
        (Fiber := Fiber)).contDiff

/-- A smooth third-jet current whose fourth-jet divergence factors a
second-order density forces the Gate880 Euler expression to vanish. -/
theorem programPT06SecondOrderHorizontalDivergenceSoundness_of_factors
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (hFactor : ProgramPT06SecondOrderHorizontalCurrentFactorsDensity4D
      density current)
    (hCurrent : ∀ direction, ContDiff Real ∞ (current direction))
    (jet : SpatialJet (Fiber := Fiber) 4) :
    programPT06SecondOrderLocalEuler density jet = 0 := by
  have hDensity : ContDiff Real ∞ density :=
    programPT06SecondOrderDensity_contDiff_top_of_factors
      density current hFactor hCurrent
  let ambientJet := programPT06FourthJetZeroExtension jet
  have hFactorFunction :
      programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4) density =
        programPT06SecondOrderHorizontalCurrentDH current := by
    funext fourthJet
    exact hFactor fourthJet
  have hEulerFour :
      programPT06MultiindexLocalEuler 4
          (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4) density)
          ambientJet = 0 := by
    rw [hFactorFunction]
    exact programPT06SecondOrderHorizontalCurrentDH_multiindexEuler_eq_zero
      current hCurrent ambientJet
  have hEulerTwo :
      programPT06MultiindexLocalEuler 2 density jet = 0 := by
    rw [← programPT06FourthJetZeroExtension_truncate jet]
    rw [← programPT06MultiindexLocalEuler_four_lift_two_eq
      density hDensity ambientJet]
    exact hEulerFour
  exact (programPT06MultiindexLocalEuler_two_eq_zero_iff
    density hDensity jet).mp hEulerTwo

/-- Soundness in the Gate926 data interface. -/
theorem programPT06SecondOrderHorizontalDivergenceSoundness
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (data : ProgramPT06SecondOrderHorizontalDivergenceSoundnessData4D
      density current)
    (hCurrent : ∀ direction, ContDiff Real ∞ (current direction))
    (jet : SpatialJet (Fiber := Fiber) 4) :
    programPT06SecondOrderLocalEuler density jet = 0 :=
  programPT06SecondOrderHorizontalDivergenceSoundness_of_factors
    density current data.factors hCurrent jet

/-- Adding a constant to a represented horizontal divergence does not alter
the second-order Euler equation. -/
theorem programPT06SecondOrderHorizontalDivergenceSoundness_of_constant_add
    (density : SpatialJet (Fiber := Fiber) 2 → Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (constant : Real)
    (hDensity : ContDiff Real ∞ density)
    (hCurrent : ∀ direction, ContDiff Real ∞ (current direction))
    (hFactor : ∀ fourthJet : SpatialJet (Fiber := Fiber) 4,
      density
          (truncateThroatSpatialMultiindexJet
            (by omega : 2 ≤ 4) fourthJet) =
        constant + programPT06SecondOrderHorizontalCurrentDH current fourthJet)
    (jet : SpatialJet (Fiber := Fiber) 4) :
    programPT06SecondOrderLocalEuler density jet = 0 := by
  let shifted : SpatialJet (Fiber := Fiber) 2 → Real :=
    fun secondJet ↦ density secondJet - constant
  have hShifted : ContDiff Real ∞ shifted :=
    hDensity.sub contDiff_const
  have hShiftedFactor :
      ProgramPT06SecondOrderHorizontalCurrentFactorsDensity4D
        shifted current := by
    intro fourthJet
    simp only [shifted]
    have hFactorPoint :
        density
            (programPT06FourthJetToSecondJetContinuousLinearMap
              (Fiber := Fiber) fourthJet) =
          constant +
            programPT06SecondOrderHorizontalCurrentDH current fourthJet := by
      simpa only [programPT06FourthJetToSecondJetContinuousLinearMap_apply]
        using hFactor fourthJet
    rw [hFactorPoint]
    ring
  have hShiftedEuler :
      programPT06SecondOrderLocalEuler shifted jet = 0 :=
    programPT06SecondOrderHorizontalDivergenceSoundness_of_factors
      shifted current hShiftedFactor hCurrent jet
  have hShiftedMultiindex :
      programPT06MultiindexLocalEuler 2 shifted jet = 0 :=
    (programPT06MultiindexLocalEuler_two_eq_zero_iff
      shifted hShifted jet).mpr hShiftedEuler
  have hLinearity := congrFun
    (programPT06MultiindexLocalEuler_sub 2 density
      (fun _ : SpatialJet (Fiber := Fiber) 2 ↦ constant)
      hDensity contDiff_const) jet
  have hDensityMultiindex :
      programPT06MultiindexLocalEuler 2 density jet = 0 := by
    change programPT06MultiindexLocalEuler 2 shifted jet =
      programPT06MultiindexLocalEuler 2 density jet -
        programPT06MultiindexLocalEuler 2
          (fun _ : SpatialJet (Fiber := Fiber) 2 ↦ constant) jet at hLinearity
    simpa [hShiftedMultiindex] using hLinearity.symm
  exact (programPT06MultiindexLocalEuler_two_eq_zero_iff
    density hDensity jet).mp hDensityMultiindex

end
end P0EFTJanusProgramPT06SecondOrderHorizontalDivergenceEulerClosure4D
end JanusFormal
