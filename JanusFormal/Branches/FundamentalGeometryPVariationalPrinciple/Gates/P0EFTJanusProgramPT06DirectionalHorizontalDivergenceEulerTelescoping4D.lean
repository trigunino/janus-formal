import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientVerticalTotalDerivativeCommutator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientMultiindexTotalDerivativeCommutation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientLocalFunctionLiftNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06TruncatedIndexSuccessorEquiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D

/-!
# Directional horizontal-divergence Euler telescoping

The multi-index Euler operator annihilates one smooth directional total
derivative.  The proof is carried on the fixed ambient eighth jet.  The
vertical-total commutator produces a predecessor term, and successor
reindexing pairs it with the leading term of the preceding multi-index.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06DirectionalHorizontalDivergenceEulerTelescoping4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D
open P0EFTJanusProgramPT06AmbientVerticalTotalDerivativeCommutator4D
open P0EFTJanusProgramPT06AmbientMultiindexTotalDerivativeCommutation4D
open P0EFTJanusProgramPT06AmbientLocalFunctionLiftNaturality4D
open P0EFTJanusProgramPT06TruncatedShiftCoordinateInjection4D
open P0EFTJanusProgramPT06TruncatedIndexSuccessorEquiv4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u v

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev SpatialJet (Fiber : Type u) (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

private abbrev AmbientCovector := Fiber →L[Real] Real

private def programPT06DirectionalCurrentAmbientLift
    (currentComponent : SpatialJet Fiber 3 → Real) :
    SpatialJet Fiber 8 → Real :=
  programPT06AmbientLocalFunctionLift (by omega : 3 ≤ 8) currentComponent

private def programPT06DirectionalEulerIndexEmbedding
    (index : ThroatSpatialTruncatedIndex 4) :
    ThroatSpatialTruncatedIndex 8 :=
  programPT06TruncatedIndexOfLE (by omega : 4 ≤ 8) index

private def programPT06DirectionalCurrentVerticalPartial
    (currentComponent : SpatialJet Fiber 3 → Real)
    (index : ThroatSpatialTruncatedIndex 4) :
    SpatialJet Fiber 8 → AmbientCovector (Fiber := Fiber) :=
  fun jet ↦
    programPT06ThroatSpatialVerticalPartialDerivative
      (programPT06DirectionalCurrentAmbientLift currentComponent) jet
      (programPT06DirectionalEulerIndexEmbedding index)

private theorem programPT06DirectionalCurrentAmbientLift_contDiff
    (currentComponent : SpatialJet Fiber 3 → Real)
    (hCurrent : ContDiff Real ∞ currentComponent) :
    ContDiff Real ∞
      (programPT06DirectionalCurrentAmbientLift currentComponent) := by
  exact programPT06AmbientLocalFunctionLift_contDiff
    (by omega : 3 ≤ 8) currentComponent hCurrent

private theorem programPT06DirectionalCurrentVerticalPartial_contDiff
    (currentComponent : SpatialJet Fiber 3 → Real)
    (hCurrent : ContDiff Real ∞ currentComponent)
    (index : ThroatSpatialTruncatedIndex 4) :
    ContDiff Real ∞
      (programPT06DirectionalCurrentVerticalPartial
        currentComponent index) := by
  exact programPT06ThroatSpatialVerticalPartialDerivative_contDiff_top
    (programPT06DirectionalCurrentAmbientLift currentComponent)
    (programPT06DirectionalCurrentAmbientLift_contDiff
      currentComponent hCurrent)
    (programPT06DirectionalEulerIndexEmbedding index)

private theorem programPT06DirectionalDensityAmbientLift
    (currentComponent : SpatialJet Fiber 3 → Real)
    (hCurrent : ContDiff Real ∞ currentComponent)
    (direction : Fin 3) :
    programPT06LocalDensityDoubleOrderLift 4
        (programPT06ThroatSpatialLocalFunctionTotalDerivative
          direction currentComponent) =
      programPT06AmbientLocalFunctionTotalDerivative 8 direction
        (programPT06DirectionalCurrentAmbientLift currentComponent) := by
  change
    programPT06AmbientLocalFunctionLift (by omega : 4 ≤ 8)
        (programPT06ThroatSpatialLocalFunctionTotalDerivative
          direction currentComponent) =
      programPT06AmbientLocalFunctionTotalDerivative 8 direction
        (programPT06AmbientLocalFunctionLift
          (by omega : 3 ≤ 8) currentComponent)
  exact (programPT06AmbientLocalFunctionLift_totalDerivative
    (by omega : 3 + 1 ≤ 8) direction currentComponent
    (hCurrent.differentiable (by simp))).symm

private def programPT06DirectionalEmbeddedPredecessorVerticalPartial
    (currentComponent : SpatialJet Fiber 3 → Real)
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 4)
    (hCoordinate : index.1 direction ≠ 0) :
    SpatialJet Fiber 8 → AmbientCovector (Fiber := Fiber) :=
  fun jet ↦
    programPT06ThroatSpatialVerticalPartialDerivative
      (programPT06DirectionalCurrentAmbientLift currentComponent) jet
      (programPT06TruncatedIndexPredecessor 8 direction
        (programPT06DirectionalEulerIndexEmbedding index)
        (by
          simpa only [programPT06DirectionalEulerIndexEmbedding,
            programPT06TruncatedIndexOfLE_value] using hCoordinate))

private theorem
    programPT06DirectionalEmbeddedPredecessorVerticalPartial_contDiff
    (currentComponent : SpatialJet Fiber 3 → Real)
    (hCurrent : ContDiff Real ∞ currentComponent)
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 4)
    (hCoordinate : index.1 direction ≠ 0) :
    ContDiff Real ∞
      (programPT06DirectionalEmbeddedPredecessorVerticalPartial
        currentComponent direction index hCoordinate) := by
  exact programPT06ThroatSpatialVerticalPartialDerivative_contDiff_top
    (programPT06DirectionalCurrentAmbientLift currentComponent)
    (programPT06DirectionalCurrentAmbientLift_contDiff
      currentComponent hCurrent)
    (programPT06TruncatedIndexPredecessor 8 direction
      (programPT06DirectionalEulerIndexEmbedding index)
      (by
        simpa only [programPT06DirectionalEulerIndexEmbedding,
          programPT06TruncatedIndexOfLE_value] using hCoordinate))

private def programPT06DirectionalEulerLeadingSummand
    (currentComponent : SpatialJet Fiber 3 → Real)
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 4)
    (jet : SpatialJet Fiber 8) : AmbientCovector (Fiber := Fiber) :=
  ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
    programPT06AmbientMultiindexTotalDerivative 8 index.1
      (programPT06AmbientLocalFunctionTotalDerivative 8 direction
        (programPT06DirectionalCurrentVerticalPartial
          currentComponent index)) jet

private def programPT06DirectionalEulerPredecessorSummand
    (currentComponent : SpatialJet Fiber 3 → Real)
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 4)
    (hCoordinate : index.1 direction ≠ 0)
    (jet : SpatialJet Fiber 8) : AmbientCovector (Fiber := Fiber) :=
  ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
    programPT06AmbientMultiindexTotalDerivative 8 index.1
      (programPT06DirectionalEmbeddedPredecessorVerticalPartial
        currentComponent direction index hCoordinate) jet

private def programPT06DirectionalEulerOptionalPredecessorSummand
    (currentComponent : SpatialJet Fiber 3 → Real)
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 4)
    (jet : SpatialJet Fiber 8) : AmbientCovector (Fiber := Fiber) :=
  if hCoordinate : index.1 direction = 0 then
    0
  else
    programPT06DirectionalEulerPredecessorSummand
      currentComponent direction index hCoordinate jet

private theorem programPT06DirectionalEulerVerticalPartial_decomposition
    (currentComponent : SpatialJet Fiber 3 → Real)
    (hCurrent : ContDiff Real ∞ currentComponent)
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 4) :
    programPT06MultiindexLocalVerticalPartial 4
        (programPT06ThroatSpatialLocalFunctionTotalDerivative
          direction currentComponent) index =
      programPT06AmbientLocalFunctionTotalDerivative 8 direction
          (programPT06DirectionalCurrentVerticalPartial
            currentComponent index) +
        if hCoordinate : index.1 direction = 0 then
          0
        else
          programPT06DirectionalEmbeddedPredecessorVerticalPartial
            currentComponent direction index hCoordinate := by
  funext jet
  rw [show
    programPT06MultiindexLocalVerticalPartial 4
        (programPT06ThroatSpatialLocalFunctionTotalDerivative
          direction currentComponent) index jet =
      programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06LocalDensityDoubleOrderLift 4
          (programPT06ThroatSpatialLocalFunctionTotalDerivative
            direction currentComponent)) jet
        (programPT06DirectionalEulerIndexEmbedding index) by rfl]
  rw [programPT06DirectionalDensityAmbientLift
    currentComponent hCurrent direction]
  have hLiftTwo : ContDiff Real 2
      (programPT06DirectionalCurrentAmbientLift currentComponent) :=
    (programPT06DirectionalCurrentAmbientLift_contDiff
      currentComponent hCurrent).of_le
        (show (2 : ℕ∞) ≤ ∞ by
          exact WithTop.coe_le_coe.mpr le_top)
  by_cases hCoordinate : index.1 direction = 0
  · have hEmbedded :
        (programPT06DirectionalEulerIndexEmbedding index).1 direction = 0 := by
      simpa only [programPT06DirectionalEulerIndexEmbedding,
        programPT06TruncatedIndexOfLE_value] using hCoordinate
    rw [dif_pos hCoordinate, add_zero]
    change
      programPT06ThroatSpatialVerticalPartialDerivative
          (programPT06AmbientLocalFunctionTotalDerivative 8 direction
            (programPT06DirectionalCurrentAmbientLift currentComponent)) jet
          (programPT06DirectionalEulerIndexEmbedding index) =
        programPT06AmbientLocalFunctionTotalDerivative 8 direction
          (fun y ↦ programPT06ThroatSpatialVerticalPartialDerivative
            (programPT06DirectionalCurrentAmbientLift currentComponent) y
            (programPT06DirectionalEulerIndexEmbedding index)) jet
    exact
      programPT06AmbientVerticalTotalDerivative_commute_of_coordinate_eq_zero
        8 direction
        (programPT06DirectionalCurrentAmbientLift currentComponent)
        hLiftTwo jet (programPT06DirectionalEulerIndexEmbedding index)
        hEmbedded
  · have hEmbedded :
        (programPT06DirectionalEulerIndexEmbedding index).1 direction ≠ 0 := by
      simpa only [programPT06DirectionalEulerIndexEmbedding,
        programPT06TruncatedIndexOfLE_value] using hCoordinate
    rw [dif_neg hCoordinate]
    change
      programPT06ThroatSpatialVerticalPartialDerivative
          (programPT06AmbientLocalFunctionTotalDerivative 8 direction
            (programPT06DirectionalCurrentAmbientLift currentComponent)) jet
          (programPT06DirectionalEulerIndexEmbedding index) =
        programPT06AmbientLocalFunctionTotalDerivative 8 direction
            (fun y ↦ programPT06ThroatSpatialVerticalPartialDerivative
              (programPT06DirectionalCurrentAmbientLift currentComponent) y
              (programPT06DirectionalEulerIndexEmbedding index)) jet +
          programPT06ThroatSpatialVerticalPartialDerivative
            (programPT06DirectionalCurrentAmbientLift currentComponent) jet
            (programPT06TruncatedIndexPredecessor 8 direction
              (programPT06DirectionalEulerIndexEmbedding index) hEmbedded)
    exact
      programPT06AmbientVerticalTotalDerivative_commute_of_coordinate_ne_zero
        8 direction
        (programPT06DirectionalCurrentAmbientLift currentComponent)
        hLiftTwo jet (programPT06DirectionalEulerIndexEmbedding index)
        hEmbedded

private theorem programPT06DirectionalEulerSummand_decomposition
    (currentComponent : SpatialJet Fiber 3 → Real)
    (hCurrent : ContDiff Real ∞ currentComponent)
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 4)
    (jet : SpatialJet Fiber 8) :
    ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
        programPT06AmbientMultiindexTotalDerivative 8 index.1
          (programPT06MultiindexLocalVerticalPartial 4
            (programPT06ThroatSpatialLocalFunctionTotalDerivative
              direction currentComponent) index) jet =
      programPT06DirectionalEulerLeadingSummand
          currentComponent direction index jet +
        programPT06DirectionalEulerOptionalPredecessorSummand
          currentComponent direction index jet := by
  rw [programPT06DirectionalEulerVerticalPartial_decomposition
    currentComponent hCurrent direction index]
  by_cases hCoordinate : index.1 direction = 0
  · rw [dif_pos hCoordinate,
      programPT06DirectionalEulerOptionalPredecessorSummand,
      dif_pos hCoordinate, add_zero]
    simp only [programPT06DirectionalEulerLeadingSummand, add_zero]
  · rw [dif_neg hCoordinate]
    change
      ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
          programPT06AmbientMultiindexTotalDerivative 8 index.1
            (programPT06AmbientLocalFunctionTotalDerivative 8 direction
                (programPT06DirectionalCurrentVerticalPartial
                  currentComponent index) +
              programPT06DirectionalEmbeddedPredecessorVerticalPartial
                currentComponent direction index hCoordinate) jet = _
    rw [show
      programPT06AmbientMultiindexTotalDerivative 8 index.1
          (programPT06AmbientLocalFunctionTotalDerivative 8 direction
              (programPT06DirectionalCurrentVerticalPartial
                currentComponent index) +
            programPT06DirectionalEmbeddedPredecessorVerticalPartial
              currentComponent direction index hCoordinate) =
        programPT06AmbientMultiindexTotalDerivative 8 index.1
            (programPT06AmbientLocalFunctionTotalDerivative 8 direction
              (programPT06DirectionalCurrentVerticalPartial
                currentComponent index)) +
          programPT06AmbientMultiindexTotalDerivative 8 index.1
            (programPT06DirectionalEmbeddedPredecessorVerticalPartial
              currentComponent direction index hCoordinate) by
      unfold programPT06AmbientMultiindexTotalDerivative
      exact programPT06AmbientIteratedTotalDerivative_add 8
        (programPT06ThroatSpatialMultiIndexDirectionWord index.1)
        (programPT06AmbientLocalFunctionTotalDerivative 8 direction
          (programPT06DirectionalCurrentVerticalPartial
            currentComponent index))
        (programPT06DirectionalEmbeddedPredecessorVerticalPartial
          currentComponent direction index hCoordinate)
        (programPT06AmbientLocalFunctionTotalDerivative_contDiff 8 direction
          (programPT06DirectionalCurrentVerticalPartial
            currentComponent index)
          (programPT06DirectionalCurrentVerticalPartial_contDiff
            currentComponent hCurrent index))
        (programPT06DirectionalEmbeddedPredecessorVerticalPartial_contDiff
          currentComponent hCurrent direction index hCoordinate)]
    simp only [Pi.add_apply, smul_add,
      programPT06DirectionalEulerLeadingSummand,
      programPT06DirectionalEulerOptionalPredecessorSummand,
      dif_neg hCoordinate,
      programPT06DirectionalEulerPredecessorSummand]

private theorem programPT06Fintype_sum_eq_subtype_of_eq_zero
    {Index : Type u} {M : Type v} [Fintype Index] [AddCommMonoid M]
    (predicate : Index → Prop) [DecidablePred predicate]
    (summand : Index → M)
    (hZero : ∀ index, ¬ predicate index → summand index = 0) :
    (∑ index : Index, summand index) =
      ∑ index : { bounded : Index // predicate bounded }, summand index := by
  classical
  calc
    (∑ index : Index, summand index) =
        (∑ index : { bounded : Index // predicate bounded }, summand index) +
          ∑ index : { bounded : Index // ¬ predicate bounded }, summand index :=
      (Fintype.sum_subtype_add_sum_subtype predicate summand).symm
    _ = ∑ index : { bounded : Index // predicate bounded }, summand index := by
      have hComplement :
          (∑ index : { bounded : Index // ¬ predicate bounded },
            summand index) = 0 :=
        Fintype.sum_eq_zero _ (fun index ↦ hZero index.1 index.2)
      rw [hComplement, add_zero]

private theorem programPT06DirectionalCurrentVerticalPartial_eq_zero
    (currentComponent : SpatialJet Fiber 3 → Real)
    (hCurrent : ContDiff Real ∞ currentComponent)
    (index : ThroatSpatialTruncatedIndex 4)
    (hOrder : 3 < throatSpatialMultiIndexOrder index.1) :
    programPT06DirectionalCurrentVerticalPartial currentComponent index = 0 := by
  funext jet
  exact programPT06AmbientLocalFunctionLift_verticalPartial_eq_zero
    (by omega : 3 ≤ 8) currentComponent
    (hCurrent.differentiable (by simp)) jet
    (programPT06DirectionalEulerIndexEmbedding index)
    (by
      simpa only [programPT06DirectionalEulerIndexEmbedding,
        programPT06TruncatedIndexOfLE_value] using hOrder)

private theorem programPT06DirectionalEulerLeadingSummand_eq_zero_of_top
    (currentComponent : SpatialJet Fiber 3 → Real)
    (hCurrent : ContDiff Real ∞ currentComponent)
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 4)
    (hOrder : 3 < throatSpatialMultiIndexOrder index.1)
    (jet : SpatialJet Fiber 8) :
    programPT06DirectionalEulerLeadingSummand
      currentComponent direction index jet = 0 := by
  rw [programPT06DirectionalEulerLeadingSummand,
    programPT06DirectionalCurrentVerticalPartial_eq_zero
      currentComponent hCurrent index hOrder]
  simp

private theorem programPT06DirectionalEulerLeadingSum_reindex
    (currentComponent : SpatialJet Fiber 3 → Real)
    (hCurrent : ContDiff Real ∞ currentComponent)
    (direction : Fin 3) (jet : SpatialJet Fiber 8) :
    (∑ index : ThroatSpatialTruncatedIndex 4,
        programPT06DirectionalEulerLeadingSummand
          currentComponent direction index jet) =
      ∑ index : ThroatSpatialTruncatedIndex 3,
        programPT06DirectionalEulerLeadingSummand currentComponent direction
          (programPT06TruncatedIndexLowerOrderEquiv 3 index).1 jet := by
  rw [programPT06Fintype_sum_eq_subtype_of_eq_zero
    (fun index : ThroatSpatialTruncatedIndex 4 ↦
      throatSpatialMultiIndexOrder index.1 ≤ 3)
    (fun index ↦ programPT06DirectionalEulerLeadingSummand
      currentComponent direction index jet)
    (fun index hIndex ↦
      programPT06DirectionalEulerLeadingSummand_eq_zero_of_top
        currentComponent hCurrent direction index
        (Nat.lt_of_not_ge hIndex) jet)]
  exact (programPT06TruncatedIndexLowerOrderEquiv_sum_comp 3
    (fun index ↦ programPT06DirectionalEulerLeadingSummand
      currentComponent direction index.1 jet)).symm

private theorem
    programPT06DirectionalEmbeddedSuccessorPredecessor_eq_lowerEmbedding
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 3) :
    programPT06TruncatedIndexPredecessor 8 direction
        (programPT06DirectionalEulerIndexEmbedding
          (programPT06TruncatedIndexSuccessorEquiv 3 direction index).1)
        (by
          simpa only [programPT06DirectionalEulerIndexEmbedding,
            programPT06TruncatedIndexOfLE_value,
            programPT06TruncatedIndexSuccessorEquiv_apply,
            programPT06TruncatedIndexSuccessor_coordinate] using
            Nat.succ_ne_zero (index.1 direction)) =
      programPT06DirectionalEulerIndexEmbedding
        (programPT06TruncatedIndexLowerOrderEquiv 3 index).1 := by
  apply Subtype.ext
  exact add_right_cancel
    ((programPT06TruncatedIndexPredecessor_add_coordinate 8 direction
      (programPT06DirectionalEulerIndexEmbedding
        (programPT06TruncatedIndexSuccessorEquiv 3 direction index).1)
      (by
        simpa only [programPT06DirectionalEulerIndexEmbedding,
          programPT06TruncatedIndexOfLE_value,
          programPT06TruncatedIndexSuccessorEquiv_apply,
          programPT06TruncatedIndexSuccessor_coordinate] using
          Nat.succ_ne_zero (index.1 direction))).trans (by
      simp only [programPT06DirectionalEulerIndexEmbedding,
        programPT06TruncatedIndexOfLE_value,
        programPT06TruncatedIndexSuccessorEquiv_apply,
        programPT06TruncatedIndexSuccessor_value,
        programPT06TruncatedIndexLowerOrderEquiv_apply,
        programPT06TruncatedIndexLowerOrderEmbedding_value]))

private theorem
    programPT06DirectionalEmbeddedPredecessorVerticalPartial_successor
    (currentComponent : SpatialJet Fiber 3 → Real)
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 3)
    (hCoordinate :
      (programPT06TruncatedIndexSuccessorEquiv 3 direction index).1.1
        direction ≠ 0) :
    programPT06DirectionalEmbeddedPredecessorVerticalPartial
        currentComponent direction
        (programPT06TruncatedIndexSuccessorEquiv 3 direction index).1
        hCoordinate =
      programPT06DirectionalCurrentVerticalPartial currentComponent
        (programPT06TruncatedIndexLowerOrderEquiv 3 index).1 := by
  funext jet
  unfold programPT06DirectionalEmbeddedPredecessorVerticalPartial
    programPT06DirectionalCurrentVerticalPartial
  rw [programPT06DirectionalEmbeddedSuccessorPredecessor_eq_lowerEmbedding]

private theorem programPT06DirectionalEulerSuccessor_pair
    (currentComponent : SpatialJet Fiber 3 → Real)
    (hCurrent : ContDiff Real ∞ currentComponent)
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 3)
    (jet : SpatialJet Fiber 8) :
    programPT06DirectionalEulerOptionalPredecessorSummand
        currentComponent direction
        (programPT06TruncatedIndexSuccessorEquiv 3 direction index).1 jet =
      -programPT06DirectionalEulerLeadingSummand
        currentComponent direction
        (programPT06TruncatedIndexLowerOrderEquiv 3 index).1 jet := by
  have hCoordinate :
      (programPT06TruncatedIndexSuccessorEquiv 3 direction index).1.1
        direction ≠ 0 := by
    simpa only [programPT06TruncatedIndexSuccessorEquiv_apply,
      programPT06TruncatedIndexSuccessor_coordinate] using
      Nat.succ_ne_zero (index.1 direction)
  rw [programPT06DirectionalEulerOptionalPredecessorSummand,
    dif_neg hCoordinate,
    programPT06DirectionalEulerPredecessorSummand,
    programPT06DirectionalEmbeddedPredecessorVerticalPartial_successor
      currentComponent direction index hCoordinate,
    programPT06DirectionalEulerLeadingSummand]
  simp only [programPT06TruncatedIndexSuccessorEquiv_apply,
    programPT06TruncatedIndexSuccessor_value,
    programPT06TruncatedIndexLowerOrderEquiv_apply,
    programPT06TruncatedIndexLowerOrderEmbedding_value,
    throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
  rw [programPT06AmbientMultiindexTotalDerivative_add_coordinate 8 index.1
    direction
    (programPT06DirectionalCurrentVerticalPartial currentComponent
      (programPT06TruncatedIndexLowerOrderEmbedding 3 index).1)
    (programPT06DirectionalCurrentVerticalPartial_contDiff
      currentComponent hCurrent
      (programPT06TruncatedIndexLowerOrderEmbedding 3 index).1)]
  simp [pow_succ]

private theorem programPT06DirectionalEulerOptionalPredecessorSum_reindex
    (currentComponent : SpatialJet Fiber 3 → Real)
    (direction : Fin 3) (jet : SpatialJet Fiber 8) :
    (∑ index : ThroatSpatialTruncatedIndex 4,
        programPT06DirectionalEulerOptionalPredecessorSummand
          currentComponent direction index jet) =
      ∑ index : ThroatSpatialTruncatedIndex 3,
        programPT06DirectionalEulerOptionalPredecessorSummand
          currentComponent direction
          (programPT06TruncatedIndexSuccessorEquiv 3 direction index).1 jet := by
  rw [programPT06Fintype_sum_eq_subtype_of_eq_zero
    (fun index : ThroatSpatialTruncatedIndex 4 ↦ index.1 direction ≠ 0)
    (fun index ↦ programPT06DirectionalEulerOptionalPredecessorSummand
      currentComponent direction index jet)
    (fun index hIndex ↦ by
      have hCoordinate : index.1 direction = 0 := not_ne_iff.mp hIndex
      simp [programPT06DirectionalEulerOptionalPredecessorSummand,
        hCoordinate])]
  exact (programPT06TruncatedIndexSuccessorEquiv_sum_comp 3 direction
    (fun index ↦ programPT06DirectionalEulerOptionalPredecessorSummand
      currentComponent direction index.1 jet)).symm

/-- The order-four multi-index Euler operator annihilates one smooth
directional total derivative of an order-three current component. -/
theorem programPT06DirectionalHorizontalDivergence_multiindexEuler_eq_zero
    (currentComponent : SpatialJet Fiber 3 → Real)
    (hCurrent : ContDiff Real ∞ currentComponent)
    (direction : Fin 3) (jet : SpatialJet Fiber 8) :
    programPT06MultiindexLocalEuler 4
        (programPT06ThroatSpatialLocalFunctionTotalDerivative
          direction currentComponent) jet = 0 := by
  rw [programPT06MultiindexLocalEuler]
  calc
    (∑ index : ThroatSpatialTruncatedIndex 4,
        ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
          programPT06AmbientMultiindexTotalDerivative 8 index.1
            (programPT06MultiindexLocalVerticalPartial 4
              (programPT06ThroatSpatialLocalFunctionTotalDerivative
                direction currentComponent) index) jet) =
        ∑ index : ThroatSpatialTruncatedIndex 4,
          (programPT06DirectionalEulerLeadingSummand
              currentComponent direction index jet +
            programPT06DirectionalEulerOptionalPredecessorSummand
              currentComponent direction index jet) := by
      apply Finset.sum_congr rfl
      intro index _
      exact programPT06DirectionalEulerSummand_decomposition
        currentComponent hCurrent direction index jet
    _ =
        (∑ index : ThroatSpatialTruncatedIndex 4,
          programPT06DirectionalEulerLeadingSummand
            currentComponent direction index jet) +
        ∑ index : ThroatSpatialTruncatedIndex 4,
          programPT06DirectionalEulerOptionalPredecessorSummand
            currentComponent direction index jet :=
      Finset.sum_add_distrib
    _ =
        (∑ index : ThroatSpatialTruncatedIndex 3,
          programPT06DirectionalEulerLeadingSummand currentComponent direction
            (programPT06TruncatedIndexLowerOrderEquiv 3 index).1 jet) +
        ∑ index : ThroatSpatialTruncatedIndex 3,
          programPT06DirectionalEulerOptionalPredecessorSummand
            currentComponent direction
            (programPT06TruncatedIndexSuccessorEquiv 3 direction index).1 jet := by
      rw [programPT06DirectionalEulerLeadingSum_reindex
          currentComponent hCurrent direction jet,
        programPT06DirectionalEulerOptionalPredecessorSum_reindex
          currentComponent direction jet]
    _ = 0 := by
      rw [show
        (∑ index : ThroatSpatialTruncatedIndex 3,
          programPT06DirectionalEulerOptionalPredecessorSummand
            currentComponent direction
            (programPT06TruncatedIndexSuccessorEquiv 3 direction index).1 jet) =
          -(∑ index : ThroatSpatialTruncatedIndex 3,
            programPT06DirectionalEulerLeadingSummand
              currentComponent direction
              (programPT06TruncatedIndexLowerOrderEquiv 3 index).1 jet) by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro index _
        exact programPT06DirectionalEulerSuccessor_pair
          currentComponent hCurrent direction index jet]
      exact add_neg_cancel _

end
end P0EFTJanusProgramPT06DirectionalHorizontalDivergenceEulerTelescoping4D
end JanusFormal
