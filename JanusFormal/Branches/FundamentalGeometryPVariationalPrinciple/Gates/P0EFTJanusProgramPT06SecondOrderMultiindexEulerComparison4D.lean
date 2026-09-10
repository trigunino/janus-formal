import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderJetRadialDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientMultiindexTotalDerivativeCommutation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientLocalFunctionLiftNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D

/-!
# Comparison of the order-two Euler presentations

The generic multi-index Euler sum agrees with the specialized Gate880
ordered-pair formula.  The half-weight in Gate880 is exactly the regrouping
weight for the symmetric order-two multi-index coordinates.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06SecondOrderMultiindexEulerComparison4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06SecondOrderJetRadialDecomposition4D
open P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D
open P0EFTJanusProgramPT06AmbientMultiindexTotalDerivativeCommutation4D
open P0EFTJanusProgramPT06AmbientLocalFunctionLiftNaturality4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u v

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
variable {Target : Type v} [NormedAddCommGroup Target] [NormedSpace Real Target]

private abbrev SpatialJet (E : Type*) [NormedAddCommGroup E]
    [NormedSpace Real E] (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet E order

private def programPT06SecondOrderCoordinateSum :
    SpatialJet Target 2 →L[Real] Target :=
  ∑ index : ThroatSpatialTruncatedIndex 2,
    ContinuousLinearMap.proj index

@[simp] private theorem programPT06SecondOrderCoordinateSum_apply
    (coefficients : SpatialJet Target 2) :
    programPT06SecondOrderCoordinateSum (Target := Target) coefficients =
      ∑ index : ThroatSpatialTruncatedIndex 2, coefficients index := by
  simp [programPT06SecondOrderCoordinateSum]

@[simp] private theorem programPT06SecondOrderCoordinateSum_injection
    (index : ThroatSpatialTruncatedIndex 2) (coefficient : Target) :
    programPT06SecondOrderCoordinateSum (Target := Target)
        (programPT06ThroatSpatialJetCoordinateInjection index coefficient) =
      coefficient := by
  rw [programPT06SecondOrderCoordinateSum_apply, Finset.sum_eq_single index]
  · exact programPT06ThroatSpatialJetCoordinateInjection_same index coefficient
  · intro coordinate _ hCoordinate
    exact programPT06ThroatSpatialJetCoordinateInjection_of_ne
      index coordinate hCoordinate coefficient
  · intro hIndex
    exact (hIndex (Finset.mem_univ index)).elim

/-- Regrouping an arbitrary order-two multi-index sum into the Gate880
value, first-order, and weighted ordered-pair coordinates. -/
theorem programPT06SecondOrderIndexSum_eq_weightedCoordinates
    (summand : ThroatSpatialTruncatedIndex 2 → Target) :
    (∑ index : ThroatSpatialTruncatedIndex 2, summand index) =
      summand programPT06SecondOrderZeroMultiIndex +
        (∑ direction : Fin 3,
          summand (programPT06SecondOrderFirstMultiIndex direction)) +
        ∑ first : Fin 3, ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight first second •
            summand (programPT06SecondOrderSecondMultiIndex first second) := by
  classical
  have hDecomposition := congrArg
    (programPT06SecondOrderCoordinateSum (Target := Target))
    (programPT06SecondOrderJet_weightedCoordinateDecomposition
      (Fiber := Target) summand)
  rw [programPT06SecondOrderCoordinateSum_apply
    (Target := Target) summand] at hDecomposition
  simpa only [map_add, map_sum, map_smul,
    programPT06SecondOrderCoordinateSum_injection] using hDecomposition

private theorem programPT06SecondOrderMultiindexVerticalPartial_eq_lift
    (localLagrangian : SpatialJet Fiber 2 → Real)
    (hLagrangian : Differentiable Real localLagrangian)
    (index : ThroatSpatialTruncatedIndex 2) :
    programPT06MultiindexLocalVerticalPartial 2 localLagrangian index =
      programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
        (fun jet ↦ programPT06ThroatSpatialVerticalPartialDerivative
          localLagrangian jet index) := by
  funext jet
  change
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
          localLagrangian) jet
        (programPT06TruncatedIndexOfLE (by omega : 2 ≤ 4) index) =
      programPT06ThroatSpatialVerticalPartialDerivative localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) index
  exact programPT06AmbientLocalFunctionLift_verticalPartial_ofLE
    (by omega : 2 ≤ 4) localLagrangian hLagrangian jet index

private theorem programPT06SecondOrderMultiindexVerticalPartial_contDiff
    (localLagrangian : SpatialJet Fiber 2 → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (index : ThroatSpatialTruncatedIndex 2) :
    ContDiff Real ∞
      (programPT06MultiindexLocalVerticalPartial 2 localLagrangian index) := by
  rw [programPT06SecondOrderMultiindexVerticalPartial_eq_lift
    localLagrangian (hLagrangian.differentiable (by simp)) index]
  apply programPT06AmbientLocalFunctionLift_contDiff
  exact programPT06ThroatSpatialVerticalPartialDerivative_contDiff_top
    localLagrangian hLagrangian index

private theorem programPT06SecondOrderMultiindexDerivative_zero
    (localLagrangian : SpatialJet Fiber 2 → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (jet : SpatialJet Fiber 4) :
    programPT06AmbientMultiindexTotalDerivative 4
        programPT06SecondOrderZeroMultiIndex.1
        (programPT06MultiindexLocalVerticalPartial 2 localLagrangian
          programPT06SecondOrderZeroMultiIndex) jet =
      programPT06SecondOrderLocalVerticalPartialZero localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) := by
  rw [programPT06SecondOrderMultiindexVerticalPartial_eq_lift
    localLagrangian (hLagrangian.differentiable (by simp))]
  change
    programPT06AmbientMultiindexTotalDerivative 4 0
        (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
          (fun jet ↦ programPT06ThroatSpatialVerticalPartialDerivative
            localLagrangian jet programPT06SecondOrderZeroMultiIndex)) jet = _
  rw [programPT06AmbientMultiindexTotalDerivative_zero_index]
  rfl

private theorem programPT06SecondOrderMultiindexDerivative_one
    (localLagrangian : SpatialJet Fiber 2 → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (direction : Fin 3) (jet : SpatialJet Fiber 4) :
    programPT06AmbientMultiindexTotalDerivative 4
        (programPT06SecondOrderFirstMultiIndex direction).1
        (programPT06MultiindexLocalVerticalPartial 2 localLagrangian
          (programPT06SecondOrderFirstMultiIndex direction)) jet =
      programPT06SecondOrderLocalEulerFirstTotalTerm
        localLagrangian direction
        (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet) := by
  have hPartial : ContDiff Real ∞
      (programPT06SecondOrderLocalVerticalPartialOne
        localLagrangian direction) :=
    programPT06ThroatSpatialVerticalPartialDerivative_contDiff_top
      localLagrangian hLagrangian
      (programPT06SecondOrderFirstMultiIndex direction)
  have hLift : ContDiff Real ∞
      (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
        (programPT06SecondOrderLocalVerticalPartialOne
          localLagrangian direction)) :=
    programPT06AmbientLocalFunctionLift_contDiff
      (by omega : 2 ≤ 4) _ hPartial
  rw [programPT06SecondOrderMultiindexVerticalPartial_eq_lift
    localLagrangian (hLagrangian.differentiable (by simp))]
  change
    programPT06AmbientMultiindexTotalDerivative 4
        (throatSpatialCoordinateMultiIndex direction)
        (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
          (programPT06SecondOrderLocalVerticalPartialOne
            localLagrangian direction)) jet = _
  rw [show throatSpatialCoordinateMultiIndex direction =
      0 + throatSpatialCoordinateMultiIndex direction by simp]
  rw [programPT06AmbientMultiindexTotalDerivative_add_coordinate 4 0 direction
    (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
      (programPT06SecondOrderLocalVerticalPartialOne
        localLagrangian direction)) hLift]
  rw [programPT06AmbientMultiindexTotalDerivative_zero_index]
  rw [programPT06AmbientLocalFunctionLift_totalDerivative
    (by omega : 2 + 1 ≤ 4) direction _
    (hPartial.differentiable (by simp))]
  rfl

private theorem programPT06SecondOrderMultiindexDerivative_two
    (localLagrangian : SpatialJet Fiber 2 → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (first second : Fin 3) (jet : SpatialJet Fiber 4) :
    programPT06AmbientMultiindexTotalDerivative 4
        (programPT06SecondOrderSecondMultiIndex first second).1
        (programPT06MultiindexLocalVerticalPartial 2 localLagrangian
          (programPT06SecondOrderSecondMultiIndex first second)) jet =
      programPT06SecondOrderLocalEulerSecondTotalTerm
        localLagrangian first second jet := by
  have hPartial : ContDiff Real ∞
      (programPT06SecondOrderLocalVerticalPartialTwo
        localLagrangian first second) :=
    programPT06ThroatSpatialVerticalPartialDerivative_contDiff_top
      localLagrangian hLagrangian
      (programPT06SecondOrderSecondMultiIndex first second)
  have hFirstTotal : ContDiff Real ∞
      (programPT06ThroatSpatialLocalFunctionTotalDerivative second
        (programPT06SecondOrderLocalVerticalPartialTwo
          localLagrangian first second)) :=
    programPT06ThroatSpatialLocalFunctionTotalDerivative_contDiff_top
      _ hPartial second
  have hPartialLift : ContDiff Real ∞
      (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
        (programPT06SecondOrderLocalVerticalPartialTwo
          localLagrangian first second)) :=
    programPT06AmbientLocalFunctionLift_contDiff
      (by omega : 2 ≤ 4) _ hPartial
  have hFirstTotalLift : ContDiff Real ∞
      (programPT06AmbientLocalFunctionLift (by omega : 3 ≤ 4)
        (programPT06ThroatSpatialLocalFunctionTotalDerivative second
          (programPT06SecondOrderLocalVerticalPartialTwo
            localLagrangian first second))) :=
    programPT06AmbientLocalFunctionLift_contDiff
      (by omega : 3 ≤ 4) _ hFirstTotal
  rw [programPT06SecondOrderMultiindexVerticalPartial_eq_lift
    localLagrangian (hLagrangian.differentiable (by simp))]
  change
    programPT06AmbientMultiindexTotalDerivative 4
        (throatSpatialCoordinateMultiIndex first +
          throatSpatialCoordinateMultiIndex second)
        (programPT06AmbientLocalFunctionLift (by omega : 2 ≤ 4)
          (programPT06SecondOrderLocalVerticalPartialTwo
            localLagrangian first second)) jet = _
  rw [programPT06AmbientMultiindexTotalDerivative_add_coordinate 4
    (throatSpatialCoordinateMultiIndex first) second _ hPartialLift]
  rw [programPT06AmbientLocalFunctionLift_totalDerivative
    (by omega : 2 + 1 ≤ 4) second _
    (hPartial.differentiable (by simp))]
  rw [show throatSpatialCoordinateMultiIndex first =
      0 + throatSpatialCoordinateMultiIndex first by simp]
  rw [programPT06AmbientMultiindexTotalDerivative_add_coordinate 4 0 first
    _ hFirstTotalLift]
  rw [programPT06AmbientMultiindexTotalDerivative_zero_index]
  rw [programPT06AmbientLocalFunctionLift_totalDerivative
    (by omega : 3 + 1 ≤ 4) first _
    (hFirstTotal.differentiable (by simp))]
  rfl

private def programPT06SecondOrderMultiindexEulerSummand
    (localLagrangian : SpatialJet Fiber 2 → Real)
    (jet : SpatialJet Fiber 4) (index : ThroatSpatialTruncatedIndex 2) :
    Fiber →L[Real] Real :=
  ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
    programPT06AmbientMultiindexTotalDerivative 4 index.1
      (programPT06MultiindexLocalVerticalPartial 2 localLagrangian index) jet

@[simp] private theorem programPT06SecondOrderMultiindexEulerSummand_zero
    (localLagrangian : SpatialJet Fiber 2 → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (jet : SpatialJet Fiber 4) :
    programPT06SecondOrderMultiindexEulerSummand localLagrangian jet
        programPT06SecondOrderZeroMultiIndex =
      programPT06SecondOrderLocalVerticalPartialZero localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) := by
  rw [programPT06SecondOrderMultiindexEulerSummand,
    programPT06SecondOrderMultiindexDerivative_zero
      localLagrangian hLagrangian jet]
  simp [programPT06SecondOrderZeroMultiIndex]

@[simp] private theorem programPT06SecondOrderMultiindexEulerSummand_one
    (localLagrangian : SpatialJet Fiber 2 → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (direction : Fin 3) (jet : SpatialJet Fiber 4) :
    programPT06SecondOrderMultiindexEulerSummand localLagrangian jet
        (programPT06SecondOrderFirstMultiIndex direction) =
      -programPT06SecondOrderLocalEulerFirstTotalTerm
        localLagrangian direction
        (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet) := by
  rw [programPT06SecondOrderMultiindexEulerSummand,
    programPT06SecondOrderMultiindexDerivative_one
      localLagrangian hLagrangian direction jet]
  simp [programPT06SecondOrderFirstMultiIndex,
    throatSpatialMultiIndexOrder_coordinateMultiIndex]

@[simp] private theorem programPT06SecondOrderMultiindexEulerSummand_two
    (localLagrangian : SpatialJet Fiber 2 → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (first second : Fin 3) (jet : SpatialJet Fiber 4) :
    programPT06SecondOrderMultiindexEulerSummand localLagrangian jet
        (programPT06SecondOrderSecondMultiIndex first second) =
      programPT06SecondOrderLocalEulerSecondTotalTerm
        localLagrangian first second jet := by
  rw [programPT06SecondOrderMultiindexEulerSummand,
    programPT06SecondOrderMultiindexDerivative_two
      localLagrangian hLagrangian first second jet]
  simp [programPT06SecondOrderSecondMultiIndex,
    throatSpatialMultiIndexOrder_add,
    throatSpatialMultiIndexOrder_coordinateMultiIndex]

/-- The order-two generic multi-index Euler operator is exactly Gate880. -/
theorem programPT06MultiindexLocalEuler_two_eq_secondOrderLocalEuler
    (localLagrangian : SpatialJet Fiber 2 → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (jet : SpatialJet Fiber 4) :
    programPT06MultiindexLocalEuler 2 localLagrangian jet =
      programPT06SecondOrderLocalEuler localLagrangian jet := by
  change
    (∑ index : ThroatSpatialTruncatedIndex 2,
      programPT06SecondOrderMultiindexEulerSummand
        localLagrangian jet index) = _
  rw [programPT06SecondOrderIndexSum_eq_weightedCoordinates]
  simp_rw [programPT06SecondOrderMultiindexEulerSummand_zero
    localLagrangian hLagrangian jet,
    programPT06SecondOrderMultiindexEulerSummand_one
      localLagrangian hLagrangian,
    programPT06SecondOrderMultiindexEulerSummand_two
      localLagrangian hLagrangian]
  rw [programPT06SecondOrderLocalEuler_formula]
  simp only [Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Vanishing of the generic order-two Euler expression is equivalent to
vanishing of the Gate880 expression. -/
theorem programPT06MultiindexLocalEuler_two_eq_zero_iff
    (localLagrangian : SpatialJet Fiber 2 → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (jet : SpatialJet Fiber 4) :
    programPT06MultiindexLocalEuler 2 localLagrangian jet = 0 ↔
      programPT06SecondOrderLocalEuler localLagrangian jet = 0 := by
  rw [programPT06MultiindexLocalEuler_two_eq_secondOrderLocalEuler
    localLagrangian hLagrangian jet]

end
end P0EFTJanusProgramPT06SecondOrderMultiindexEulerComparison4D
end JanusFormal
