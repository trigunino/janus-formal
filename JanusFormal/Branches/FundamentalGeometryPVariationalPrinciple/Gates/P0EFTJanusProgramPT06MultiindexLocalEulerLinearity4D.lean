import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientLocalFunctionLiftNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientMultiindexTotalDerivativeCommutation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D

/-!
# Linearity of the multi-index local Euler operator

The double-order lift, its vertical partials, and fixed-ambient
multi-index total derivatives preserve finite linear combinations of smooth
local functions.  Consequently the generic local Euler operator is linear
and annihilates constant densities.

No horizontal-divergence soundness is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06MultiindexLocalEulerLinearity4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D
open P0EFTJanusProgramPT06AmbientLocalFunctionLiftNaturality4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u v

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
variable {Target : Type v} [NormedAddCommGroup Target] [NormedSpace Real Target]

private abbrev SpatialJet (Fiber : Type u) (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

/-- The double-order lift of a smooth local density is smooth. -/
theorem programPT06LocalDensityDoubleOrderLift_contDiff
    (order : Nat) (localLagrangian : SpatialJet Fiber order → Real)
    (hLocalLagrangian : ContDiff Real ∞ localLagrangian) :
    ContDiff Real ∞
      (programPT06LocalDensityDoubleOrderLift order localLagrangian) := by
  exact hLocalLagrangian.comp
    (programPT06TruncatedJetRestrictionContinuousLinearMap
      (Fiber := Fiber) (by omega : order ≤ order + order)).contDiff

@[simp] theorem programPT06LocalDensityDoubleOrderLift_add
    (order : Nat) (first second : SpatialJet Fiber order → Real) :
    programPT06LocalDensityDoubleOrderLift order (first + second) =
      programPT06LocalDensityDoubleOrderLift order first +
        programPT06LocalDensityDoubleOrderLift order second := by
  rfl

@[simp] theorem programPT06LocalDensityDoubleOrderLift_const_smul
    (order : Nat) (scalar : Real)
    (localLagrangian : SpatialJet Fiber order → Real) :
    programPT06LocalDensityDoubleOrderLift order
        (fun jet ↦ scalar • localLagrangian jet) =
      fun jet ↦ scalar •
        programPT06LocalDensityDoubleOrderLift order localLagrangian jet := by
  rfl

/-- Every indexed vertical partial of a smooth lifted density is smooth. -/
theorem programPT06MultiindexLocalVerticalPartial_contDiff
    (order : Nat) (localLagrangian : SpatialJet Fiber order → Real)
    (hLocalLagrangian : ContDiff Real ∞ localLagrangian)
    (index : ThroatSpatialTruncatedIndex order) :
    ContDiff Real ∞
      (programPT06MultiindexLocalVerticalPartial
        order localLagrangian index) := by
  change ContDiff Real ∞
    (fun jet ↦ programPT06ThroatSpatialVerticalPartialDerivative
      (programPT06LocalDensityDoubleOrderLift order localLagrangian) jet
      (programPT06TruncatedIndexOfLE
        (by omega : order ≤ order + order) index))
  exact programPT06ThroatSpatialVerticalPartialDerivative_contDiff_top
    (programPT06LocalDensityDoubleOrderLift order localLagrangian)
    (programPT06LocalDensityDoubleOrderLift_contDiff
      order localLagrangian hLocalLagrangian)
    (programPT06TruncatedIndexOfLE
      (by omega : order ≤ order + order) index)

/-- Vertical partials of the lifted density preserve addition. -/
theorem programPT06MultiindexLocalVerticalPartial_add
    (order : Nat) (first second : SpatialJet Fiber order → Real)
    (hFirst : ContDiff Real ∞ first)
    (hSecond : ContDiff Real ∞ second)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06MultiindexLocalVerticalPartial order (first + second) index =
      programPT06MultiindexLocalVerticalPartial order first index +
        programPT06MultiindexLocalVerticalPartial order second index := by
  have hFirstLift : Differentiable Real
      (programPT06LocalDensityDoubleOrderLift order first) :=
    (programPT06LocalDensityDoubleOrderLift_contDiff
      order first hFirst).differentiable (by simp)
  have hSecondLift : Differentiable Real
      (programPT06LocalDensityDoubleOrderLift order second) :=
    (programPT06LocalDensityDoubleOrderLift_contDiff
      order second hSecond).differentiable (by simp)
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  let injection := programPT06ThroatSpatialJetCoordinateInjection
    (programPT06TruncatedIndexOfLE
      (by omega : order ≤ order + order) index) variation
  have hDerivative := fderiv_add (hFirstLift jet) (hSecondLift jet)
  have hPoint := congrArg (fun derivative ↦ derivative injection) hDerivative
  change
    fderiv Real
        (fun candidate ↦
          programPT06LocalDensityDoubleOrderLift order first candidate +
            programPT06LocalDensityDoubleOrderLift order second candidate)
        jet injection =
      fderiv Real (programPT06LocalDensityDoubleOrderLift order first)
          jet injection +
        fderiv Real (programPT06LocalDensityDoubleOrderLift order second)
          jet injection
  convert hPoint using 1 <;> rfl

/-- Vertical partials of the lifted density preserve constant scalar
multiplication. -/
theorem programPT06MultiindexLocalVerticalPartial_const_smul
    (order : Nat) (scalar : Real)
    (localLagrangian : SpatialJet Fiber order → Real)
    (hLocalLagrangian : ContDiff Real ∞ localLagrangian)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06MultiindexLocalVerticalPartial order
        (fun jet ↦ scalar • localLagrangian jet) index =
      fun jet ↦ scalar •
        programPT06MultiindexLocalVerticalPartial
          order localLagrangian index jet := by
  have hLift : Differentiable Real
      (programPT06LocalDensityDoubleOrderLift order localLagrangian) :=
    (programPT06LocalDensityDoubleOrderLift_contDiff
      order localLagrangian hLocalLagrangian).differentiable (by simp)
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  let injection := programPT06ThroatSpatialJetCoordinateInjection
    (programPT06TruncatedIndexOfLE
      (by omega : order ≤ order + order) index) variation
  have hDerivative := ((hLift jet).hasFDerivAt.const_smul scalar).fderiv
  have hPoint := congrArg (fun derivative ↦ derivative injection) hDerivative
  change
    fderiv Real
        (fun candidate ↦ scalar •
          programPT06LocalDensityDoubleOrderLift
            order localLagrangian candidate) jet injection =
      scalar •
        fderiv Real (programPT06LocalDensityDoubleOrderLift
          order localLagrangian) jet injection
  convert hPoint using 1 <;> rfl

@[simp] theorem programPT06MultiindexLocalVerticalPartial_const
    (order : Nat) (constant : Real)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06MultiindexLocalVerticalPartial
        (Fiber := Fiber) order (fun _ ↦ constant) index = 0 := by
  have hLift :
      programPT06LocalDensityDoubleOrderLift
          (Fiber := Fiber) order (fun _ ↦ constant) =
        (fun _ : SpatialJet Fiber (order + order) ↦ constant) := by
    funext jet
    rfl
  funext jet
  rw [show programPT06MultiindexLocalVerticalPartial
      (Fiber := Fiber) order (fun _ ↦ constant) index jet =
        programPT06ThroatSpatialVerticalPartialDerivative
          (programPT06LocalDensityDoubleOrderLift
            (Fiber := Fiber) order (fun _ ↦ constant)) jet
          (programPT06TruncatedIndexOfLE
            (by omega : order ≤ order + order) index) by rfl,
    hLift]
  simp [
    programPT06ThroatSpatialVerticalPartialDerivative]

/-- Fixed-ambient multi-index total derivatives preserve addition on smooth
functions. -/
theorem programPT06AmbientMultiindexTotalDerivative_add
    (order : Nat) (index : ThroatSpatialMultiIndex)
    (first second : SpatialJet Fiber order → Target)
    (hFirst : ContDiff Real ∞ first)
    (hSecond : ContDiff Real ∞ second) :
    programPT06AmbientMultiindexTotalDerivative order index
        (first + second) =
      programPT06AmbientMultiindexTotalDerivative order index first +
        programPT06AmbientMultiindexTotalDerivative order index second := by
  unfold programPT06AmbientMultiindexTotalDerivative
  exact programPT06AmbientIteratedTotalDerivative_add
    order (programPT06ThroatSpatialMultiIndexDirectionWord index)
      first second hFirst hSecond

/-- Fixed-ambient multi-index total derivatives preserve constant scalar
multiplication on smooth functions. -/
theorem programPT06AmbientMultiindexTotalDerivative_const_smul
    (order : Nat) (index : ThroatSpatialMultiIndex) (scalar : Real)
    (localFunction : SpatialJet Fiber order → Target)
    (hLocalFunction : ContDiff Real ∞ localFunction) :
    programPT06AmbientMultiindexTotalDerivative order index
        (fun jet ↦ scalar • localFunction jet) =
      fun jet ↦ scalar •
        programPT06AmbientMultiindexTotalDerivative
          order index localFunction jet := by
  unfold programPT06AmbientMultiindexTotalDerivative
  exact programPT06AmbientIteratedTotalDerivative_const_smul
    order (programPT06ThroatSpatialMultiIndexDirectionWord index)
      scalar localFunction hLocalFunction

/-- The generic local Euler operator preserves addition on smooth local
densities. -/
theorem programPT06MultiindexLocalEuler_add
    (order : Nat) (first second : SpatialJet Fiber order → Real)
    (hFirst : ContDiff Real ∞ first)
    (hSecond : ContDiff Real ∞ second) :
    programPT06MultiindexLocalEuler order (first + second) =
      programPT06MultiindexLocalEuler order first +
        programPT06MultiindexLocalEuler order second := by
  have hFirstPartial (index : ThroatSpatialTruncatedIndex order) :
      ContDiff Real ∞
        (programPT06MultiindexLocalVerticalPartial order first index) :=
    programPT06MultiindexLocalVerticalPartial_contDiff
      order first hFirst index
  have hSecondPartial (index : ThroatSpatialTruncatedIndex order) :
      ContDiff Real ∞
        (programPT06MultiindexLocalVerticalPartial order second index) :=
    programPT06MultiindexLocalVerticalPartial_contDiff
      order second hSecond index
  funext jet
  simp only [programPT06MultiindexLocalEuler, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  rw [programPT06MultiindexLocalVerticalPartial_add
      order first second hFirst hSecond index,
    programPT06AmbientMultiindexTotalDerivative_add
      (order + order) index.1 _ _
        (hFirstPartial index) (hSecondPartial index),
    Pi.add_apply, smul_add]

/-- The generic local Euler operator preserves constant scalar
multiplication on smooth local densities. -/
theorem programPT06MultiindexLocalEuler_const_smul
    (order : Nat) (scalar : Real)
    (localLagrangian : SpatialJet Fiber order → Real)
    (hLocalLagrangian : ContDiff Real ∞ localLagrangian) :
    programPT06MultiindexLocalEuler order
        (fun jet ↦ scalar • localLagrangian jet) =
      fun jet ↦ scalar •
        programPT06MultiindexLocalEuler order localLagrangian jet := by
  have hPartial (index : ThroatSpatialTruncatedIndex order) :
      ContDiff Real ∞
        (programPT06MultiindexLocalVerticalPartial
          order localLagrangian index) :=
    programPT06MultiindexLocalVerticalPartial_contDiff
      order localLagrangian hLocalLagrangian index
  funext jet
  simp only [programPT06MultiindexLocalEuler]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [programPT06MultiindexLocalVerticalPartial_const_smul
      order scalar localLagrangian hLocalLagrangian index,
    programPT06AmbientMultiindexTotalDerivative_const_smul
      (order + order) index.1 scalar _ (hPartial index)]
  simp only [smul_smul, mul_comm]

/-- The generic local Euler operator changes sign under negation. -/
theorem programPT06MultiindexLocalEuler_neg
    (order : Nat) (localLagrangian : SpatialJet Fiber order → Real)
    (hLocalLagrangian : ContDiff Real ∞ localLagrangian) :
    programPT06MultiindexLocalEuler order (-localLagrangian) =
      -programPT06MultiindexLocalEuler order localLagrangian := by
  funext jet
  change
    programPT06MultiindexLocalEuler order
        (fun candidate ↦ -localLagrangian candidate) jet =
      -programPT06MultiindexLocalEuler order localLagrangian jet
  have hPoint := congrFun
    (programPT06MultiindexLocalEuler_const_smul
      order (-1 : Real) localLagrangian hLocalLagrangian) jet
  simpa only [neg_smul, one_smul] using hPoint

/-- The generic local Euler operator preserves subtraction on smooth local
densities. -/
theorem programPT06MultiindexLocalEuler_sub
    (order : Nat) (first second : SpatialJet Fiber order → Real)
    (hFirst : ContDiff Real ∞ first)
    (hSecond : ContDiff Real ∞ second) :
    programPT06MultiindexLocalEuler order (first - second) =
      programPT06MultiindexLocalEuler order first -
        programPT06MultiindexLocalEuler order second := by
  rw [sub_eq_add_neg, sub_eq_add_neg,
    programPT06MultiindexLocalEuler_add order first (-second)
      hFirst hSecond.neg,
    programPT06MultiindexLocalEuler_neg order second hSecond]

/-- Constant local densities have zero generic Euler operator. -/
@[simp] theorem programPT06MultiindexLocalEuler_const
    (order : Nat) (constant : Real) :
    programPT06MultiindexLocalEuler
        (Fiber := Fiber) order (fun _ ↦ constant) = 0 := by
  funext jet
  simp [programPT06MultiindexLocalEuler]

end
end P0EFTJanusProgramPT06MultiindexLocalEulerLinearity4D
end JanusFormal
