import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderEulerHigherFrechetFormula4D

/-!
# Multi-index total derivatives and local Euler operators

This gate gives an order-independent local Euler carrier on the genuine
spatial Finsupp jet tower.  A local function of order `r` is pulled to the
fixed ambient jet `J^(2r)`.  Formal shifts are continuous-linear
endomorphisms of that ambient jet, so their iterates have a uniform type.

The generic Euler operator sums once over each genuine multi-index, avoiding
the ordered-pair half-weights used by the specialized Gate880 presentation.
No horizontal-divergence soundness or comparison with Gate880 is asserted
until the required multi-index telescoping and regrouping are proved.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u v

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
variable {Target : Type v} [NormedAddCommGroup Target] [NormedSpace Real Target]

private abbrev SpatialJet (Fiber : Type u) (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

/-- Continuous-linear restriction between any two finite spatial jet orders. -/
def programPT06TruncatedJetRestrictionContinuousLinearMap
    {lower higher : Nat} (hOrder : lower ≤ higher) :
    SpatialJet Fiber higher →L[Real] SpatialJet Fiber lower :=
  ContinuousLinearMap.pi fun index : ThroatSpatialTruncatedIndex lower =>
    ContinuousLinearMap.proj ⟨index.1, index.2.trans hOrder⟩

@[simp] theorem programPT06TruncatedJetRestrictionContinuousLinearMap_apply
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (jet : SpatialJet Fiber higher) :
    programPT06TruncatedJetRestrictionContinuousLinearMap
        (Fiber := Fiber) hOrder jet =
      truncateThroatSpatialMultiindexJet hOrder jet := by
  rfl

/-- Embed a bounded multi-index into a larger truncation. -/
def programPT06TruncatedIndexOfLE
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (index : ThroatSpatialTruncatedIndex lower) :
    ThroatSpatialTruncatedIndex higher :=
  ⟨index.1, index.2.trans hOrder⟩

@[simp] theorem programPT06TruncatedIndexOfLE_value
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (index : ThroatSpatialTruncatedIndex lower) :
    (programPT06TruncatedIndexOfLE hOrder index).1 = index.1 := by
  rfl

/-- The truncated formal shift on a fixed finite jet.  It reads the next
coordinate when that coordinate is still in the truncation and is zero on
the top-order boundary. -/
def programPT06TruncatedJetShiftContinuousLinearMap
    (order : Nat) (direction : Fin 3) :
    SpatialJet Fiber order →L[Real] SpatialJet Fiber order :=
  ContinuousLinearMap.pi fun index : ThroatSpatialTruncatedIndex order =>
    if hShift : throatSpatialMultiIndexOrder
        (index.1 + throatSpatialCoordinateMultiIndex direction) ≤ order then
      ContinuousLinearMap.proj
        ⟨index.1 + throatSpatialCoordinateMultiIndex direction, hShift⟩
    else
      0

@[simp] theorem programPT06TruncatedJetShiftContinuousLinearMap_apply
    (order : Nat) (direction : Fin 3) (jet : SpatialJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06TruncatedJetShiftContinuousLinearMap
        (Fiber := Fiber) order direction jet index =
      if hShift : throatSpatialMultiIndexOrder
          (index.1 + throatSpatialCoordinateMultiIndex direction) ≤ order then
        jet ⟨index.1 + throatSpatialCoordinateMultiIndex direction, hShift⟩
      else
        0 := by
  by_cases hShift : throatSpatialMultiIndexOrder
      (index.1 + throatSpatialCoordinateMultiIndex direction) <= order <;>
    simp [programPT06TruncatedJetShiftContinuousLinearMap, hShift]

/-- Fixed-order truncated shifts commute. -/
theorem programPT06TruncatedJetShiftContinuousLinearMap_comm
    (order : Nat) (first second : Fin 3) :
    (programPT06TruncatedJetShiftContinuousLinearMap
        (Fiber := Fiber) order first).comp
        (programPT06TruncatedJetShiftContinuousLinearMap
          (Fiber := Fiber) order second) =
      (programPT06TruncatedJetShiftContinuousLinearMap
        (Fiber := Fiber) order second).comp
        (programPT06TruncatedJetShiftContinuousLinearMap
          (Fiber := Fiber) order first) := by
  apply ContinuousLinearMap.ext
  intro jet
  funext index
  simp only [ContinuousLinearMap.comp_apply,
    programPT06TruncatedJetShiftContinuousLinearMap_apply]
  by_cases hTwo : throatSpatialMultiIndexOrder index.1 + 2 <= order
  · have hOne : throatSpatialMultiIndexOrder index.1 + 1 <= order := by
      omega
    have hFirst : throatSpatialMultiIndexOrder
        (index.1 + throatSpatialCoordinateMultiIndex first) <= order := by
      rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
      exact hOne
    have hSecond : throatSpatialMultiIndexOrder
        (index.1 + throatSpatialCoordinateMultiIndex second) <= order := by
      rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
      exact hOne
    have hFirstSecond : throatSpatialMultiIndexOrder
        ((index.1 + throatSpatialCoordinateMultiIndex first) +
          throatSpatialCoordinateMultiIndex second) <= order := by
      rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex,
        throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
      omega
    have hSecondFirst : throatSpatialMultiIndexOrder
        ((index.1 + throatSpatialCoordinateMultiIndex second) +
          throatSpatialCoordinateMultiIndex first) <= order := by
      rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex,
        throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
      omega
    simp only [dif_pos hFirst, dif_pos hSecond,
      dif_pos hFirstSecond, dif_pos hSecondFirst]
    apply congrArg jet
    apply Subtype.ext
    ac_rfl
  · by_cases hOne : throatSpatialMultiIndexOrder index.1 + 1 <= order
    · have hFirst : throatSpatialMultiIndexOrder
          (index.1 + throatSpatialCoordinateMultiIndex first) <= order := by
        rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
        exact hOne
      have hSecond : throatSpatialMultiIndexOrder
          (index.1 + throatSpatialCoordinateMultiIndex second) <= order := by
        rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
        exact hOne
      have hFirstSecond : Not (throatSpatialMultiIndexOrder
          ((index.1 + throatSpatialCoordinateMultiIndex first) +
            throatSpatialCoordinateMultiIndex second) <= order) := by
        rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex,
          throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
        omega
      have hSecondFirst : Not (throatSpatialMultiIndexOrder
          ((index.1 + throatSpatialCoordinateMultiIndex second) +
            throatSpatialCoordinateMultiIndex first) <= order) := by
        rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex,
          throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
        omega
      simp only [dif_pos hFirst, dif_pos hSecond,
        dif_neg hFirstSecond, dif_neg hSecondFirst]
    · have hFirst : Not (throatSpatialMultiIndexOrder
          (index.1 + throatSpatialCoordinateMultiIndex first) <= order) := by
        rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
        exact hOne
      have hSecond : Not (throatSpatialMultiIndexOrder
          (index.1 + throatSpatialCoordinateMultiIndex second) <= order) := by
        rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
        exact hOne
      simp only [dif_neg hFirst, dif_neg hSecond]

/-- Formal total derivative of a local function on one fixed ambient jet.
The truncated shift keeps both the source and target function spaces fixed. -/
def programPT06AmbientLocalFunctionTotalDerivative
    (order : Nat) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Target) :
    SpatialJet Fiber order → Target :=
  fun jet =>
    fderiv Real localFunction jet
      (programPT06TruncatedJetShiftContinuousLinearMap
        (Fiber := Fiber) order direction jet)

@[simp] theorem programPT06AmbientLocalFunctionTotalDerivative_const
    (order : Nat) (direction : Fin 3) (constant : Target) :
    programPT06AmbientLocalFunctionTotalDerivative
        (Fiber := Fiber) order direction
        (fun _ : SpatialJet Fiber order => constant) = 0 := by
  funext jet
  simp [programPT06AmbientLocalFunctionTotalDerivative]

@[simp] theorem programPT06AmbientLocalFunctionTotalDerivative_zero
    (order : Nat) (direction : Fin 3) :
    programPT06AmbientLocalFunctionTotalDerivative
        (Fiber := Fiber) (Target := Target) order direction 0 = 0 := by
  exact programPT06AmbientLocalFunctionTotalDerivative_const
    (Fiber := Fiber) order direction 0

/-- The fixed-ambient total derivative preserves addition at differentiable
local functions. -/
theorem programPT06AmbientLocalFunctionTotalDerivative_add
    (order : Nat) (direction : Fin 3)
    (first second : SpatialJet Fiber order → Target)
    (hFirst : Differentiable Real first)
    (hSecond : Differentiable Real second) :
    programPT06AmbientLocalFunctionTotalDerivative
        order direction (first + second) =
      programPT06AmbientLocalFunctionTotalDerivative order direction first +
        programPT06AmbientLocalFunctionTotalDerivative order direction second := by
  funext jet
  let tangent := programPT06TruncatedJetShiftContinuousLinearMap
    (Fiber := Fiber) order direction jet
  have hDerivative := fderiv_add (hFirst jet) (hSecond jet)
  have hPoint := congrArg (fun derivative => derivative tangent) hDerivative
  simpa [programPT06AmbientLocalFunctionTotalDerivative, tangent] using hPoint

/-- The fixed-ambient total derivative preserves constant scalar
multiplication at differentiable local functions. -/
theorem programPT06AmbientLocalFunctionTotalDerivative_const_smul
    (order : Nat) (direction : Fin 3) (scalar : Real)
    (localFunction : SpatialJet Fiber order → Target)
    (hLocalFunction : Differentiable Real localFunction) :
    programPT06AmbientLocalFunctionTotalDerivative order direction
        (fun jet => scalar • localFunction jet) =
      fun jet => scalar •
        programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction jet := by
  funext jet
  let tangent := programPT06TruncatedJetShiftContinuousLinearMap
    (Fiber := Fiber) order direction jet
  have hDerivative :=
    ((hLocalFunction jet).hasFDerivAt.const_smul scalar).fderiv
  have hPoint := congrArg (fun derivative => derivative tangent) hDerivative
  change fderiv Real (scalar • localFunction) jet tangent =
    scalar • fderiv Real localFunction jet tangent
  exact hPoint

/-- Smoothness is preserved by one fixed-ambient total derivative. -/
theorem programPT06AmbientLocalFunctionTotalDerivative_contDiff
    (order : Nat) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Target)
    (hLocalFunction : ContDiff Real ∞ localFunction) :
    ContDiff Real ∞
      (programPT06AmbientLocalFunctionTotalDerivative
        order direction localFunction) := by
  have hGradient : ContDiff Real ∞ (fderiv Real localFunction) :=
    hLocalFunction.fderiv_right (m := ∞) (by simp)
  have hRestricted : ContDiff Real ∞
      (fun jet : SpatialJet Fiber order => fderiv Real localFunction jet) :=
    hGradient
  have hApplied := hRestricted.clm_apply
    (programPT06TruncatedJetShiftContinuousLinearMap
      (Fiber := Fiber) order direction).contDiff
  change ContDiff Real ∞
    (fun jet : SpatialJet Fiber order =>
      fderiv Real localFunction jet
        (programPT06TruncatedJetShiftContinuousLinearMap
          (Fiber := Fiber) order direction jet))
  exact hApplied

/-- Iterate fixed-ambient total derivatives along a list of directions. -/
def programPT06AmbientIteratedTotalDerivative
    (order : Nat) : List (Fin 3) →
    (SpatialJet Fiber order → Target) →
      (SpatialJet Fiber order → Target)
  | [], localFunction => localFunction
  | direction :: directions, localFunction =>
      programPT06AmbientIteratedTotalDerivative order directions
        (programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction)

@[simp] theorem programPT06AmbientIteratedTotalDerivative_nil
    (order : Nat) (localFunction : SpatialJet Fiber order → Target) :
    programPT06AmbientIteratedTotalDerivative order [] localFunction =
      localFunction := by
  rfl

@[simp] theorem programPT06AmbientIteratedTotalDerivative_cons
    (order : Nat) (direction : Fin 3) (directions : List (Fin 3))
    (localFunction : SpatialJet Fiber order → Target) :
    programPT06AmbientIteratedTotalDerivative order
        (direction :: directions) localFunction =
      programPT06AmbientIteratedTotalDerivative order directions
        (programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction) := by
  rfl

@[simp] theorem programPT06AmbientIteratedTotalDerivative_zero
    (order : Nat) (directions : List (Fin 3)) :
    programPT06AmbientIteratedTotalDerivative
        (Fiber := Fiber) (Target := Target) order directions 0 = 0 := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      simp [programPT06AmbientIteratedTotalDerivative, induction]

/-- Every finite total-derivative word preserves smoothness. -/
theorem programPT06AmbientIteratedTotalDerivative_contDiff
    (order : Nat) (directions : List (Fin 3))
    (localFunction : SpatialJet Fiber order → Target)
    (hLocalFunction : ContDiff Real ∞ localFunction) :
    ContDiff Real ∞
      (programPT06AmbientIteratedTotalDerivative
        order directions localFunction) := by
  induction directions generalizing localFunction with
  | nil => exact hLocalFunction
  | cons direction directions induction =>
      exact induction _
        (programPT06AmbientLocalFunctionTotalDerivative_contDiff
          order direction localFunction hLocalFunction)

/-- Iterated total derivatives preserve addition on smooth functions. -/
theorem programPT06AmbientIteratedTotalDerivative_add
    (order : Nat) (directions : List (Fin 3))
    (first second : SpatialJet Fiber order → Target)
    (hFirst : ContDiff Real ∞ first)
    (hSecond : ContDiff Real ∞ second) :
    programPT06AmbientIteratedTotalDerivative order directions
        (first + second) =
      programPT06AmbientIteratedTotalDerivative order directions first +
        programPT06AmbientIteratedTotalDerivative order directions second := by
  induction directions generalizing first second with
  | nil => rfl
  | cons direction directions induction =>
      rw [programPT06AmbientIteratedTotalDerivative_cons,
        programPT06AmbientLocalFunctionTotalDerivative_add
          order direction first second
          (hFirst.differentiable (by simp))
          (hSecond.differentiable (by simp))]
      exact induction _ _
        (programPT06AmbientLocalFunctionTotalDerivative_contDiff
          order direction first hFirst)
        (programPT06AmbientLocalFunctionTotalDerivative_contDiff
          order direction second hSecond)

/-- Iterated total derivatives preserve scalar multiplication on smooth
functions. -/
theorem programPT06AmbientIteratedTotalDerivative_const_smul
    (order : Nat) (directions : List (Fin 3)) (scalar : Real)
    (localFunction : SpatialJet Fiber order → Target)
    (hLocalFunction : ContDiff Real ∞ localFunction) :
    programPT06AmbientIteratedTotalDerivative order directions
        (fun jet => scalar • localFunction jet) =
      fun jet => scalar •
        programPT06AmbientIteratedTotalDerivative
          order directions localFunction jet := by
  induction directions generalizing localFunction with
  | nil => rfl
  | cons direction directions induction =>
      rw [programPT06AmbientIteratedTotalDerivative_cons,
        programPT06AmbientLocalFunctionTotalDerivative_const_smul
          order direction scalar localFunction
          (hLocalFunction.differentiable (by simp))]
      exact induction _
        (programPT06AmbientLocalFunctionTotalDerivative_contDiff
          order direction localFunction hLocalFunction)

/-- Canonical sorted direction word carried by a genuine spatial
multi-index. -/
def programPT06ThroatSpatialMultiIndexDirectionWord
    (index : ThroatSpatialMultiIndex) : List (Fin 3) :=
  (Finsupp.toMultiset index).sort (fun first second => first ≤ second)

/-- Iterate total derivatives with the multiplicities of one spatial
multi-index. -/
def programPT06AmbientMultiindexTotalDerivative
    (order : Nat) (index : ThroatSpatialMultiIndex)
    (localFunction : SpatialJet Fiber order → Target) :
    SpatialJet Fiber order → Target :=
  programPT06AmbientIteratedTotalDerivative order
    (programPT06ThroatSpatialMultiIndexDirectionWord index) localFunction

@[simp] theorem programPT06AmbientMultiindexTotalDerivative_zero_index
    (order : Nat) (localFunction : SpatialJet Fiber order → Target) :
    programPT06AmbientMultiindexTotalDerivative order 0 localFunction =
      localFunction := by
  simp [programPT06AmbientMultiindexTotalDerivative,
    programPT06ThroatSpatialMultiIndexDirectionWord]

@[simp] theorem programPT06AmbientMultiindexTotalDerivative_zero
    (order : Nat) (index : ThroatSpatialMultiIndex) :
    programPT06AmbientMultiindexTotalDerivative
        (Fiber := Fiber) (Target := Target) order index 0 = 0 := by
  simp [programPT06AmbientMultiindexTotalDerivative]

/-- Pull an order-`r` local density to the fixed ambient jet `J^(2r)`. -/
def programPT06LocalDensityDoubleOrderLift
    (order : Nat) (localLagrangian : SpatialJet Fiber order → Real) :
    SpatialJet Fiber (order + order) → Real :=
  localLagrangian ∘
    programPT06TruncatedJetRestrictionContinuousLinearMap
      (Fiber := Fiber) (by omega : order ≤ order + order)

/-- Vertical partial of the lifted density in one genuine order-`r`
multi-index coordinate. -/
def programPT06MultiindexLocalVerticalPartial
    (order : Nat) (localLagrangian : SpatialJet Fiber order → Real)
    (index : ThroatSpatialTruncatedIndex order) :
    SpatialJet Fiber (order + order) → (Fiber →L[Real] Real) :=
  fun jet =>
    programPT06ThroatSpatialVerticalPartialDerivative
      (programPT06LocalDensityDoubleOrderLift order localLagrangian) jet
      (programPT06TruncatedIndexOfLE
        (by omega : order ≤ order + order) index)

/-- Generic autonomous local Euler operator of order `r`, evaluated on
`J^(2r)`.  Each multi-index occurs exactly once. -/
def programPT06MultiindexLocalEuler
    (order : Nat) (localLagrangian : SpatialJet Fiber order → Real) :
    SpatialJet Fiber (order + order) → (Fiber →L[Real] Real) :=
  fun jet =>
    ∑ index : ThroatSpatialTruncatedIndex order,
      ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
        programPT06AmbientMultiindexTotalDerivative
          (order + order) index.1
          (programPT06MultiindexLocalVerticalPartial
            order localLagrangian index) jet

@[simp] theorem programPT06MultiindexLocalVerticalPartial_zero
    (order : Nat) (index : ThroatSpatialTruncatedIndex order) :
    programPT06MultiindexLocalVerticalPartial
        (Fiber := Fiber) order 0 index = 0 := by
  funext jet
  simp [programPT06MultiindexLocalVerticalPartial,
    programPT06LocalDensityDoubleOrderLift,
    programPT06ThroatSpatialVerticalPartialDerivative]

@[simp] theorem programPT06MultiindexLocalEuler_zero
    (order : Nat) :
    programPT06MultiindexLocalEuler
        (Fiber := Fiber) order 0 = 0 := by
  funext jet
  simp [programPT06MultiindexLocalEuler]

end
end P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D
end JanusFormal
