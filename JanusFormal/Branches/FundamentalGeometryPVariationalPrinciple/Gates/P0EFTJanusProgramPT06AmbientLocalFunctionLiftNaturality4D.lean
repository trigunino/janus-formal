import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D

/-!
# Naturality of ambient lifts of local jet functions

Local functions on a lower finite jet order pull back along continuous-linear
jet restriction.  Their Frechet and vertical derivatives therefore ignore
the added coordinates.  When one further jet order is available, this pullback
also intertwines the finite-order and fixed-ambient total derivatives.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AmbientLocalFunctionLiftNaturality4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped ContDiff
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderEulerHigherFrechetFormula4D
open P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u v

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
variable {Target : Type v} [NormedAddCommGroup Target] [NormedSpace Real Target]

private abbrev SpatialJet (Fiber : Type u) (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

/-- Pull a local function to any higher finite jet order. -/
def programPT06AmbientLocalFunctionLift
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (localFunction : SpatialJet Fiber lower → Target) :
    SpatialJet Fiber higher → Target :=
  localFunction ∘
    programPT06TruncatedJetRestrictionContinuousLinearMap
      (Fiber := Fiber) hOrder

omit [NormedAddCommGroup Target] [NormedSpace Real Target] in
@[simp] theorem programPT06AmbientLocalFunctionLift_apply
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (localFunction : SpatialJet Fiber lower → Target)
    (jet : SpatialJet Fiber higher) :
    programPT06AmbientLocalFunctionLift hOrder localFunction jet =
      localFunction (truncateThroatSpatialMultiindexJet hOrder jet) := by
  rfl

/-- Pullback along jet restriction preserves every differentiability order. -/
theorem programPT06AmbientLocalFunctionLift_contDiff
    {lower higher : Nat} {n : WithTop ℕ∞} (hOrder : lower ≤ higher)
    (localFunction : SpatialJet Fiber lower → Target)
    (hLocalFunction : ContDiff Real n localFunction) :
    ContDiff Real n
      (programPT06AmbientLocalFunctionLift hOrder localFunction) := by
  exact hLocalFunction.comp
    (programPT06TruncatedJetRestrictionContinuousLinearMap
      (Fiber := Fiber) hOrder).contDiff

/-- Frechet derivative of a lifted local function. -/
theorem programPT06AmbientLocalFunctionLift_fderiv
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (localFunction : SpatialJet Fiber lower → Target)
    (hLocalFunction : Differentiable Real localFunction)
    (jet : SpatialJet Fiber higher) :
    fderiv Real (programPT06AmbientLocalFunctionLift hOrder localFunction) jet =
      (fderiv Real localFunction
        (truncateThroatSpatialMultiindexJet hOrder jet)).comp
          (programPT06TruncatedJetRestrictionContinuousLinearMap
            (Fiber := Fiber) hOrder) := by
  exact ((hLocalFunction _).hasFDerivAt.comp jet
    (programPT06TruncatedJetRestrictionContinuousLinearMap
      (Fiber := Fiber) hOrder).hasFDerivAt).fderiv

/-- Evaluated Frechet derivative formula for a lifted local function. -/
theorem programPT06AmbientLocalFunctionLift_fderiv_apply
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (localFunction : SpatialJet Fiber lower → Target)
    (hLocalFunction : Differentiable Real localFunction)
    (jet tangent : SpatialJet Fiber higher) :
    fderiv Real (programPT06AmbientLocalFunctionLift hOrder localFunction)
        jet tangent =
      fderiv Real localFunction
        (truncateThroatSpatialMultiindexJet hOrder jet)
        (truncateThroatSpatialMultiindexJet hOrder tangent) := by
  rw [programPT06AmbientLocalFunctionLift_fderiv
    hOrder localFunction hLocalFunction]
  rfl

/-- Restricting the coordinate injection of an embedded lower-order index
recovers the original coordinate injection. -/
theorem programPT06TruncatedJetRestriction_coordinateInjection_ofLE
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (index : ThroatSpatialTruncatedIndex lower) (variation : Fiber) :
    truncateThroatSpatialMultiindexJet hOrder
        (programPT06ThroatSpatialJetCoordinateInjection
          (programPT06TruncatedIndexOfLE hOrder index) variation) =
      programPT06ThroatSpatialJetCoordinateInjection index variation := by
  funext coordinate
  change
    programPT06ThroatSpatialJetCoordinateInjection
        (programPT06TruncatedIndexOfLE hOrder index) variation
        (programPT06TruncatedIndexOfLE hOrder coordinate) =
      programPT06ThroatSpatialJetCoordinateInjection index variation coordinate
  by_cases hCoordinate : coordinate = index
  · subst coordinate
    rw [programPT06ThroatSpatialJetCoordinateInjection_same,
      programPT06ThroatSpatialJetCoordinateInjection_same]
  · have hEmbedded :
        programPT06TruncatedIndexOfLE hOrder coordinate ≠
          programPT06TruncatedIndexOfLE hOrder index := by
      intro hEqual
      apply hCoordinate
      apply Subtype.ext
      exact congrArg
        (fun embedded : ThroatSpatialTruncatedIndex higher => embedded.1)
        hEqual
    rw [programPT06ThroatSpatialJetCoordinateInjection_of_ne
        (programPT06TruncatedIndexOfLE hOrder index)
        (programPT06TruncatedIndexOfLE hOrder coordinate)
        hEmbedded variation,
      programPT06ThroatSpatialJetCoordinateInjection_of_ne
        index coordinate hCoordinate variation]

/-- The vertical derivative in an embedded lower-order coordinate is the
original vertical derivative. -/
theorem programPT06AmbientLocalFunctionLift_verticalPartial_ofLE
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (localFunction : SpatialJet Fiber lower → Target)
    (hLocalFunction : Differentiable Real localFunction)
    (jet : SpatialJet Fiber higher)
    (index : ThroatSpatialTruncatedIndex lower) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AmbientLocalFunctionLift hOrder localFunction) jet
        (programPT06TruncatedIndexOfLE hOrder index) =
      programPT06ThroatSpatialVerticalPartialDerivative localFunction
        (truncateThroatSpatialMultiindexJet hOrder jet) index := by
  apply ContinuousLinearMap.ext
  intro variation
  rw [programPT06ThroatSpatialVerticalPartialDerivative_apply,
    programPT06ThroatSpatialVerticalPartialDerivative_apply,
    programPT06AmbientLocalFunctionLift_fderiv_apply
      hOrder localFunction hLocalFunction]
  rw [programPT06TruncatedJetRestriction_coordinateInjection_ofLE]

/-- A coordinate strictly above the source order disappears under jet
restriction. -/
theorem programPT06TruncatedJetRestriction_coordinateInjection_eq_zero
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (index : ThroatSpatialTruncatedIndex higher)
    (hIndex : lower < throatSpatialMultiIndexOrder index.1)
    (variation : Fiber) :
    truncateThroatSpatialMultiindexJet hOrder
        (programPT06ThroatSpatialJetCoordinateInjection index variation) = 0 := by
  funext coordinate
  have hEmbedded : programPT06TruncatedIndexOfLE hOrder coordinate ≠ index := by
    intro hEqual
    have hValue : coordinate.1 = index.1 := congrArg Subtype.val hEqual
    have hIndexLe : throatSpatialMultiIndexOrder index.1 ≤ lower := by
      simpa only [← hValue] using coordinate.2
    exact (Nat.not_le_of_gt hIndex) hIndexLe
  exact programPT06ThroatSpatialJetCoordinateInjection_of_ne
    index (programPT06TruncatedIndexOfLE hOrder coordinate)
    hEmbedded variation

/-- A lifted local function has zero vertical derivative in every genuinely
higher-order coordinate. -/
theorem programPT06AmbientLocalFunctionLift_verticalPartial_eq_zero
    {lower higher : Nat} (hOrder : lower ≤ higher)
    (localFunction : SpatialJet Fiber lower → Target)
    (hLocalFunction : Differentiable Real localFunction)
    (jet : SpatialJet Fiber higher)
    (index : ThroatSpatialTruncatedIndex higher)
    (hIndex : lower < throatSpatialMultiIndexOrder index.1) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AmbientLocalFunctionLift hOrder localFunction) jet index =
      0 := by
  apply ContinuousLinearMap.ext
  intro variation
  rw [programPT06ThroatSpatialVerticalPartialDerivative_apply,
    programPT06AmbientLocalFunctionLift_fderiv_apply
      hOrder localFunction hLocalFunction,
    programPT06TruncatedJetRestriction_coordinateInjection_eq_zero
      hOrder index hIndex]
  simp

/-- Below the ambient boundary, restricting one fixed-ambient shift gives the
finite-order formal total derivative of the restricted jet. -/
theorem programPT06TruncateTruncatedJetShift
    {lower higher : Nat} (hOrder : lower + 1 ≤ higher)
    (direction : Fin 3) (jet : SpatialJet Fiber higher) :
    truncateThroatSpatialMultiindexJet (by omega : lower ≤ higher)
        (programPT06TruncatedJetShiftContinuousLinearMap
          (Fiber := Fiber) higher direction jet) =
      throatSpatialTotalDerivative direction
        (truncateThroatSpatialMultiindexJet hOrder jet) := by
  funext index
  change
    programPT06TruncatedJetShiftContinuousLinearMap
        (Fiber := Fiber) higher direction jet
        (programPT06TruncatedIndexOfLE
          (by omega : lower ≤ higher) index) =
      jet ⟨index.1 + throatSpatialCoordinateMultiIndex direction, by
        rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
        omega⟩
  rw [programPT06TruncatedJetShiftContinuousLinearMap_apply]
  have hShift : throatSpatialMultiIndexOrder
      (index.1 + throatSpatialCoordinateMultiIndex direction) ≤ higher := by
    rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
    omega
  simp only [programPT06TruncatedIndexOfLE_value]
  rw [dif_pos hShift]

/-- Pullback to a sufficiently high ambient order intertwines the native
one-order total derivative with the fixed-ambient total derivative. -/
theorem programPT06AmbientLocalFunctionLift_totalDerivative
    {lower higher : Nat} (hOrder : lower + 1 ≤ higher)
    (direction : Fin 3)
    (localFunction : SpatialJet Fiber lower → Target)
    (hLocalFunction : Differentiable Real localFunction) :
    programPT06AmbientLocalFunctionTotalDerivative higher direction
        (programPT06AmbientLocalFunctionLift
          (by omega : lower ≤ higher) localFunction) =
      programPT06AmbientLocalFunctionLift hOrder
        (programPT06ThroatSpatialLocalFunctionTotalDerivative
          direction localFunction) := by
  funext jet
  rw [programPT06AmbientLocalFunctionLift_apply,
    programPT06ThroatSpatialLocalFunctionTotalDerivative_apply]
  unfold programPT06AmbientLocalFunctionTotalDerivative
  rw [programPT06AmbientLocalFunctionLift_fderiv_apply
    (by omega : lower ≤ higher) localFunction hLocalFunction]
  rw [programPT06TruncateTruncatedJetShift hOrder direction jet]
  rw [programPT06TruncateThroatSpatialMultiindexJet_trans]

end
end P0EFTJanusProgramPT06AmbientLocalFunctionLiftNaturality4D
end JanusFormal
