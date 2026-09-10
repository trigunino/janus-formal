import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderEulerHigherFrechetFormula4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderJetRadialDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DiagonalHomogeneousEulerIdentity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DiagonalPolynomialHigherFrechetDerivative4D

/-!
# Radial Cartan homotopy for second-order local functions

This gate constructs the order-two radial Cartan current on genuine spatial
jets.  Its horizontal divergence splits the radial Frechet derivative into
the value-slot Euler contraction and the remaining jet-coordinate terms.
For a nonconstant diagonal homogeneous density, division by its degree gives
an explicit horizontal primitive whenever its second-order Euler expression
vanishes.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D

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
open P0EFTJanusProgramPT06SecondOrderJetRadialDecomposition4D
open P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D
open P0EFTJanusProgramPT06DiagonalPolynomialHigherFrechetDerivative4D
open P0EFTJanusProgramPT06DiagonalHomogeneousEulerIdentity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u v

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
variable {Target : Type v} [NormedAddCommGroup Target] [NormedSpace Real Target]

private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- Autonomous horizontal currents whose components depend on third jets. -/
abbrev ProgramPT06SecondOrderHorizontalCurrent4D :=
  Fin 3 → ThirdJet (Fiber := Fiber) → Real

/-- Genuine horizontal differential of an order-two current. -/
def programPT06SecondOrderHorizontalCurrentDH
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber)) : FourthJet (Fiber := Fiber) → Real :=
  fun jet => ∑ direction : Fin 3,
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
      (current direction) jet

private def programPT06ThroatSpatialJetCoordinateProjection
    {order : Nat} (index : ThroatSpatialTruncatedIndex order) :
    TruncatedThroatSpatialMultiindexJet Fiber order →L[Real] Fiber :=
  ContinuousLinearMap.proj index

@[simp] private theorem programPT06ThroatSpatialJetCoordinateProjection_apply
    {order : Nat} (index : ThroatSpatialTruncatedIndex order)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber order) :
    programPT06ThroatSpatialJetCoordinateProjection
        (Fiber := Fiber) index jet = jet index :=
  rfl

/-- Contract a covector-valued local function with one radial jet
coordinate. -/
def programPT06ThroatSpatialRadialContraction
    {order : Nat}
    (coefficient : TruncatedThroatSpatialMultiindexJet Fiber order →
      (Fiber →L[Real] Real))
    (index : ThroatSpatialTruncatedIndex order) :
    TruncatedThroatSpatialMultiindexJet Fiber order → Real :=
  fun jet => coefficient jet (jet index)

/-- Product rule for one formal total derivative of a radial coordinate
contraction. -/
theorem programPT06ThroatSpatialLocalFunctionTotalDerivative_radialContraction
    {order : Nat}
    (coefficient : TruncatedThroatSpatialMultiindexJet Fiber order →
      (Fiber →L[Real] Real))
    (hCoefficient : Differentiable Real coefficient)
    (index : ThroatSpatialTruncatedIndex order) (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (programPT06ThroatSpatialRadialContraction coefficient index) jet =
      coefficient
          (truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet)
          ((throatSpatialTotalDerivative direction jet) index) +
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
            coefficient jet
          ((truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet)
            index) := by
  let base := truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet
  let tangent := throatSpatialTotalDerivative direction jet
  let coordinate :=
    programPT06ThroatSpatialJetCoordinateProjection
      (Fiber := Fiber) index
  change
    fderiv Real (fun candidate => coefficient candidate (candidate index))
        base tangent =
      coefficient base (tangent index) +
        fderiv Real coefficient base tangent (base index)
  have hProduct := fderiv_clm_apply (hCoefficient base)
    coordinate.differentiableAt
  have hPoint := congrArg (fun derivative => derivative tangent) hProduct
  simpa [coordinate, programPT06ThroatSpatialJetCoordinateProjection] using
    hPoint

private theorem programPT06ThroatSpatialRadialContraction_differentiable
    {order : Nat}
    (coefficient : TruncatedThroatSpatialMultiindexJet Fiber order →
      (Fiber →L[Real] Real))
    (hCoefficient : Differentiable Real coefficient)
    (index : ThroatSpatialTruncatedIndex order) :
    Differentiable Real
      (programPT06ThroatSpatialRadialContraction coefficient index) := by
  let coordinate :=
    programPT06ThroatSpatialJetCoordinateProjection
      (Fiber := Fiber) index
  change Differentiable Real
    (fun jet => coefficient jet (jet index))
  simpa [coordinate, programPT06ThroatSpatialJetCoordinateProjection] using
    hCoefficient.clm_apply coordinate.differentiable

private def programPT06LiftSecondJetLocalFunction
    (localFunction : SecondJet (Fiber := Fiber) → Target) :
    ThirdJet (Fiber := Fiber) → Target :=
  fun jet => localFunction
    (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)

private def programPT06TruncateThirdJetContinuousLinearMap :
    ThirdJet (Fiber := Fiber) →L[Real] SecondJet (Fiber := Fiber) :=
  ContinuousLinearMap.pi fun index : ThroatSpatialTruncatedIndex 2 =>
    ContinuousLinearMap.proj
      ⟨index.1, index.2.trans (by omega : 2 ≤ 3)⟩

@[simp] private theorem
    programPT06TruncateThirdJetContinuousLinearMap_apply
    (jet : ThirdJet (Fiber := Fiber)) :
    programPT06TruncateThirdJetContinuousLinearMap (Fiber := Fiber) jet =
      truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet :=
  rfl

private def programPT06ThirdJetTotalDerivativeContinuousLinearMap
    (direction : Fin 3) :
    ThirdJet (Fiber := Fiber) →L[Real] SecondJet (Fiber := Fiber) :=
  ContinuousLinearMap.pi fun index : ThroatSpatialTruncatedIndex 2 =>
    ContinuousLinearMap.proj
      ⟨index.1 + throatSpatialCoordinateMultiIndex direction, by
        rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
        omega⟩

@[simp] private theorem
    programPT06ThirdJetTotalDerivativeContinuousLinearMap_apply
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    programPT06ThirdJetTotalDerivativeContinuousLinearMap
        (Fiber := Fiber) direction jet =
      throatSpatialTotalDerivative direction jet :=
  rfl

private theorem programPT06LiftSecondJetLocalFunction_differentiable
    (localFunction : SecondJet (Fiber := Fiber) → Target)
    (hLocalFunction : Differentiable Real localFunction) :
    Differentiable Real
      (programPT06LiftSecondJetLocalFunction localFunction) := by
  let truncate :=
    programPT06TruncateThirdJetContinuousLinearMap (Fiber := Fiber)
  have hLift :
      programPT06LiftSecondJetLocalFunction localFunction =
        localFunction ∘ (⇑truncate) := by
    funext jet
    simp [programPT06LiftSecondJetLocalFunction, truncate]
  rw [hLift]
  exact hLocalFunction.comp truncate.differentiable

private theorem
    programPT06ThroatSpatialLocalFunctionTotalDerivative_liftSecondJet
    (localFunction : SecondJet (Fiber := Fiber) → Target)
    (hLocalFunction : Differentiable Real localFunction)
    (direction : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (programPT06LiftSecondJetLocalFunction localFunction) jet =
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        localFunction
        (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet) := by
  let base :=
    truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet
  let truncate :=
    programPT06TruncateThirdJetContinuousLinearMap (Fiber := Fiber)
  have hLift :
      programPT06LiftSecondJetLocalFunction localFunction =
        localFunction ∘ (⇑truncate) := by
    funext candidate
    simp [programPT06LiftSecondJetLocalFunction, truncate]
  have hComposition : HasFDerivAt
      (programPT06LiftSecondJetLocalFunction localFunction)
      ((fderiv Real localFunction (truncate base)).comp truncate) base := by
    rw [hLift]
    exact (hLocalFunction (truncate base)).hasFDerivAt.comp base
      truncate.hasFDerivAt
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    direction _ jet _ hComposition,
    programPT06ThroatSpatialLocalFunctionTotalDerivative_apply]
  simp only [ContinuousLinearMap.comp_apply]
  dsimp only [truncate]
  simp only [programPT06TruncateThirdJetContinuousLinearMap_apply]
  rw [programPT06TruncateThroatSpatialTotalDerivative]

private def programPT06SecondOrderEulerRestriction
    (index : ThroatSpatialTruncatedIndex 2) :
    (SecondJet (Fiber := Fiber) →L[Real] Real) →L[Real]
      (Fiber →L[Real] Real) :=
  (ContinuousLinearMap.compL Real Fiber
    (SecondJet (Fiber := Fiber)) Real).flip
      (programPT06ThroatSpatialJetCoordinateInjection index)

private theorem programPT06SecondOrderVerticalPartial_contDiff_two
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (index : ThroatSpatialTruncatedIndex 2) :
    ContDiff Real 2
      (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
        localLagrangian jet index) := by
  have hGradient : ContDiff Real 2 (fderiv Real localLagrangian) :=
    hLagrangian.fderiv_right (m := 2) (by norm_num)
  have hRestricted :=
    (programPT06SecondOrderEulerRestriction
      (Fiber := Fiber) index).contDiff.comp hGradient
  simpa [programPT06SecondOrderEulerRestriction,
    programPT06ThroatSpatialVerticalPartialDerivative,
    Function.comp_def] using hRestricted

private theorem
    programPT06SecondOrderVerticalPartial_differentiable
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (index : ThroatSpatialTruncatedIndex 2) :
    Differentiable Real
      (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
        localLagrangian jet index) :=
  (programPT06SecondOrderVerticalPartial_contDiff_two
    localLagrangian hLagrangian index).differentiable (by norm_num)

private theorem
    programPT06SecondOrderVerticalPartialTotalDerivative_differentiable
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (index : ThroatSpatialTruncatedIndex 2) (direction : Fin 3) :
    Differentiable Real
      (programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
          localLagrangian jet index)) := by
  let coefficient := fun jet =>
    programPT06ThroatSpatialVerticalPartialDerivative
      localLagrangian jet index
  let truncate :=
    programPT06TruncateThirdJetContinuousLinearMap (Fiber := Fiber)
  let total :=
    programPT06ThirdJetTotalDerivativeContinuousLinearMap
      (Fiber := Fiber) direction
  have hCoefficient : ContDiff Real 2 coefficient :=
    programPT06SecondOrderVerticalPartial_contDiff_two
      localLagrangian hLagrangian index
  have hDerivative : ContDiff Real 1 (fderiv Real coefficient) :=
    hCoefficient.fderiv_right (m := 1) (by norm_num)
  have hComposed : ContDiff Real 1
      (fun jet : ThirdJet (Fiber := Fiber) =>
        fderiv Real coefficient (truncate jet)) :=
    hDerivative.comp truncate.contDiff
  have hApplied : ContDiff Real 1
      (fun jet : ThirdJet (Fiber := Fiber) =>
        fderiv Real coefficient (truncate jet) (total jet)) :=
    hComposed.clm_apply total.contDiff
  change Differentiable Real
    (fun jet : ThirdJet (Fiber := Fiber) =>
      fderiv Real coefficient (truncate jet) (total jet))
  exact hApplied.differentiable (by norm_num)

private def programPT06ThirdOrderZeroMultiIndex :
    ThroatSpatialTruncatedIndex 3 :=
  ⟨programPT06SecondOrderZeroMultiIndex.1, by
    exact programPT06SecondOrderZeroMultiIndex.2.trans (by omega)⟩

private def programPT06ThirdOrderFirstMultiIndex
    (direction : Fin 3) : ThroatSpatialTruncatedIndex 3 :=
  ⟨(programPT06SecondOrderFirstMultiIndex direction).1,
    (programPT06SecondOrderFirstMultiIndex direction).2.trans (by omega)⟩

/-- Radial contraction of the first-order vertical partial in one
direction. -/
def programPT06SecondOrderRadialFirstContraction
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (direction : Fin 3) : SecondJet (Fiber := Fiber) → Real :=
  programPT06ThroatSpatialRadialContraction
    (programPT06SecondOrderLocalVerticalPartialOne
      localLagrangian direction)
    programPT06SecondOrderZeroMultiIndex

/-- Radial contraction of a second-order vertical partial with the matching
first-jet coordinate. -/
def programPT06SecondOrderRadialSecondContraction
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (first second : Fin 3) : SecondJet (Fiber := Fiber) → Real :=
  programPT06ThroatSpatialRadialContraction
    (programPT06SecondOrderLocalVerticalPartialTwo
      localLagrangian first second)
    (programPT06SecondOrderFirstMultiIndex second)

/-- Radial contraction of the first prolongation of a second-order vertical
partial. -/
def programPT06SecondOrderRadialProlongedSecondContraction
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (first second : Fin 3) : ThirdJet (Fiber := Fiber) → Real :=
  programPT06ThroatSpatialRadialContraction
    (programPT06ThroatSpatialLocalFunctionTotalDerivative second
      (programPT06SecondOrderLocalVerticalPartialTwo
        localLagrangian first second))
    programPT06ThirdOrderZeroMultiIndex

private theorem programPT06SecondOrderRadialFirstContraction_differentiable
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (direction : Fin 3) :
    Differentiable Real
      (programPT06SecondOrderRadialFirstContraction
        localLagrangian direction) := by
  apply programPT06ThroatSpatialRadialContraction_differentiable
  change Differentiable Real
    (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
      localLagrangian jet
      (programPT06SecondOrderFirstMultiIndex direction))
  exact programPT06SecondOrderVerticalPartial_differentiable
    localLagrangian hLagrangian
    (programPT06SecondOrderFirstMultiIndex direction)

private theorem programPT06SecondOrderRadialSecondContraction_differentiable
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (first second : Fin 3) :
    Differentiable Real
      (programPT06SecondOrderRadialSecondContraction
        localLagrangian first second) := by
  apply programPT06ThroatSpatialRadialContraction_differentiable
  change Differentiable Real
    (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
      localLagrangian jet
      (programPT06SecondOrderSecondMultiIndex first second))
  exact programPT06SecondOrderVerticalPartial_differentiable
    localLagrangian hLagrangian
    (programPT06SecondOrderSecondMultiIndex first second)

private theorem
    programPT06SecondOrderRadialProlongedSecondContraction_differentiable
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (first second : Fin 3) :
    Differentiable Real
      (programPT06SecondOrderRadialProlongedSecondContraction
        localLagrangian first second) := by
  apply programPT06ThroatSpatialRadialContraction_differentiable
  change Differentiable Real
    (programPT06ThroatSpatialLocalFunctionTotalDerivative second
      (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
        localLagrangian jet
        (programPT06SecondOrderSecondMultiIndex first second)))
  exact programPT06SecondOrderVerticalPartialTotalDerivative_differentiable
    localLagrangian hLagrangian
    (programPT06SecondOrderSecondMultiIndex first second) second

omit [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] in
@[simp] private theorem
    programPT06ThroatSpatialTotalDerivative_zeroCoordinate
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    throatSpatialTotalDerivative direction jet
        programPT06SecondOrderZeroMultiIndex =
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)
        (programPT06SecondOrderFirstMultiIndex direction) := by
  apply congrArg jet
  apply Subtype.ext
  simp [programPT06SecondOrderZeroMultiIndex,
    programPT06SecondOrderFirstMultiIndex]

omit [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] in
@[simp] private theorem
    programPT06ThroatSpatialTotalDerivative_firstCoordinate
    (first second : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    throatSpatialTotalDerivative first jet
        (programPT06SecondOrderFirstMultiIndex second) =
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)
        (programPT06SecondOrderSecondMultiIndex first second) := by
  apply congrArg jet
  apply Subtype.ext
  change
    throatSpatialCoordinateMultiIndex second +
        throatSpatialCoordinateMultiIndex first =
      throatSpatialCoordinateMultiIndex first +
        throatSpatialCoordinateMultiIndex second
  exact add_comm _ _

omit [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] in
@[simp] private theorem
    programPT06ThroatSpatialFourthTotalDerivative_zeroCoordinate
    (direction : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    throatSpatialTotalDerivative direction jet
        programPT06ThirdOrderZeroMultiIndex =
      (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)
        (programPT06ThirdOrderFirstMultiIndex direction) := by
  apply congrArg jet
  apply Subtype.ext
  simp [programPT06ThirdOrderZeroMultiIndex,
    programPT06SecondOrderZeroMultiIndex,
    programPT06ThirdOrderFirstMultiIndex,
    programPT06SecondOrderFirstMultiIndex]

omit [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] in
@[simp] private theorem programPT06TruncateFourthJet_thirdOrderFirst
    (direction : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)
        (programPT06ThirdOrderFirstMultiIndex direction) =
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
        (programPT06SecondOrderFirstMultiIndex direction) := by
  apply congrArg jet
  apply Subtype.ext
  rfl

omit [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] in
@[simp] private theorem programPT06TruncateFourthJet_thirdOrderZero
    (jet : FourthJet (Fiber := Fiber)) :
    (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)
        programPT06ThirdOrderZeroMultiIndex =
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
        programPT06SecondOrderZeroMultiIndex := by
  apply congrArg jet
  apply Subtype.ext
  rfl

/-- Product rule for the first-order part of the radial Cartan current. -/
theorem programPT06SecondOrderRadialFirstContraction_totalDerivative
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (programPT06SecondOrderRadialFirstContraction
          localLagrangian direction) jet =
      programPT06SecondOrderLocalVerticalPartialOne
          localLagrangian direction
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)
          ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)
            (programPT06SecondOrderFirstMultiIndex direction)) +
        programPT06SecondOrderLocalEulerFirstTotalTerm
            localLagrangian direction jet
          ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)
            programPT06SecondOrderZeroMultiIndex) := by
  simpa [programPT06SecondOrderRadialFirstContraction,
    programPT06SecondOrderLocalEulerFirstTotalTerm] using
    (programPT06ThroatSpatialLocalFunctionTotalDerivative_radialContraction
      (programPT06SecondOrderLocalVerticalPartialOne
        localLagrangian direction)
      (by
        change Differentiable Real
          (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
            localLagrangian jet
            (programPT06SecondOrderFirstMultiIndex direction))
        exact programPT06SecondOrderVerticalPartial_differentiable
          localLagrangian hLagrangian
          (programPT06SecondOrderFirstMultiIndex direction))
      programPT06SecondOrderZeroMultiIndex direction jet)

/-- Product rule for the unprolonged second-order part of the radial current. -/
theorem programPT06SecondOrderRadialSecondContraction_totalDerivative
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (first second : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative first
        (programPT06SecondOrderRadialSecondContraction
          localLagrangian first second) jet =
      programPT06SecondOrderLocalVerticalPartialTwo
          localLagrangian first second
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)
          ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)
            (programPT06SecondOrderSecondMultiIndex first second)) +
        programPT06ThroatSpatialLocalFunctionTotalDerivative first
            (programPT06SecondOrderLocalVerticalPartialTwo
              localLagrangian first second) jet
          ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)
            (programPT06SecondOrderFirstMultiIndex second)) := by
  simpa [programPT06SecondOrderRadialSecondContraction] using
    (programPT06ThroatSpatialLocalFunctionTotalDerivative_radialContraction
      (programPT06SecondOrderLocalVerticalPartialTwo
        localLagrangian first second)
      (by
        change Differentiable Real
          (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
            localLagrangian jet
            (programPT06SecondOrderSecondMultiIndex first second))
        exact programPT06SecondOrderVerticalPartial_differentiable
          localLagrangian hLagrangian
          (programPT06SecondOrderSecondMultiIndex first second))
      (programPT06SecondOrderFirstMultiIndex second) first jet)

/-- Product rule for the prolonged second-order part of the radial current. -/
theorem
    programPT06SecondOrderRadialProlongedSecondContraction_totalDerivative
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (first second : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative first
        (programPT06SecondOrderRadialProlongedSecondContraction
          localLagrangian first second) jet =
      programPT06ThroatSpatialLocalFunctionTotalDerivative second
          (programPT06SecondOrderLocalVerticalPartialTwo
            localLagrangian first second)
          (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)
          ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
            (programPT06SecondOrderFirstMultiIndex first)) +
        programPT06SecondOrderLocalEulerSecondTotalTerm
            localLagrangian first second jet
          ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
            programPT06SecondOrderZeroMultiIndex) := by
  rw [programPT06SecondOrderRadialProlongedSecondContraction,
    programPT06ThroatSpatialLocalFunctionTotalDerivative_radialContraction]
  · simp [programPT06SecondOrderLocalEulerSecondTotalTerm,
      programPT06TruncateThroatSpatialMultiindexJet_trans]
  · change Differentiable Real
      (programPT06ThroatSpatialLocalFunctionTotalDerivative second
        (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
          localLagrangian jet
          (programPT06SecondOrderSecondMultiIndex first second)))
    exact programPT06SecondOrderVerticalPartialTotalDerivative_differentiable
      localLagrangian hLagrangian
      (programPT06SecondOrderSecondMultiIndex first second) second

/-- The unscaled radial Cartan current in one throat direction. -/
def programPT06SecondOrderRadialCartanCurrentComponent
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (direction : Fin 3) : ThirdJet (Fiber := Fiber) → Real :=
  fun jet =>
    programPT06SecondOrderRadialFirstContraction
      localLagrangian direction
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) +
    ∑ second : Fin 3,
      programPT06SecondOrderEulerSymmetryWeight direction second •
        (programPT06SecondOrderRadialSecondContraction
            localLagrangian direction second
            (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) -
          programPT06SecondOrderRadialProlongedSecondContraction
            localLagrangian direction second jet)

/-- The three components of the unscaled radial Cartan current. -/
def programPT06SecondOrderRadialCartanCurrent
    (localLagrangian : SecondJet (Fiber := Fiber) → Real) :
    ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber) :=
  programPT06SecondOrderRadialCartanCurrentComponent localLagrangian

/-- The actual horizontal differential of the three radial Cartan-current
components. -/
def programPT06SecondOrderRadialCartanCurrentDH
    (localLagrangian : SecondJet (Fiber := Fiber) → Real) :
    FourthJet (Fiber := Fiber) → Real :=
  programPT06SecondOrderHorizontalCurrentDH
    (programPT06SecondOrderRadialCartanCurrent localLagrangian)

private theorem
    programPT06ThroatSpatialLocalFunctionTotalDerivative_add
    {order : Nat}
    (first second : TruncatedThroatSpatialMultiindexJet Fiber order → Target)
    (hFirst : Differentiable Real first)
    (hSecond : Differentiable Real second)
    (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun candidate => first candidate + second candidate) jet =
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction first jet +
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          second jet := by
  let base := truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet
  let tangent := throatSpatialTotalDerivative direction jet
  have hDerivative := fderiv_add (hFirst base) (hSecond base)
  have hPoint := congrArg (fun derivative => derivative tangent) hDerivative
  change
    fderiv Real (fun candidate => first candidate + second candidate)
        base tangent =
      fderiv Real first base tangent + fderiv Real second base tangent
  convert hPoint using 1 <;> rfl

private theorem
    programPT06ThroatSpatialLocalFunctionTotalDerivative_sub
    {order : Nat}
    (first second : TruncatedThroatSpatialMultiindexJet Fiber order → Target)
    (hFirst : Differentiable Real first)
    (hSecond : Differentiable Real second)
    (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun candidate => first candidate - second candidate) jet =
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction first jet -
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          second jet := by
  let base := truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet
  let tangent := throatSpatialTotalDerivative direction jet
  have hDerivative := fderiv_sub (hFirst base) (hSecond base)
  have hPoint := congrArg (fun derivative => derivative tangent) hDerivative
  change
    fderiv Real (fun candidate => first candidate - second candidate)
        base tangent =
      fderiv Real first base tangent - fderiv Real second base tangent
  convert hPoint using 1 <;> rfl

private theorem
    programPT06ThroatSpatialLocalFunctionTotalDerivative_fin_sum
    {Index : Type*} [Fintype Index] {order : Nat}
    (coefficient : Index → Real)
    (family : Index →
      TruncatedThroatSpatialMultiindexJet Fiber order → Target)
    (hDifferentiable : ∀ index, Differentiable Real (family index))
    (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun candidate =>
          ∑ index : Index, coefficient index • family index candidate) jet =
      ∑ index : Index, coefficient index •
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          (family index) jet := by
  let base := truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet
  have hDerivative : HasFDerivAt
      (fun candidate =>
        ∑ index : Index, coefficient index • family index candidate)
      (∑ index : Index,
        coefficient index • fderiv Real (family index) base) base := by
    apply HasFDerivAt.fun_sum
    intro index _
    exact ((hDifferentiable index).differentiableAt.hasFDerivAt).const_smul
      (coefficient index)
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    direction _ jet _ hDerivative]
  simp [programPT06ThroatSpatialLocalFunctionTotalDerivative, base]

/-- A `C3` local Lagrangian produces differentiable radial-current
components. -/
theorem programPT06SecondOrderRadialCartanCurrentComponent_differentiable
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (direction : Fin 3) :
    Differentiable Real
      (programPT06SecondOrderRadialCartanCurrentComponent
        localLagrangian direction) := by
  have hFirst : Differentiable Real
      (programPT06LiftSecondJetLocalFunction
        (programPT06SecondOrderRadialFirstContraction
          localLagrangian direction)) :=
    programPT06LiftSecondJetLocalFunction_differentiable _
      (programPT06SecondOrderRadialFirstContraction_differentiable
        localLagrangian hLagrangian direction)
  have hFamily (second : Fin 3) : Differentiable Real
      (fun jet : ThirdJet (Fiber := Fiber) =>
        programPT06LiftSecondJetLocalFunction
            (programPT06SecondOrderRadialSecondContraction
              localLagrangian direction second) jet -
          programPT06SecondOrderRadialProlongedSecondContraction
            localLagrangian direction second jet) :=
    (programPT06LiftSecondJetLocalFunction_differentiable _
      (programPT06SecondOrderRadialSecondContraction_differentiable
        localLagrangian hLagrangian direction second)).sub
      (programPT06SecondOrderRadialProlongedSecondContraction_differentiable
        localLagrangian hLagrangian direction second)
  have hSum : Differentiable Real
      (fun jet : ThirdJet (Fiber := Fiber) =>
        ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight direction second •
            (programPT06LiftSecondJetLocalFunction
                (programPT06SecondOrderRadialSecondContraction
                  localLagrangian direction second) jet -
              programPT06SecondOrderRadialProlongedSecondContraction
                localLagrangian direction second jet)) := by
    apply Differentiable.fun_sum
    intro second _
    exact (hFamily second).const_smul
      (programPT06SecondOrderEulerSymmetryWeight direction second : Real)
  change Differentiable Real
    (fun jet : ThirdJet (Fiber := Fiber) =>
      programPT06LiftSecondJetLocalFunction
          (programPT06SecondOrderRadialFirstContraction
            localLagrangian direction) jet +
        ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight direction second •
            (programPT06LiftSecondJetLocalFunction
                (programPT06SecondOrderRadialSecondContraction
                  localLagrangian direction second) jet -
              programPT06SecondOrderRadialProlongedSecondContraction
                localLagrangian direction second jet))
  exact hFirst.add hSum

/-- One total derivative of a radial-current component, before cancellation
of the two mixed double sums. -/
theorem programPT06SecondOrderRadialCartanCurrentComponent_totalDerivative
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (direction : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (programPT06SecondOrderRadialCartanCurrentComponent
          localLagrangian direction) jet =
      (programPT06SecondOrderLocalVerticalPartialOne
          localLagrangian direction
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
          ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
            (programPT06SecondOrderFirstMultiIndex direction)) +
        programPT06SecondOrderLocalEulerFirstTotalTerm
            localLagrangian direction
            (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)
          ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
            programPT06SecondOrderZeroMultiIndex)) +
      ∑ second : Fin 3,
        programPT06SecondOrderEulerSymmetryWeight direction second •
          ((programPT06SecondOrderLocalVerticalPartialTwo
              localLagrangian direction second
              (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
              ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
                (programPT06SecondOrderSecondMultiIndex direction second)) +
            programPT06ThroatSpatialLocalFunctionTotalDerivative direction
                (programPT06SecondOrderLocalVerticalPartialTwo
                  localLagrangian direction second)
                (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)
              ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
                (programPT06SecondOrderFirstMultiIndex second))) -
           (programPT06ThroatSpatialLocalFunctionTotalDerivative second
                (programPT06SecondOrderLocalVerticalPartialTwo
                  localLagrangian direction second)
                (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)
              ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
                (programPT06SecondOrderFirstMultiIndex direction)) +
            programPT06SecondOrderLocalEulerSecondTotalTerm
                localLagrangian direction second jet
              ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
                programPT06SecondOrderZeroMultiIndex))) := by
  let firstTerm := programPT06LiftSecondJetLocalFunction
    (programPT06SecondOrderRadialFirstContraction
      localLagrangian direction)
  let secondTerm := fun second : Fin 3 =>
    programPT06LiftSecondJetLocalFunction
      (programPT06SecondOrderRadialSecondContraction
        localLagrangian direction second)
  let prolongedTerm := fun second : Fin 3 =>
    programPT06SecondOrderRadialProlongedSecondContraction
      localLagrangian direction second
  have hFirst : Differentiable Real firstTerm :=
    programPT06LiftSecondJetLocalFunction_differentiable _
      (programPT06SecondOrderRadialFirstContraction_differentiable
        localLagrangian hLagrangian direction)
  have hSecond (second : Fin 3) : Differentiable Real (secondTerm second) :=
    programPT06LiftSecondJetLocalFunction_differentiable _
      (programPT06SecondOrderRadialSecondContraction_differentiable
        localLagrangian hLagrangian direction second)
  have hProlonged (second : Fin 3) :
      Differentiable Real (prolongedTerm second) :=
    programPT06SecondOrderRadialProlongedSecondContraction_differentiable
      localLagrangian hLagrangian direction second
  have hFamily (second : Fin 3) : Differentiable Real
      (fun candidate => secondTerm second candidate -
        prolongedTerm second candidate) :=
    (hSecond second).sub (hProlonged second)
  change
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
      (fun candidate => firstTerm candidate +
        ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight direction second •
            (secondTerm second candidate - prolongedTerm second candidate))
      jet = _
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_add
    firstTerm _ hFirst (by
      apply Differentiable.fun_sum
      intro second _
      exact (hFamily second).const_smul
        (programPT06SecondOrderEulerSymmetryWeight direction second : Real))
    direction jet]
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_fin_sum
    (fun second : Fin 3 =>
      programPT06SecondOrderEulerSymmetryWeight direction second)
    (fun second candidate =>
      secondTerm second candidate - prolongedTerm second candidate)
    hFamily direction jet]
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_liftSecondJet
    (programPT06SecondOrderRadialFirstContraction
      localLagrangian direction)
    (programPT06SecondOrderRadialFirstContraction_differentiable
      localLagrangian hLagrangian direction)]
  rw [programPT06SecondOrderRadialFirstContraction_totalDerivative
    localLagrangian hLagrangian]
  congr 1
  apply Finset.sum_congr rfl
  intro second _
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_sub
    (secondTerm second) (prolongedTerm second)
    (hSecond second) (hProlonged second) direction jet]
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_liftSecondJet
    (programPT06SecondOrderRadialSecondContraction
      localLagrangian direction second)
    (programPT06SecondOrderRadialSecondContraction_differentiable
      localLagrangian hLagrangian direction second)]
  rw [programPT06SecondOrderRadialSecondContraction_totalDerivative
    localLagrangian hLagrangian]
  rw [programPT06SecondOrderRadialProlongedSecondContraction_totalDerivative
    localLagrangian hLagrangian]
  simp [programPT06TruncateThroatSpatialMultiindexJet_trans]

/-- The radial first Frechet derivative is the weighted sum of all value,
first-jet and symmetric second-jet vertical contractions. -/
theorem programPT06SecondOrderRadialFrechetDerivative_decomposition
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (jet : SecondJet (Fiber := Fiber)) :
    fderiv Real localLagrangian jet jet =
      programPT06SecondOrderLocalVerticalPartialZero
          localLagrangian jet
          (jet programPT06SecondOrderZeroMultiIndex) +
        (∑ direction : Fin 3,
          programPT06SecondOrderLocalVerticalPartialOne
            localLagrangian direction jet
            (jet (programPT06SecondOrderFirstMultiIndex direction))) +
        ∑ first : Fin 3, ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight first second •
            programPT06SecondOrderLocalVerticalPartialTwo
              localLagrangian first second jet
              (jet (programPT06SecondOrderSecondMultiIndex first second)) := by
  have hDirection := congrArg
    (fun variation : SecondJet (Fiber := Fiber) =>
      fderiv Real localLagrangian jet variation)
    (programPT06SecondOrderJet_weightedCoordinateDecomposition jet)
  rw [hDirection]
  simp [programPT06SecondOrderLocalVerticalPartialZero_apply,
    programPT06SecondOrderLocalVerticalPartialOne_apply,
    programPT06SecondOrderLocalVerticalPartialTwo_apply]

/-- After the two mixed sums cancel, the Cartan-current differential is the
sum of the positive radial jet contractions and the negative of the two
non-value Euler contributions. -/
theorem programPT06SecondOrderRadialCartanCurrentDH_formula
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderRadialCartanCurrentDH localLagrangian jet =
      (∑ direction : Fin 3,
        programPT06SecondOrderLocalVerticalPartialOne
          localLagrangian direction
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
          ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
            (programPT06SecondOrderFirstMultiIndex direction))) +
      (∑ first : Fin 3, ∑ second : Fin 3,
        programPT06SecondOrderEulerSymmetryWeight first second •
          programPT06SecondOrderLocalVerticalPartialTwo
            localLagrangian first second
            (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
            ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
              (programPT06SecondOrderSecondMultiIndex first second))) +
      (∑ direction : Fin 3,
        programPT06SecondOrderLocalEulerFirstTotalTerm
          localLagrangian direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)
          ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
            programPT06SecondOrderZeroMultiIndex)) -
      ∑ first : Fin 3, ∑ second : Fin 3,
        programPT06SecondOrderEulerSymmetryWeight first second •
          programPT06SecondOrderLocalEulerSecondTotalTerm
            localLagrangian first second jet
            ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
              programPT06SecondOrderZeroMultiIndex) := by
  let jetTwo :=
    truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet
  let jetThree :=
    truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet
  have hMixed :
      (∑ first : Fin 3, ∑ second : Fin 3,
        programPT06SecondOrderEulerSymmetryWeight first second •
          programPT06ThroatSpatialLocalFunctionTotalDerivative first
              (programPT06SecondOrderLocalVerticalPartialTwo
                localLagrangian first second) jetThree
            (jetTwo (programPT06SecondOrderFirstMultiIndex second))) =
      ∑ first : Fin 3, ∑ second : Fin 3,
        programPT06SecondOrderEulerSymmetryWeight first second •
          programPT06ThroatSpatialLocalFunctionTotalDerivative second
              (programPT06SecondOrderLocalVerticalPartialTwo
                localLagrangian first second) jetThree
            (jetTwo (programPT06SecondOrderFirstMultiIndex first)) := by
    calc
      (∑ first : Fin 3, ∑ second : Fin 3,
        programPT06SecondOrderEulerSymmetryWeight first second •
          programPT06ThroatSpatialLocalFunctionTotalDerivative first
              (programPT06SecondOrderLocalVerticalPartialTwo
                localLagrangian first second) jetThree
            (jetTwo (programPT06SecondOrderFirstMultiIndex second))) =
          ∑ first : Fin 3, ∑ second : Fin 3,
            programPT06SecondOrderEulerSymmetryWeight second first •
              programPT06ThroatSpatialLocalFunctionTotalDerivative second
                  (programPT06SecondOrderLocalVerticalPartialTwo
                    localLagrangian second first) jetThree
                (jetTwo (programPT06SecondOrderFirstMultiIndex first)) := by
        rw [Finset.sum_comm]
      _ = ∑ first : Fin 3, ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight first second •
            programPT06ThroatSpatialLocalFunctionTotalDerivative second
                (programPT06SecondOrderLocalVerticalPartialTwo
                  localLagrangian first second) jetThree
              (jetTwo (programPT06SecondOrderFirstMultiIndex first)) := by
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro second _
        rw [programPT06SecondOrderEulerSymmetryWeight_comm second first,
          programPT06SecondOrderLocalVerticalPartialTwo_comm
            localLagrangian second first]
  rw [programPT06SecondOrderRadialCartanCurrentDH,
    programPT06SecondOrderHorizontalCurrentDH,
    programPT06SecondOrderRadialCartanCurrent]
  simp_rw [programPT06SecondOrderRadialCartanCurrentComponent_totalDerivative
    localLagrangian hLagrangian]
  change _ =
    (∑ direction : Fin 3,
        programPT06SecondOrderLocalVerticalPartialOne
          localLagrangian direction jetTwo
          (jetTwo (programPT06SecondOrderFirstMultiIndex direction))) +
      (∑ first : Fin 3, ∑ second : Fin 3,
        programPT06SecondOrderEulerSymmetryWeight first second •
          programPT06SecondOrderLocalVerticalPartialTwo
            localLagrangian first second jetTwo
            (jetTwo
              (programPT06SecondOrderSecondMultiIndex first second))) +
      (∑ direction : Fin 3,
        programPT06SecondOrderLocalEulerFirstTotalTerm
          localLagrangian direction jetThree
          (jetTwo programPT06SecondOrderZeroMultiIndex)) -
      ∑ first : Fin 3, ∑ second : Fin 3,
        programPT06SecondOrderEulerSymmetryWeight first second •
          programPT06SecondOrderLocalEulerSecondTotalTerm
            localLagrangian first second jet
            (jetTwo programPT06SecondOrderZeroMultiIndex)
  simp only [smul_eq_mul, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [smul_eq_mul] at hMixed
  rw [hMixed]
  ring

/-- Radial Cartan identity for an arbitrary `C3` second-order local
Lagrangian. -/
theorem programPT06SecondOrderRadialCartanIdentity
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (jet : FourthJet (Fiber := Fiber)) :
    fderiv Real localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) =
      programPT06SecondOrderLocalEuler localLagrangian jet
          ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
            programPT06SecondOrderZeroMultiIndex) +
        programPT06SecondOrderRadialCartanCurrentDH localLagrangian jet := by
  rw [programPT06SecondOrderRadialFrechetDerivative_decomposition,
    programPT06SecondOrderLocalEuler_apply,
    programPT06SecondOrderRadialCartanCurrentDH_formula
      localLagrangian hLagrangian]
  ring

/-- Gate922 notation for the same radial Cartan identity. -/
theorem programPT06SecondOrderHigherFrechetRadialCartanIdentity
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderEulerHigherFrechetDerivative 1 localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
        ![truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet] =
      programPT06SecondOrderLocalEuler localLagrangian jet
          ((truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
            programPT06SecondOrderZeroMultiIndex) +
        programPT06SecondOrderRadialCartanCurrentDH localLagrangian jet := by
  simpa [programPT06SecondOrderEulerHigherFrechetDerivative] using
    programPT06SecondOrderRadialCartanIdentity
      localLagrangian hLagrangian jet

private theorem
    programPT06ThroatSpatialLocalFunctionTotalDerivative_const_smul
    {order : Nat} (scalar : Real)
    (localFunction :
      TruncatedThroatSpatialMultiindexJet Fiber order → Real)
    (hLocalFunction : Differentiable Real localFunction)
    (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun candidate => scalar • localFunction candidate) jet =
      scalar •
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          localFunction jet := by
  let base := truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet
  have hDerivative : HasFDerivAt
      (fun candidate => scalar • localFunction candidate)
      (scalar • fderiv Real localFunction base) base := by
    (convert ((hLocalFunction base).hasFDerivAt).const_smul scalar using 1;
      rfl)
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    direction _ jet _ hDerivative]
  rfl

/-- The degree-normalized Cartan current for a diagonal homogeneous form. -/
def programPT06SecondOrderHomogeneousRadialCartanCurrent
    (degree : Nat)
    (form : ProgramPT06ContinuousHomogeneousForm4D
      (SecondJet (Fiber := Fiber)) degree) :
    ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber) :=
  fun direction jet => (degree : Real)⁻¹ •
    programPT06SecondOrderRadialCartanCurrentComponent
      (programPT06DiagonalHomogeneousTerm form) direction jet

/-- Horizontal differential of the normalized homogeneous Cartan current. -/
def programPT06SecondOrderHomogeneousRadialCartanCurrentDH
    (degree : Nat)
    (form : ProgramPT06ContinuousHomogeneousForm4D
      (SecondJet (Fiber := Fiber)) degree) :
    FourthJet (Fiber := Fiber) → Real :=
  programPT06SecondOrderHorizontalCurrentDH
    (programPT06SecondOrderHomogeneousRadialCartanCurrent degree form)

theorem programPT06SecondOrderHomogeneousRadialCartanCurrentDH_eq
    (degree : Nat)
    (form : ProgramPT06ContinuousHomogeneousForm4D
      (SecondJet (Fiber := Fiber)) degree)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderHomogeneousRadialCartanCurrentDH
        degree form jet =
      (degree : Real)⁻¹ •
        programPT06SecondOrderRadialCartanCurrentDH
          (programPT06DiagonalHomogeneousTerm form) jet := by
  let localLagrangian := programPT06DiagonalHomogeneousTerm form
  have hLagrangian : ContDiff Real 3 localLagrangian :=
    (programPT06DiagonalHomogeneousTerm_contDiff form).of_le
      (show (3 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  change
    (∑ direction : Fin 3,
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun candidate => (degree : Real)⁻¹ •
          programPT06SecondOrderRadialCartanCurrentComponent
            localLagrangian direction candidate) jet) =
      (degree : Real)⁻¹ •
        ∑ direction : Fin 3,
          programPT06ThroatSpatialLocalFunctionTotalDerivative direction
            (programPT06SecondOrderRadialCartanCurrentComponent
              localLagrangian direction) jet
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro direction _
  exact programPT06ThroatSpatialLocalFunctionTotalDerivative_const_smul
    (degree : Real)⁻¹ _
    (programPT06SecondOrderRadialCartanCurrentComponent_differentiable
      localLagrangian hLagrangian direction) direction jet

/-- A nonconstant homogeneous density in the Euler kernel is the horizontal
differential of its explicit degree-normalized radial Cartan current. -/
theorem
    programPT06SecondOrderHomogeneousDensity_eq_currentDH_of_euler_eq_zero
    {degree : Nat} (hDegree : degree ≠ 0)
    (form : ProgramPT06ContinuousHomogeneousForm4D
      (SecondJet (Fiber := Fiber)) degree)
    (jet : FourthJet (Fiber := Fiber))
    (hEuler : programPT06SecondOrderLocalEuler
      (programPT06DiagonalHomogeneousTerm form) jet = 0) :
    programPT06DiagonalHomogeneousTerm form
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) =
      programPT06SecondOrderHomogeneousRadialCartanCurrentDH
        degree form jet := by
  let localLagrangian := programPT06DiagonalHomogeneousTerm form
  let jetTwo :=
    truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet
  have hLagrangian : ContDiff Real 3 localLagrangian :=
    (programPT06DiagonalHomogeneousTerm_contDiff form).of_le
      (show (3 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hEulerPoint :
      programPT06SecondOrderLocalEuler localLagrangian jet
          (jetTwo programPT06SecondOrderZeroMultiIndex) = 0 := by
    rw [hEuler]
    rfl
  have hCartan := programPT06SecondOrderRadialCartanIdentity
    localLagrangian hLagrangian jet
  have hDegreeReal : (degree : Real) ≠ 0 := by
    exact_mod_cast hDegree
  rw [programPT06DiagonalHomogeneousTerm_fderiv_self form jetTwo,
    hEulerPoint, zero_add] at hCartan
  rw [programPT06SecondOrderHomogeneousRadialCartanCurrentDH_eq]
  change localLagrangian jetTwo =
    (degree : Real)⁻¹ •
      programPT06SecondOrderRadialCartanCurrentDH localLagrangian jet
  rw [← hCartan]
  simp [smul_eq_mul, hDegreeReal, localLagrangian]

end
end P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
end JanusFormal

