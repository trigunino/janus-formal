import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AffineSecondOrderExactness4D

/-!
# A genuine quadratic horizontal boundary density

This gate extends the certified affine null-density class by one explicit
nonlinear family.  A directed order-one current is the product of two
continuous linear functionals of the value coordinate.  Its actual formal
total derivative is a homogeneous quadratic function on the genuine spatial
second jet, and Gate880's Euler operator annihilates it.

The construction is deliberately bounded: it covers rank-one quadratic
value currents in one throat direction (and their finite linear spans after
using linearity), not arbitrary quadratic currents and not the complete T02
degree-four carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev FirstJet := ThroatSpatialMultiindexJet1 Fiber
private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- One directed rank-one quadratic current.  Its component is
`left(u) * right(u)` and depends only on the value coordinate of an order-one
jet. -/
structure ProgramPT06DirectedQuadraticValueCurrent4D
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] where
  direction : Fin 3
  left : Fiber →L[Real] Real
  right : Fiber →L[Real] Real

/-- The value multi-index in an order-one jet. -/
def programPT06FirstOrderZeroMultiIndex :
    ThroatSpatialTruncatedIndex 1 :=
  ⟨0, by simp⟩

private def firstOrderValueProjection :
    FirstJet (Fiber := Fiber) →L[Real] Fiber :=
  ContinuousLinearMap.proj programPT06FirstOrderZeroMultiIndex

private def secondOrderValueProjection :
    SecondJet (Fiber := Fiber) →L[Real] Fiber :=
  ContinuousLinearMap.proj programPT06SecondOrderZeroMultiIndex

private def secondOrderFirstProjection (direction : Fin 3) :
    SecondJet (Fiber := Fiber) →L[Real] Fiber :=
  ContinuousLinearMap.proj
    (programPT06SecondOrderFirstMultiIndex direction)

private theorem secondOrderFirstMultiIndex_ne_zero (direction : Fin 3) :
    programPT06SecondOrderFirstMultiIndex direction ≠
      programPT06SecondOrderZeroMultiIndex := by
  intro hIndex
  have hOrder := congrArg
    (fun index : ThroatSpatialTruncatedIndex 2 =>
      throatSpatialMultiIndexOrder index.1) hIndex
  simp [programPT06SecondOrderFirstMultiIndex,
    programPT06SecondOrderZeroMultiIndex] at hOrder

private theorem throatSpatialCoordinateMultiIndex_injective :
    Function.Injective throatSpatialCoordinateMultiIndex := by
  intro first second hIndex
  by_contra hDirections
  have hCoordinate := congrArg (fun index : ThroatSpatialMultiIndex => index first)
    hIndex
  simp [throatSpatialCoordinateMultiIndex, hDirections] at hCoordinate

private theorem secondOrderFirstMultiIndex_injective :
    Function.Injective programPT06SecondOrderFirstMultiIndex := by
  intro first second hIndex
  apply throatSpatialCoordinateMultiIndex_injective
  exact congrArg Subtype.val hIndex

private theorem secondOrderSecondMultiIndex_ne_zero
    (first second : Fin 3) :
    programPT06SecondOrderSecondMultiIndex first second ≠
      programPT06SecondOrderZeroMultiIndex := by
  intro hIndex
  have hOrder := congrArg
    (fun index : ThroatSpatialTruncatedIndex 2 =>
      throatSpatialMultiIndexOrder index.1) hIndex
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
      throatSpatialMultiIndexOrder index.1) hIndex
  simp [programPT06SecondOrderSecondMultiIndex,
    programPT06SecondOrderFirstMultiIndex,
    throatSpatialMultiIndexOrder_add] at hOrder

@[simp] private theorem firstOrderValueProjection_truncate_second
    (jet : SecondJet (Fiber := Fiber)) :
    firstOrderValueProjection (Fiber := Fiber)
        (truncateThroatSpatialMultiindexJet (by omega : 1 ≤ 2) jet) =
      secondOrderValueProjection (Fiber := Fiber) jet := by
  rfl

@[simp] private theorem firstOrderValueProjection_totalDerivative
    (direction : Fin 3) (jet : SecondJet (Fiber := Fiber)) :
    firstOrderValueProjection (Fiber := Fiber)
        (throatSpatialTotalDerivative direction jet) =
      secondOrderFirstProjection (Fiber := Fiber) direction jet := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  simp [programPT06FirstOrderZeroMultiIndex,
    programPT06SecondOrderFirstMultiIndex]

@[simp] private theorem secondOrderValueProjection_totalDerivative
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    secondOrderValueProjection (Fiber := Fiber)
        (throatSpatialTotalDerivative direction jet) =
      secondOrderFirstProjection (Fiber := Fiber) direction
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  simp [programPT06SecondOrderZeroMultiIndex,
    programPT06SecondOrderFirstMultiIndex]

private def firstOrderLeftCovector
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    FirstJet (Fiber := Fiber) →L[Real] Real :=
  current.left.comp (firstOrderValueProjection (Fiber := Fiber))

private def firstOrderRightCovector
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    FirstJet (Fiber := Fiber) →L[Real] Real :=
  current.right.comp (firstOrderValueProjection (Fiber := Fiber))

/-- The sole nonzero polynomial current component. -/
def programPT06DirectedQuadraticValueCurrentComponent
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    FirstJet (Fiber := Fiber) → Real :=
  fun jet =>
    firstOrderLeftCovector current jet *
      firstOrderRightCovector current jet

private def programPT06DirectedQuadraticValueCurrentDerivative
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (jet : FirstJet (Fiber := Fiber)) :
    FirstJet (Fiber := Fiber) →L[Real] Real :=
  (firstOrderRightCovector current jet) • firstOrderLeftCovector current +
    (firstOrderLeftCovector current jet) • firstOrderRightCovector current

theorem programPT06DirectedQuadraticValueCurrentComponent_hasFDerivAt
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (jet : FirstJet (Fiber := Fiber)) :
    HasFDerivAt
      (programPT06DirectedQuadraticValueCurrentComponent current)
      (programPT06DirectedQuadraticValueCurrentDerivative current jet) jet := by
  change HasFDerivAt
    (fun candidate : FirstJet (Fiber := Fiber) =>
      firstOrderLeftCovector current candidate *
        firstOrderRightCovector current candidate) _ jet
  have hRaw :=
    ((firstOrderLeftCovector current).hasFDerivAt (x := jet)).mul
      ((firstOrderRightCovector current).hasFDerivAt (x := jet))
  refine hRaw.congr_fderiv ?_
  ext variation
  simp [programPT06DirectedQuadraticValueCurrentDerivative]
  ring

/-- The actual formal total derivative of the directed quadratic current. -/
def programPT06DirectedQuadraticValueCurrentDivergence
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    SecondJet (Fiber := Fiber) → Real :=
  programPT06ThroatSpatialLocalFunctionTotalDerivative current.direction
    (programPT06DirectedQuadraticValueCurrentComponent current)

private def secondOrderLeftValueCovector
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  current.left.comp (secondOrderValueProjection (Fiber := Fiber))

private def secondOrderRightValueCovector
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  current.right.comp (secondOrderValueProjection (Fiber := Fiber))

private def secondOrderLeftFirstCovector
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  current.left.comp
    (secondOrderFirstProjection (Fiber := Fiber) current.direction)

private def secondOrderRightFirstCovector
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  current.right.comp
    (secondOrderFirstProjection (Fiber := Fiber) current.direction)

/-- Explicit homogeneous quadratic density on the second-jet carrier. -/
def programPT06DirectedQuadraticValueDensityEvaluation
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    SecondJet (Fiber := Fiber) → Real :=
  fun jet =>
    secondOrderLeftFirstCovector current jet *
        secondOrderRightValueCovector current jet +
      secondOrderLeftValueCovector current jet *
        secondOrderRightFirstCovector current jet

/-- Algebraic homotopy identity: the explicit quadratic density is exactly
the genuine total derivative of the polynomial current component. -/
theorem programPT06DirectedQuadraticValueCurrentDivergence_eq_density
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    programPT06DirectedQuadraticValueCurrentDivergence current =
      programPT06DirectedQuadraticValueDensityEvaluation current := by
  funext jet
  rw [programPT06DirectedQuadraticValueCurrentDivergence,
    programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
      current.direction
      (programPT06DirectedQuadraticValueCurrentComponent current) jet
      (programPT06DirectedQuadraticValueCurrentDerivative current
        (truncateThroatSpatialMultiindexJet (by omega : 1 ≤ 2) jet))
      (programPT06DirectedQuadraticValueCurrentComponent_hasFDerivAt
        current
        (truncateThroatSpatialMultiindexJet (by omega : 1 ≤ 2) jet))]
  simp [programPT06DirectedQuadraticValueCurrentDerivative,
    programPT06DirectedQuadraticValueDensityEvaluation,
    firstOrderLeftCovector, firstOrderRightCovector,
    secondOrderLeftValueCovector, secondOrderRightValueCovector,
    secondOrderLeftFirstCovector, secondOrderRightFirstCovector]
  ring

@[simp] theorem programPT06DirectedQuadraticValueDensityEvaluation_smul
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (scalar : Real) (jet : SecondJet (Fiber := Fiber)) :
    programPT06DirectedQuadraticValueDensityEvaluation current (scalar • jet) =
      scalar ^ 2 *
        programPT06DirectedQuadraticValueDensityEvaluation current jet := by
  simp [programPT06DirectedQuadraticValueDensityEvaluation]
  ring

private def programPT06DirectedQuadraticValueDensityDerivative
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  (secondOrderRightValueCovector current jet) •
      secondOrderLeftFirstCovector current +
    (secondOrderLeftFirstCovector current jet) •
      secondOrderRightValueCovector current +
    (secondOrderRightFirstCovector current jet) •
      secondOrderLeftValueCovector current +
    (secondOrderLeftValueCovector current jet) •
      secondOrderRightFirstCovector current

theorem programPT06DirectedQuadraticValueDensityEvaluation_hasFDerivAt
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    HasFDerivAt
      (programPT06DirectedQuadraticValueDensityEvaluation current)
      (programPT06DirectedQuadraticValueDensityDerivative current jet) jet := by
  change HasFDerivAt
    (fun candidate : SecondJet (Fiber := Fiber) =>
      secondOrderLeftFirstCovector current candidate *
          secondOrderRightValueCovector current candidate +
        secondOrderLeftValueCovector current candidate *
          secondOrderRightFirstCovector current candidate) _ jet
  have hRaw :=
    (((secondOrderLeftFirstCovector current).hasFDerivAt (x := jet)).mul
      ((secondOrderRightValueCovector current).hasFDerivAt (x := jet))).add
    (((secondOrderLeftValueCovector current).hasFDerivAt (x := jet)).mul
      ((secondOrderRightFirstCovector current).hasFDerivAt (x := jet)))
  refine hRaw.congr_fderiv ?_
  ext variation
  simp [programPT06DirectedQuadraticValueDensityDerivative]
  ring

private def programPT06DirectedQuadraticValueZeroPartialMap
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    SecondJet (Fiber := Fiber) →L[Real] (Fiber →L[Real] Real) :=
  (secondOrderLeftFirstCovector current).smulRight current.right +
    (secondOrderRightFirstCovector current).smulRight current.left

private def programPT06DirectedQuadraticValueFirstPartialMap
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    SecondJet (Fiber := Fiber) →L[Real] (Fiber →L[Real] Real) :=
  (secondOrderRightValueCovector current).smulRight current.left +
    (secondOrderLeftValueCovector current).smulRight current.right

theorem programPT06DirectedQuadraticValueDensityVerticalPartialZero
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06DirectedQuadraticValueDensityEvaluation current) =
      programPT06DirectedQuadraticValueZeroPartialMap current := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06DirectedQuadraticValueDensityEvaluation current) jet
      programPT06SecondOrderZeroMultiIndex = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06DirectedQuadraticValueDensityEvaluation current) jet
    programPT06SecondOrderZeroMultiIndex
    (programPT06DirectedQuadraticValueDensityDerivative current jet)
    (programPT06DirectedQuadraticValueDensityEvaluation_hasFDerivAt
      current jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06DirectedQuadraticValueDensityDerivative,
    programPT06DirectedQuadraticValueZeroPartialMap,
    secondOrderLeftValueCovector, secondOrderRightValueCovector,
    secondOrderLeftFirstCovector, secondOrderRightFirstCovector,
    secondOrderValueProjection, secondOrderFirstProjection,
    secondOrderFirstMultiIndex_ne_zero current.direction]

theorem programPT06DirectedQuadraticValueDensityVerticalPartialOne_self
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06DirectedQuadraticValueDensityEvaluation current)
        current.direction =
      programPT06DirectedQuadraticValueFirstPartialMap current := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06DirectedQuadraticValueDensityEvaluation current) jet
      (programPT06SecondOrderFirstMultiIndex current.direction) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06DirectedQuadraticValueDensityEvaluation current) jet
    (programPT06SecondOrderFirstMultiIndex current.direction)
    (programPT06DirectedQuadraticValueDensityDerivative current jet)
    (programPT06DirectedQuadraticValueDensityEvaluation_hasFDerivAt
      current jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06DirectedQuadraticValueDensityDerivative,
    programPT06DirectedQuadraticValueFirstPartialMap,
    secondOrderLeftValueCovector, secondOrderRightValueCovector,
    secondOrderLeftFirstCovector, secondOrderRightFirstCovector,
    secondOrderValueProjection, secondOrderFirstProjection,
    Ne.symm (secondOrderFirstMultiIndex_ne_zero current.direction)]

theorem programPT06DirectedQuadraticValueDensityVerticalPartialOne_of_ne
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (direction : Fin 3) (hDirection : direction ≠ current.direction) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06DirectedQuadraticValueDensityEvaluation current)
        direction = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06DirectedQuadraticValueDensityEvaluation current) jet
      (programPT06SecondOrderFirstMultiIndex direction) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06DirectedQuadraticValueDensityEvaluation current) jet
    (programPT06SecondOrderFirstMultiIndex direction)
    (programPT06DirectedQuadraticValueDensityDerivative current jet)
    (programPT06DirectedQuadraticValueDensityEvaluation_hasFDerivAt
      current jet)]
  apply ContinuousLinearMap.ext
  intro variation
  have hIndex :
      programPT06SecondOrderFirstMultiIndex current.direction ≠
        programPT06SecondOrderFirstMultiIndex direction := by
    intro hEqual
    exact hDirection
      (secondOrderFirstMultiIndex_injective hEqual.symm)
  simp [programPT06DirectedQuadraticValueDensityDerivative,
    secondOrderLeftValueCovector, secondOrderRightValueCovector,
    secondOrderLeftFirstCovector, secondOrderRightFirstCovector,
    secondOrderValueProjection, secondOrderFirstProjection,
    Ne.symm (secondOrderFirstMultiIndex_ne_zero direction), hIndex]

theorem programPT06DirectedQuadraticValueDensityVerticalPartialTwo
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06DirectedQuadraticValueDensityEvaluation current)
        first second = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06DirectedQuadraticValueDensityEvaluation current) jet
      (programPT06SecondOrderSecondMultiIndex first second) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06DirectedQuadraticValueDensityEvaluation current) jet
    (programPT06SecondOrderSecondMultiIndex first second)
    (programPT06DirectedQuadraticValueDensityDerivative current jet)
    (programPT06DirectedQuadraticValueDensityEvaluation_hasFDerivAt
      current jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06DirectedQuadraticValueDensityDerivative,
    secondOrderLeftValueCovector, secondOrderRightValueCovector,
    secondOrderLeftFirstCovector, secondOrderRightFirstCovector,
    secondOrderValueProjection, secondOrderFirstProjection,
    Ne.symm (secondOrderSecondMultiIndex_ne_zero first second),
    Ne.symm (secondOrderSecondMultiIndex_ne_first first second current.direction)]

private theorem programPT06DirectedQuadraticValueFirstPartialTotalDerivative
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (jet : ThirdJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative current.direction
        (programPT06DirectedQuadraticValueFirstPartialMap current) jet =
      programPT06DirectedQuadraticValueZeroPartialMap current
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_linear]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06DirectedQuadraticValueFirstPartialMap,
    programPT06DirectedQuadraticValueZeroPartialMap,
    secondOrderLeftValueCovector, secondOrderRightValueCovector,
    secondOrderLeftFirstCovector, secondOrderRightFirstCovector]
  ring

private theorem programPT06DirectedQuadraticValueEulerFirstTerm_self
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (jet : ThirdJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06DirectedQuadraticValueDensityEvaluation current)
        current.direction jet =
      programPT06DirectedQuadraticValueZeroPartialMap current
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) := by
  rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
    programPT06DirectedQuadraticValueDensityVerticalPartialOne_self]
  exact programPT06DirectedQuadraticValueFirstPartialTotalDerivative
    current jet

private theorem programPT06DirectedQuadraticValueEulerFirstTerm_of_ne
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (direction : Fin 3) (hDirection : direction ≠ current.direction)
    (jet : ThirdJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06DirectedQuadraticValueDensityEvaluation current)
        direction jet = 0 := by
  rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
    programPT06DirectedQuadraticValueDensityVerticalPartialOne_of_ne
      current direction hDirection]
  simp

private theorem programPT06DirectedQuadraticValueEulerSecondTerm
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (first second : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06DirectedQuadraticValueDensityEvaluation current)
        first second jet = 0 := by
  rw [programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06DirectedQuadraticValueDensityVerticalPartialTwo]
  simp

/-- Gate880 soundness for the first genuinely nonlinear current class. -/
theorem programPT06SecondOrderLocalEuler_directedQuadraticValueDensity_eq_zero
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06DirectedQuadraticValueDensityEvaluation current) jet = 0 := by
  rw [programPT06SecondOrderLocalEuler_formula,
    programPT06DirectedQuadraticValueDensityVerticalPartialZero]
  have hFirst :
      (∑ direction : Fin 3,
        programPT06SecondOrderLocalEulerFirstTotalTerm
          (programPT06DirectedQuadraticValueDensityEvaluation current)
          direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)) =
        programPT06DirectedQuadraticValueZeroPartialMap current
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) := by
    rw [Finset.sum_eq_single current.direction]
    · rw [programPT06DirectedQuadraticValueEulerFirstTerm_self]
      congr 2
    · intro direction _ hDirection
      exact programPT06DirectedQuadraticValueEulerFirstTerm_of_ne
        current direction hDirection _
    · simp
  rw [hFirst]
  simp [programPT06DirectedQuadraticValueEulerSecondTerm]

/-- The same Euler-null statement expressed directly for the actual total
derivative from the homotopy identity. -/
theorem programPT06SecondOrderLocalEuler_directedQuadraticValueDivergence_eq_zero
    (current : ProgramPT06DirectedQuadraticValueCurrent4D Fiber)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06DirectedQuadraticValueCurrentDivergence current) jet = 0 := by
  rw [programPT06DirectedQuadraticValueCurrentDivergence_eq_density]
  exact
    programPT06SecondOrderLocalEuler_directedQuadraticValueDensity_eq_zero
      current jet

end
end P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D
end JanusFormal
