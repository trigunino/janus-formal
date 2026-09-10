import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderLocalEuler4D

/-!
# Euler soundness for directed C2 value currents

This gate treats a nonlinear family of horizontal boundaries at once.  A
potential on the field-value fiber is supplied with its genuine Frechet
derivative, a derivative of that derivative, and the resulting Hessian
symmetry.  Placing the potential in one horizontal direction gives the true
Gate879 total derivative

`D_i V(u) = DV(u)(u_i)`.

Gate880's second-order Euler operator annihilates this density: its value
partial and the total derivative of its first-jet partial are the two orders
of evaluation of the symmetric Hessian.  The construction includes all
diagonal polynomial potentials through degree four from the earlier
polynomial gate.  It does not classify the full polynomial Euler kernel or
currents depending on derivative coordinates.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06C2ValuePotentialCurrent4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D
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

/-- A value potential with certified first and second Frechet derivatives.
The second derivative is recorded in curried continuous-bilinear form. -/
structure ProgramPT06C2ValuePotential4D
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] where
  value : Fiber → Real
  gradient : Fiber → (Fiber →L[Real] Real)
  hessian : Fiber → (Fiber →L[Real] (Fiber →L[Real] Real))
  value_hasFDerivAt : ∀ field,
    HasFDerivAt value (gradient field) field
  gradient_hasFDerivAt : ∀ field,
    HasFDerivAt gradient (hessian field) field
  hessian_symmetric : ∀ field first second,
    hessian field first second = hessian field second first

theorem ProgramPT06C2ValuePotential4D.gradient_continuous
    (potential : ProgramPT06C2ValuePotential4D Fiber) :
    Continuous potential.gradient := by
  rw [continuous_iff_continuousAt]
  intro field
  exact (potential.gradient_hasFDerivAt field).continuousAt

/-- Every globally `C2` scalar potential supplies the preceding certificate
using its actual first and second Frechet derivatives. -/
def programPT06C2ValuePotentialOfContDiff
    (value : Fiber → Real) (hValue : ContDiff Real 2 value) :
    ProgramPT06C2ValuePotential4D Fiber where
  value := value
  gradient := fderiv Real value
  hessian := fderiv Real (fderiv Real value)
  value_hasFDerivAt := fun field =>
    (hValue.differentiable (by norm_num) field).hasFDerivAt
  gradient_hasFDerivAt := fun field =>
    ((hValue.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) field).hasFDerivAt
  hessian_symmetric := fun field first second =>
    second_derivative_symmetric
      (fun point => (hValue.differentiable (by norm_num) point).hasFDerivAt)
      (((hValue.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num) field).hasFDerivAt)
      first second

/-- A `C2` value potential placed in one horizontal direction. -/
structure ProgramPT06DirectedC2ValueCurrent4D
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] where
  direction : Fin 3
  potential : ProgramPT06C2ValuePotential4D Fiber

/-- The value index in a genuine first jet. -/
def programPT06C2FirstOrderZeroMultiIndex :
    ThroatSpatialTruncatedIndex 1 :=
  ⟨0, by simp⟩

private def firstOrderValueProjection :
    FirstJet (Fiber := Fiber) →L[Real] Fiber :=
  ContinuousLinearMap.proj programPT06C2FirstOrderZeroMultiIndex

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
  have hCoordinate := congrArg
    (fun index : ThroatSpatialMultiIndex => index first) hIndex
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
  simp [programPT06C2FirstOrderZeroMultiIndex,
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

/-- The local first-jet component of a directed potential current. -/
def programPT06DirectedC2ValueCurrentComponent
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber) :
    FirstJet (Fiber := Fiber) → Real :=
  fun jet => current.potential.value
    (firstOrderValueProjection (Fiber := Fiber) jet)

private def programPT06DirectedC2ValueCurrentComponentDerivative
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (jet : FirstJet (Fiber := Fiber)) :
    FirstJet (Fiber := Fiber) →L[Real] Real :=
  (current.potential.gradient
    (firstOrderValueProjection (Fiber := Fiber) jet)).comp
      (firstOrderValueProjection (Fiber := Fiber))

theorem programPT06DirectedC2ValueCurrentComponent_hasFDerivAt
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (jet : FirstJet (Fiber := Fiber)) :
    HasFDerivAt
      (programPT06DirectedC2ValueCurrentComponent current)
      (programPT06DirectedC2ValueCurrentComponentDerivative current jet) jet := by
  exact (current.potential.value_hasFDerivAt
    (firstOrderValueProjection (Fiber := Fiber) jet)).comp jet
      (firstOrderValueProjection (Fiber := Fiber)).hasFDerivAt

/-- The actual Gate879 horizontal derivative of the directed current. -/
def programPT06DirectedC2ValueCurrentDivergence
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber) :
    SecondJet (Fiber := Fiber) → Real :=
  programPT06ThroatSpatialLocalFunctionTotalDerivative current.direction
    (programPT06DirectedC2ValueCurrentComponent current)

/-- Chain-rule form of the same density on genuine second jets. -/
def programPT06DirectedC2ValueDensityEvaluation
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber) :
    SecondJet (Fiber := Fiber) → Real :=
  fun jet =>
    current.potential.gradient
      (secondOrderValueProjection (Fiber := Fiber) jet)
      (secondOrderFirstProjection (Fiber := Fiber) current.direction jet)

/-- The explicit density is definitionally tied to Gate879's true total
derivative rather than introduced as an independent boundary ansatz. -/
theorem programPT06DirectedC2ValueCurrentDivergence_eq_density
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber) :
    programPT06DirectedC2ValueCurrentDivergence current =
      programPT06DirectedC2ValueDensityEvaluation current := by
  funext jet
  rw [programPT06DirectedC2ValueCurrentDivergence,
    programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
      current.direction
      (programPT06DirectedC2ValueCurrentComponent current) jet
      (programPT06DirectedC2ValueCurrentComponentDerivative current
        (truncateThroatSpatialMultiindexJet (by omega : 1 ≤ 2) jet))
      (programPT06DirectedC2ValueCurrentComponent_hasFDerivAt current
        (truncateThroatSpatialMultiindexJet (by omega : 1 ≤ 2) jet))]
  simp [programPT06DirectedC2ValueCurrentComponentDerivative,
    programPT06DirectedC2ValueDensityEvaluation]

private def programPT06DirectedC2ValueDensityDerivative
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  (ContinuousLinearMap.apply Real Real
      (secondOrderFirstProjection (Fiber := Fiber) current.direction jet)).comp
        ((current.potential.hessian
          (secondOrderValueProjection (Fiber := Fiber) jet)).comp
            (secondOrderValueProjection (Fiber := Fiber))) +
    (current.potential.gradient
      (secondOrderValueProjection (Fiber := Fiber) jet)).comp
        (secondOrderFirstProjection (Fiber := Fiber) current.direction)

private theorem programPT06DirectedC2ValueGradientOnSecondJet_hasFDerivAt
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    HasFDerivAt
      (fun candidate : SecondJet (Fiber := Fiber) =>
        current.potential.gradient
          (secondOrderValueProjection (Fiber := Fiber) candidate))
      ((current.potential.hessian
        (secondOrderValueProjection (Fiber := Fiber) jet)).comp
          (secondOrderValueProjection (Fiber := Fiber))) jet := by
  exact (current.potential.gradient_hasFDerivAt
    (secondOrderValueProjection (Fiber := Fiber) jet)).comp jet
      (secondOrderValueProjection (Fiber := Fiber)).hasFDerivAt

theorem programPT06DirectedC2ValueDensityEvaluation_hasFDerivAt
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    HasFDerivAt
      (programPT06DirectedC2ValueDensityEvaluation current)
      (programPT06DirectedC2ValueDensityDerivative current jet) jet := by
  have hRaw :=
    (programPT06DirectedC2ValueGradientOnSecondJet_hasFDerivAt current jet).clm_apply
      ((secondOrderFirstProjection (Fiber := Fiber)
        current.direction).hasFDerivAt (x := jet))
  refine hRaw.congr_fderiv ?_
  ext variation
  simp [programPT06DirectedC2ValueDensityDerivative]
  abel

private def programPT06DirectedC2ValueDensityZeroPartial
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) : Fiber →L[Real] Real :=
  (ContinuousLinearMap.apply Real Real
    (secondOrderFirstProjection (Fiber := Fiber) current.direction jet)).comp
      (current.potential.hessian
        (secondOrderValueProjection (Fiber := Fiber) jet))

theorem programPT06DirectedC2ValueDensityVerticalPartialZero
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06DirectedC2ValueDensityEvaluation current) =
      programPT06DirectedC2ValueDensityZeroPartial current := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06DirectedC2ValueDensityEvaluation current) jet
      programPT06SecondOrderZeroMultiIndex = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06DirectedC2ValueDensityEvaluation current) jet
    programPT06SecondOrderZeroMultiIndex
    (programPT06DirectedC2ValueDensityDerivative current jet)
    (programPT06DirectedC2ValueDensityEvaluation_hasFDerivAt current jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06DirectedC2ValueDensityDerivative,
    programPT06DirectedC2ValueDensityZeroPartial,
    secondOrderValueProjection, secondOrderFirstProjection,
    secondOrderFirstMultiIndex_ne_zero current.direction]

theorem programPT06DirectedC2ValueDensityVerticalPartialOne_self
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06DirectedC2ValueDensityEvaluation current)
        current.direction =
      fun jet => current.potential.gradient
        (secondOrderValueProjection (Fiber := Fiber) jet) := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06DirectedC2ValueDensityEvaluation current) jet
      (programPT06SecondOrderFirstMultiIndex current.direction) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06DirectedC2ValueDensityEvaluation current) jet
    (programPT06SecondOrderFirstMultiIndex current.direction)
    (programPT06DirectedC2ValueDensityDerivative current jet)
    (programPT06DirectedC2ValueDensityEvaluation_hasFDerivAt current jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06DirectedC2ValueDensityDerivative,
    secondOrderValueProjection, secondOrderFirstProjection,
    Ne.symm (secondOrderFirstMultiIndex_ne_zero current.direction)]

theorem programPT06DirectedC2ValueDensityVerticalPartialOne_of_ne
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (direction : Fin 3) (hDirection : direction ≠ current.direction) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06DirectedC2ValueDensityEvaluation current) direction = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06DirectedC2ValueDensityEvaluation current) jet
      (programPT06SecondOrderFirstMultiIndex direction) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06DirectedC2ValueDensityEvaluation current) jet
    (programPT06SecondOrderFirstMultiIndex direction)
    (programPT06DirectedC2ValueDensityDerivative current jet)
    (programPT06DirectedC2ValueDensityEvaluation_hasFDerivAt current jet)]
  apply ContinuousLinearMap.ext
  intro variation
  have hIndex :
      programPT06SecondOrderFirstMultiIndex current.direction ≠
        programPT06SecondOrderFirstMultiIndex direction := by
    intro hEqual
    exact hDirection (secondOrderFirstMultiIndex_injective hEqual.symm)
  simp [programPT06DirectedC2ValueDensityDerivative,
    secondOrderValueProjection, secondOrderFirstProjection,
    Ne.symm (secondOrderFirstMultiIndex_ne_zero direction), hIndex]

theorem programPT06DirectedC2ValueDensityVerticalPartialTwo
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06DirectedC2ValueDensityEvaluation current)
        first second = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06DirectedC2ValueDensityEvaluation current) jet
      (programPT06SecondOrderSecondMultiIndex first second) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06DirectedC2ValueDensityEvaluation current) jet
    (programPT06SecondOrderSecondMultiIndex first second)
    (programPT06DirectedC2ValueDensityDerivative current jet)
    (programPT06DirectedC2ValueDensityEvaluation_hasFDerivAt current jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06DirectedC2ValueDensityDerivative,
    secondOrderValueProjection, secondOrderFirstProjection,
    Ne.symm (secondOrderSecondMultiIndex_ne_zero first second),
    Ne.symm
      (secondOrderSecondMultiIndex_ne_first first second current.direction)]

private theorem programPT06DirectedC2ValueFirstPartialTotalDerivative
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (jet : ThirdJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative current.direction
        (fun candidate : SecondJet (Fiber := Fiber) =>
          current.potential.gradient
            (secondOrderValueProjection (Fiber := Fiber) candidate)) jet =
      current.potential.hessian
        (secondOrderValueProjection (Fiber := Fiber)
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))
        (secondOrderFirstProjection (Fiber := Fiber) current.direction
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    current.direction
    (fun candidate : SecondJet (Fiber := Fiber) =>
      current.potential.gradient
        (secondOrderValueProjection (Fiber := Fiber) candidate)) jet
    ((current.potential.hessian
      (secondOrderValueProjection (Fiber := Fiber)
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))).comp
      (secondOrderValueProjection (Fiber := Fiber)))
    (programPT06DirectedC2ValueGradientOnSecondJet_hasFDerivAt current
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  simp

private theorem programPT06DirectedC2ValueEulerFirstTerm_self
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (jet : ThirdJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06DirectedC2ValueDensityEvaluation current)
        current.direction jet =
      current.potential.hessian
        (secondOrderValueProjection (Fiber := Fiber)
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))
        (secondOrderFirstProjection (Fiber := Fiber) current.direction
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) := by
  rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
    programPT06DirectedC2ValueDensityVerticalPartialOne_self]
  exact programPT06DirectedC2ValueFirstPartialTotalDerivative current jet

private theorem programPT06DirectedC2ValueEulerFirstTerm_of_ne
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (direction : Fin 3) (hDirection : direction ≠ current.direction)
    (jet : ThirdJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06DirectedC2ValueDensityEvaluation current)
        direction jet = 0 := by
  rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
    programPT06DirectedC2ValueDensityVerticalPartialOne_of_ne
      current direction hDirection]
  simp

private theorem programPT06DirectedC2ValueEulerSecondTerm
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (first second : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06DirectedC2ValueDensityEvaluation current)
        first second jet = 0 := by
  rw [programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06DirectedC2ValueDensityVerticalPartialTwo]
  simp

/-- Gate880 soundness for every directed `C2` value current. -/
theorem programPT06SecondOrderLocalEuler_directedC2ValueDensity_eq_zero
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06DirectedC2ValueDensityEvaluation current) jet = 0 := by
  rw [programPT06SecondOrderLocalEuler_formula,
    programPT06DirectedC2ValueDensityVerticalPartialZero]
  have hFirst :
      (∑ direction : Fin 3,
        programPT06SecondOrderLocalEulerFirstTotalTerm
          (programPT06DirectedC2ValueDensityEvaluation current)
          direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)) =
        current.potential.hessian
          (secondOrderValueProjection (Fiber := Fiber)
            (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet))
          (secondOrderFirstProjection (Fiber := Fiber) current.direction
            (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)) := by
    rw [Finset.sum_eq_single current.direction]
    · rw [programPT06DirectedC2ValueEulerFirstTerm_self]
      congr 2
    · intro direction _ hDirection
      exact programPT06DirectedC2ValueEulerFirstTerm_of_ne
        current direction hDirection _
    · simp
  rw [hFirst]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06DirectedC2ValueDensityZeroPartial,
    programPT06DirectedC2ValueEulerSecondTerm,
    current.potential.hessian_symmetric]

/-- The same result stated for the actual Gate879 total derivative. -/
theorem programPT06SecondOrderLocalEuler_directedC2ValueDivergence_eq_zero
    (current : ProgramPT06DirectedC2ValueCurrent4D Fiber)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06DirectedC2ValueCurrentDivergence current) jet = 0 := by
  rw [programPT06DirectedC2ValueCurrentDivergence_eq_density]
  exact programPT06SecondOrderLocalEuler_directedC2ValueDensity_eq_zero
    current jet

private theorem programPT06DiagonalHomogeneousTerm_contDiff
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D Fiber degree) :
    ContDiff Real ⊤ (programPT06DiagonalHomogeneousTerm form) := by
  exact (ContinuousMultilinearMap.contDiff form).comp
    (contDiff_pi.2 fun _ => contDiff_id)

/-- The previously constructed diagonal degree-at-most-four polynomial is
globally smooth, hence provides a certified `C2` value potential. -/
theorem programPT06DiagonalPolynomialEvaluation_contDiff
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D Fiber) :
    ContDiff Real ⊤ (programPT06DiagonalPolynomialEvaluation polynomial) := by
  have hConstant : ContDiff Real ⊤
      (programPT06DiagonalConstantTerm polynomial.constant : Fiber → Real) :=
    contDiff_const
  have hLinear : ContDiff Real ⊤
      (programPT06DiagonalLinearTerm polynomial.linear) :=
    polynomial.linear.contDiff
  have hQuadratic :=
    programPT06DiagonalHomogeneousTerm_contDiff polynomial.quadratic
  have hCubic :=
    programPT06DiagonalHomogeneousTerm_contDiff polynomial.cubic
  have hQuartic :=
    programPT06DiagonalHomogeneousTerm_contDiff polynomial.quartic
  exact ((((hConstant.add hLinear).add hQuadratic).add hCubic).add hQuartic)

/-- Canonical `C2` certificate for a diagonal polynomial through degree four. -/
def programPT06DiagonalPolynomialC2ValuePotential
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D Fiber) :
    ProgramPT06C2ValuePotential4D Fiber :=
  programPT06C2ValuePotentialOfContDiff
    (programPT06DiagonalPolynomialEvaluation polynomial)
    ((programPT06DiagonalPolynomialEvaluation_contDiff polynomial).of_le
      (by norm_num))

@[simp] theorem programPT06DiagonalPolynomialC2ValuePotential_gradient
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D Fiber)
    (field : Fiber) :
    (programPT06DiagonalPolynomialC2ValuePotential polynomial).gradient field =
      programPT06DiagonalPolynomialDerivative polynomial field := by
  exact programPT06DiagonalPolynomialEvaluation_fderiv polynomial field

/-- A diagonal polynomial value potential placed in one chosen direction. -/
def programPT06DirectedDiagonalPolynomialValueCurrent
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D Fiber)
    (direction : Fin 3) : ProgramPT06DirectedC2ValueCurrent4D Fiber where
  direction := direction
  potential := programPT06DiagonalPolynomialC2ValuePotential polynomial

/-- All diagonal polynomial value currents through degree four are genuine
Gate879 boundaries and are killed by Gate880. -/
theorem programPT06SecondOrderLocalEuler_directedDiagonalPolynomialDivergence_eq_zero
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D Fiber)
    (direction : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06DirectedC2ValueCurrentDivergence
          (programPT06DirectedDiagonalPolynomialValueCurrent
            polynomial direction)) jet = 0 := by
  exact programPT06SecondOrderLocalEuler_directedC2ValueDivergence_eq_zero
    (programPT06DirectedDiagonalPolynomialValueCurrent polynomial direction) jet

end
end P0EFTJanusProgramPT06C2ValuePotentialCurrent4D
end JanusFormal
