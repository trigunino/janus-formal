import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D

/-!
# A multifield Jacobian-minor null Lagrangian

For two continuous covectors `alpha`, `beta` on a finite-dimensional real
normed fiber and two distinct throat directions `i`, `j`, this gate treats
the first-order density

`alpha(u_i) * beta(u_j) - alpha(u_j) * beta(u_i)`.

The explicit current has components
`J_i = alpha(u) * beta(u_j)` and
`J_j = -alpha(u) * beta(u_i)`, with every other component zero.  Direct
Frechet calculations prove that its genuine Gate879 horizontal divergence
is the displayed density: the two mixed second-jet terms cancel by symmetry
of the jet multi-index.  A second direct polynomial calculation proves that
Gate880 Euler vanishes on every fourth jet, without a supplied Cartan
regularity certificate.

The density degenerates when either covector vanishes or when the two
covectors are linearly dependent.  This is one rank-two Jacobian minor, not a
classification of all multifield minors or of the complete polynomial Euler
kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06MultifieldJacobianMinorNullLagrangian4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
  [FiniteDimensional Real Fiber]

private abbrev FirstJet := ThroatSpatialMultiindexJet1 Fiber
private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- Data selecting one oriented rank-two Jacobian minor. -/
structure ProgramPT06MultifieldJacobianMinorData4D
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber] where
  alpha : Fiber →L[Real] Real
  beta : Fiber →L[Real] Real
  firstDirection : Fin 3
  secondDirection : Fin 3
  directions_ne : firstDirection ≠ secondDirection

private def firstOrderFirstMultiIndex (direction : Fin 3) :
    ThroatSpatialTruncatedIndex 1 :=
  ⟨throatSpatialCoordinateMultiIndex direction, by simp⟩

private def firstOrderValueProjection :
    FirstJet (Fiber := Fiber) →L[Real] Fiber :=
  ContinuousLinearMap.proj programPT06FirstOrderZeroMultiIndex

private def firstOrderFirstProjection (direction : Fin 3) :
    FirstJet (Fiber := Fiber) →L[Real] Fiber :=
  ContinuousLinearMap.proj (firstOrderFirstMultiIndex direction)

private def secondOrderFirstProjection (direction : Fin 3) :
    SecondJet (Fiber := Fiber) →L[Real] Fiber :=
  ContinuousLinearMap.proj
    (programPT06SecondOrderFirstMultiIndex direction)

private def secondOrderSecondProjection (first second : Fin 3) :
    SecondJet (Fiber := Fiber) →L[Real] Fiber :=
  ContinuousLinearMap.proj
    (programPT06SecondOrderSecondMultiIndex first second)

private def thirdOrderSecondMultiIndex (first second : Fin 3) :
    ThroatSpatialTruncatedIndex 3 :=
  { val :=
      throatSpatialCoordinateMultiIndex first +
        throatSpatialCoordinateMultiIndex second
    property := by
      rw [throatSpatialMultiIndexOrder_add]
      simp }

private theorem thirdOrderSecondMultiIndex_comm (first second : Fin 3) :
    thirdOrderSecondMultiIndex first second =
      thirdOrderSecondMultiIndex second first := by
  apply Subtype.ext
  exact add_comm _ _

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

private theorem secondOrderFirstMultiIndex_ne_zero (direction : Fin 3) :
    programPT06SecondOrderFirstMultiIndex direction ≠
      programPT06SecondOrderZeroMultiIndex := by
  intro hIndex
  have hOrder := congrArg
    (fun index : ThroatSpatialTruncatedIndex 2 =>
      throatSpatialMultiIndexOrder index.val) hIndex
  simp [programPT06SecondOrderFirstMultiIndex,
    programPT06SecondOrderZeroMultiIndex] at hOrder

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

omit [FiniteDimensional Real Fiber] in
@[simp] private theorem firstOrderValueProjection_truncate_second
    (jet : SecondJet (Fiber := Fiber)) :
    firstOrderValueProjection (Fiber := Fiber)
        (truncateThroatSpatialMultiindexJet (by omega : 1 <= 2) jet) =
      jet programPT06SecondOrderZeroMultiIndex := by
  rfl

omit [FiniteDimensional Real Fiber] in
@[simp] private theorem firstOrderFirstProjection_truncate_second
    (direction : Fin 3) (jet : SecondJet (Fiber := Fiber)) :
    firstOrderFirstProjection (Fiber := Fiber) direction
        (truncateThroatSpatialMultiindexJet (by omega : 1 <= 2) jet) =
      secondOrderFirstProjection (Fiber := Fiber) direction jet := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

omit [FiniteDimensional Real Fiber] in
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

omit [FiniteDimensional Real Fiber] in
@[simp] private theorem firstOrderFirstProjection_totalDerivative
    (horizontal slot : Fin 3) (jet : SecondJet (Fiber := Fiber)) :
    firstOrderFirstProjection (Fiber := Fiber) slot
        (throatSpatialTotalDerivative horizontal jet) =
      secondOrderSecondProjection (Fiber := Fiber) horizontal slot jet := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  simp [firstOrderFirstMultiIndex,
    programPT06SecondOrderSecondMultiIndex, add_comm]

omit [FiniteDimensional Real Fiber] in
@[simp] private theorem secondOrderFirstProjection_totalDerivative
    (horizontal slot : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    secondOrderFirstProjection (Fiber := Fiber) slot
        (throatSpatialTotalDerivative horizontal jet) =
      jet (thirdOrderSecondMultiIndex horizontal slot) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  simp [programPT06SecondOrderFirstMultiIndex,
    thirdOrderSecondMultiIndex, add_comm]

private def firstOrderAlphaValue
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    FirstJet (Fiber := Fiber) →L[Real] Real :=
  data.alpha.comp (firstOrderValueProjection (Fiber := Fiber))

private def firstOrderBetaFirst
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (direction : Fin 3) : FirstJet (Fiber := Fiber) →L[Real] Real :=
  data.beta.comp (firstOrderFirstProjection (Fiber := Fiber) direction)

private def programPT06JacobianMinorPositiveCurrent
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    FirstJet (Fiber := Fiber) -> Real :=
  fun jet =>
    firstOrderAlphaValue data jet *
      firstOrderBetaFirst data data.secondDirection jet

private def programPT06JacobianMinorNegativeCurrent
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    FirstJet (Fiber := Fiber) -> Real :=
  fun jet =>
    -(firstOrderAlphaValue data jet *
      firstOrderBetaFirst data data.firstDirection jet)

/-- The explicit order-one current with two nonzero components. -/
def programPT06MultifieldJacobianMinorCurrentComponent
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (direction : Fin 3) : FirstJet (Fiber := Fiber) -> Real :=
  if direction = data.firstDirection then
    programPT06JacobianMinorPositiveCurrent data
  else if direction = data.secondDirection then
    programPT06JacobianMinorNegativeCurrent data
  else
    0

/-- Every component of the explicit Jacobian-minor current is smooth. -/
theorem programPT06MultifieldJacobianMinorCurrentComponent_differentiable
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (direction : Fin 3) :
    Differentiable Real
      (programPT06MultifieldJacobianMinorCurrentComponent data direction) := by
  by_cases hFirst : direction = data.firstDirection
  · subst direction
    simp only [programPT06MultifieldJacobianMinorCurrentComponent, if_pos]
    exact (firstOrderAlphaValue data).differentiable.mul
      (firstOrderBetaFirst data data.secondDirection).differentiable
  · by_cases hSecond : direction = data.secondDirection
    · subst direction
      simp only [programPT06MultifieldJacobianMinorCurrentComponent,
        hFirst, if_false, if_pos]
      exact ((firstOrderAlphaValue data).differentiable.mul
        (firstOrderBetaFirst data data.firstDirection).differentiable).neg
    · simp only [programPT06MultifieldJacobianMinorCurrentComponent,
        hFirst, hSecond, if_false]
      fun_prop

private def programPT06JacobianMinorPositiveCurrentDerivative
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (jet : FirstJet (Fiber := Fiber)) :
    FirstJet (Fiber := Fiber) →L[Real] Real :=
  (firstOrderBetaFirst data data.secondDirection jet) •
      firstOrderAlphaValue data +
    (firstOrderAlphaValue data jet) •
      firstOrderBetaFirst data data.secondDirection

private theorem programPT06JacobianMinorPositiveCurrent_hasFDerivAt
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (jet : FirstJet (Fiber := Fiber)) :
    HasFDerivAt
      (programPT06JacobianMinorPositiveCurrent data)
      (programPT06JacobianMinorPositiveCurrentDerivative data jet) jet := by
  have hRaw :=
    ((firstOrderAlphaValue data).hasFDerivAt (x := jet)).mul
      ((firstOrderBetaFirst data data.secondDirection).hasFDerivAt (x := jet))
  refine hRaw.congr_fderiv ?_
  ext variation
  simp [programPT06JacobianMinorPositiveCurrentDerivative]
  ring

private def programPT06JacobianMinorNegativeCurrentDerivative
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (jet : FirstJet (Fiber := Fiber)) :
    FirstJet (Fiber := Fiber) →L[Real] Real :=
  -((firstOrderBetaFirst data data.firstDirection jet) •
      firstOrderAlphaValue data +
    (firstOrderAlphaValue data jet) •
      firstOrderBetaFirst data data.firstDirection)

private theorem programPT06JacobianMinorNegativeCurrent_hasFDerivAt
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (jet : FirstJet (Fiber := Fiber)) :
    HasFDerivAt
      (programPT06JacobianMinorNegativeCurrent data)
      (programPT06JacobianMinorNegativeCurrentDerivative data jet) jet := by
  have hRaw :=
    (((firstOrderAlphaValue data).hasFDerivAt (x := jet)).mul
      ((firstOrderBetaFirst data data.firstDirection).hasFDerivAt (x := jet))).neg
  refine hRaw.congr_fderiv ?_
  ext variation
  simp [programPT06JacobianMinorNegativeCurrentDerivative]
  ring

private def secondOrderAlphaValue
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  data.alpha.comp
    (ContinuousLinearMap.proj programPT06SecondOrderZeroMultiIndex)

private def secondOrderAlphaFirst
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (direction : Fin 3) : SecondJet (Fiber := Fiber) →L[Real] Real :=
  data.alpha.comp (secondOrderFirstProjection (Fiber := Fiber) direction)

private def secondOrderBetaFirst
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (direction : Fin 3) : SecondJet (Fiber := Fiber) →L[Real] Real :=
  data.beta.comp (secondOrderFirstProjection (Fiber := Fiber) direction)

private def secondOrderBetaSecond
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (first second : Fin 3) : SecondJet (Fiber := Fiber) →L[Real] Real :=
  data.beta.comp
    (secondOrderSecondProjection (Fiber := Fiber) first second)

private theorem programPT06JacobianMinorPositiveCurrent_totalDerivative
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (horizontal : Fin 3) (jet : SecondJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative horizontal
        (programPT06JacobianMinorPositiveCurrent data) jet =
      secondOrderAlphaFirst data horizontal jet *
          secondOrderBetaFirst data data.secondDirection jet +
        secondOrderAlphaValue data jet *
          secondOrderBetaSecond data horizontal data.secondDirection jet := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    horizontal (programPT06JacobianMinorPositiveCurrent data) jet
    (programPT06JacobianMinorPositiveCurrentDerivative data
      (truncateThroatSpatialMultiindexJet (by omega : 1 <= 2) jet))
    (programPT06JacobianMinorPositiveCurrent_hasFDerivAt data
      (truncateThroatSpatialMultiindexJet (by omega : 1 <= 2) jet))]
  simp [programPT06JacobianMinorPositiveCurrentDerivative,
    firstOrderAlphaValue, firstOrderBetaFirst, secondOrderAlphaValue,
    secondOrderAlphaFirst, secondOrderBetaFirst, secondOrderBetaSecond]
  ring

private theorem programPT06JacobianMinorNegativeCurrent_totalDerivative
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (horizontal : Fin 3) (jet : SecondJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative horizontal
        (programPT06JacobianMinorNegativeCurrent data) jet =
      -(secondOrderAlphaFirst data horizontal jet *
          secondOrderBetaFirst data data.firstDirection jet +
        secondOrderAlphaValue data jet *
          secondOrderBetaSecond data horizontal data.firstDirection jet) := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    horizontal (programPT06JacobianMinorNegativeCurrent data) jet
    (programPT06JacobianMinorNegativeCurrentDerivative data
      (truncateThroatSpatialMultiindexJet (by omega : 1 <= 2) jet))
    (programPT06JacobianMinorNegativeCurrent_hasFDerivAt data
      (truncateThroatSpatialMultiindexJet (by omega : 1 <= 2) jet))]
  simp [programPT06JacobianMinorNegativeCurrentDerivative,
    firstOrderAlphaValue, firstOrderBetaFirst, secondOrderAlphaValue,
    secondOrderAlphaFirst, secondOrderBetaFirst, secondOrderBetaSecond]
  ring

private theorem programPT06JacobianMinorCurrentComponent_totalDerivative
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (direction : Fin 3) (jet : SecondJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (programPT06MultifieldJacobianMinorCurrentComponent data direction) jet =
      if direction = data.firstDirection then
        secondOrderAlphaFirst data direction jet *
            secondOrderBetaFirst data data.secondDirection jet +
          secondOrderAlphaValue data jet *
            secondOrderBetaSecond data direction data.secondDirection jet
      else if direction = data.secondDirection then
        -(secondOrderAlphaFirst data direction jet *
            secondOrderBetaFirst data data.firstDirection jet +
          secondOrderAlphaValue data jet *
            secondOrderBetaSecond data direction data.firstDirection jet)
      else 0 := by
  by_cases hFirst : direction = data.firstDirection
  · subst direction
    rw [show
      programPT06MultifieldJacobianMinorCurrentComponent
          data data.firstDirection =
        programPT06JacobianMinorPositiveCurrent data by
          simp [programPT06MultifieldJacobianMinorCurrentComponent]]
    rw [programPT06JacobianMinorPositiveCurrent_totalDerivative]
    simp
  · by_cases hSecond : direction = data.secondDirection
    · subst direction
      rw [show
        programPT06MultifieldJacobianMinorCurrentComponent
            data data.secondDirection =
          programPT06JacobianMinorNegativeCurrent data by
            simp [programPT06MultifieldJacobianMinorCurrentComponent, hFirst]]
      rw [programPT06JacobianMinorNegativeCurrent_totalDerivative]
      simp [hFirst]
    · rw [show
        programPT06MultifieldJacobianMinorCurrentComponent data direction = 0 by
          simp [programPT06MultifieldJacobianMinorCurrentComponent,
            hFirst, hSecond]]
      simp [hFirst, hSecond]

private theorem programPT06FinThree_sum_two_ite
    {Target : Type*} [AddCommMonoid Target]
    (first second : Fin 3) (hDirections : first ≠ second)
    (positive negative : Fin 3 -> Target) :
    (∑ direction : Fin 3,
      if direction = first then positive direction
      else if direction = second then negative direction
      else 0) = positive first + negative second := by
  calc
    (∑ direction : Fin 3,
      if direction = first then positive direction
      else if direction = second then negative direction
      else 0) =
        (∑ direction : Fin 3,
          ((if direction = first then positive direction else 0) +
            (if direction = second then negative direction else 0))) := by
      apply Finset.sum_congr rfl
      intro direction _
      by_cases hFirst : direction = first
      · subst direction
        simp [hDirections]
      · by_cases hSecond : direction = second <;>
          simp [hFirst, hSecond, Ne.symm hDirections]
    _ =
        (∑ direction : Fin 3,
          if direction = first then positive direction else 0) +
        ∑ direction : Fin 3,
          if direction = second then negative direction else 0 := by
      rw [Finset.sum_add_distrib]
    _ = positive first + negative second := by
      have hPositive :
          (∑ direction : Fin 3,
            if direction = first then positive direction else 0) =
              positive first :=
        Fintype.sum_ite_eq' first positive
      have hNegative :
          (∑ direction : Fin 3,
            if direction = second then negative direction else 0) =
              negative second :=
        Fintype.sum_ite_eq' second negative
      rw [hPositive, hNegative]

private theorem secondOrderBetaSecond_comm
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (first second : Fin 3) (jet : SecondJet (Fiber := Fiber)) :
    secondOrderBetaSecond data first second jet =
      secondOrderBetaSecond data second first jet := by
  simp [secondOrderBetaSecond, secondOrderSecondProjection,
    programPT06SecondOrderSecondMultiIndex_comm]

/-- The genuine Gate879 divergence of the explicit two-component current. -/
def programPT06MultifieldJacobianMinorCurrentDivergence
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    SecondJet (Fiber := Fiber) -> Real :=
  fun jet => ∑ direction : Fin 3,
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
      (programPT06MultifieldJacobianMinorCurrentComponent data direction) jet

/-- Evaluation of the oriented Jacobian-minor density. -/
def programPT06MultifieldJacobianMinorDensityEvaluation
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    SecondJet (Fiber := Fiber) -> Real :=
  fun jet =>
    secondOrderAlphaFirst data data.firstDirection jet *
        secondOrderBetaFirst data data.secondDirection jet -
      secondOrderAlphaFirst data data.secondDirection jet *
        secondOrderBetaFirst data data.firstDirection jet

/-- Algebraic homotopy identity: the true divergence is the minor. -/
theorem programPT06MultifieldJacobianMinorCurrentDivergence_eq_density
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    programPT06MultifieldJacobianMinorCurrentDivergence data =
      programPT06MultifieldJacobianMinorDensityEvaluation data := by
  funext jet
  unfold programPT06MultifieldJacobianMinorCurrentDivergence
  simp_rw [programPT06JacobianMinorCurrentComponent_totalDerivative]
  rw [programPT06FinThree_sum_two_ite
    data.firstDirection data.secondDirection data.directions_ne]
  rw [secondOrderBetaSecond_comm data
    data.firstDirection data.secondDirection jet]
  unfold programPT06MultifieldJacobianMinorDensityEvaluation
  ring

private def programPT06JacobianMinorDensityDerivative
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  (secondOrderBetaFirst data data.secondDirection jet) •
      secondOrderAlphaFirst data data.firstDirection +
    (secondOrderAlphaFirst data data.firstDirection jet) •
      secondOrderBetaFirst data data.secondDirection -
    ((secondOrderBetaFirst data data.firstDirection jet) •
        secondOrderAlphaFirst data data.secondDirection +
      (secondOrderAlphaFirst data data.secondDirection jet) •
        secondOrderBetaFirst data data.firstDirection)

theorem programPT06MultifieldJacobianMinorDensityEvaluation_hasFDerivAt
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    HasFDerivAt
      (programPT06MultifieldJacobianMinorDensityEvaluation data)
      (programPT06JacobianMinorDensityDerivative data jet) jet := by
  have hRaw :=
    (((secondOrderAlphaFirst data data.firstDirection).hasFDerivAt
      (x := jet)).mul
      ((secondOrderBetaFirst data data.secondDirection).hasFDerivAt
        (x := jet))).sub
    (((secondOrderAlphaFirst data data.secondDirection).hasFDerivAt
      (x := jet)).mul
      ((secondOrderBetaFirst data data.firstDirection).hasFDerivAt
        (x := jet)))
  refine hRaw.congr_fderiv ?_
  ext variation
  simp [programPT06JacobianMinorDensityDerivative]
  ring

/-- The Jacobian-minor density is differentiable on the whole second-jet
space. -/
theorem programPT06MultifieldJacobianMinorDensityEvaluation_differentiable
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    Differentiable Real
      (programPT06MultifieldJacobianMinorDensityEvaluation data) :=
  fun jet =>
    (programPT06MultifieldJacobianMinorDensityEvaluation_hasFDerivAt
      data jet).differentiableAt

private def programPT06JacobianMinorFirstPartialAtFirst
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    SecondJet (Fiber := Fiber) →L[Real] (Fiber →L[Real] Real) :=
  (secondOrderBetaFirst data data.secondDirection).smulRight data.alpha -
    (secondOrderAlphaFirst data data.secondDirection).smulRight data.beta

private def programPT06JacobianMinorFirstPartialAtSecond
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    SecondJet (Fiber := Fiber) →L[Real] (Fiber →L[Real] Real) :=
  (secondOrderAlphaFirst data data.firstDirection).smulRight data.beta -
    (secondOrderBetaFirst data data.firstDirection).smulRight data.alpha

/-- The minor has no value-slot vertical derivative. -/
theorem programPT06JacobianMinorVerticalPartialZero
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06MultifieldJacobianMinorDensityEvaluation data) = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06MultifieldJacobianMinorDensityEvaluation data) jet
      programPT06SecondOrderZeroMultiIndex = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06MultifieldJacobianMinorDensityEvaluation data) jet
    programPT06SecondOrderZeroMultiIndex
    (programPT06JacobianMinorDensityDerivative data jet)
    (programPT06MultifieldJacobianMinorDensityEvaluation_hasFDerivAt data jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06JacobianMinorDensityDerivative, secondOrderAlphaFirst,
    secondOrderBetaFirst, secondOrderFirstProjection,
    secondOrderFirstMultiIndex_ne_zero]

private theorem programPT06JacobianMinorVerticalPartialOne_first
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06MultifieldJacobianMinorDensityEvaluation data)
        data.firstDirection =
      programPT06JacobianMinorFirstPartialAtFirst data := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06MultifieldJacobianMinorDensityEvaluation data) jet
      (programPT06SecondOrderFirstMultiIndex data.firstDirection) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06MultifieldJacobianMinorDensityEvaluation data) jet
    (programPT06SecondOrderFirstMultiIndex data.firstDirection)
    (programPT06JacobianMinorDensityDerivative data jet)
    (programPT06MultifieldJacobianMinorDensityEvaluation_hasFDerivAt data jet)]
  have hIndex :
      programPT06SecondOrderFirstMultiIndex data.secondDirection ≠
        programPT06SecondOrderFirstMultiIndex data.firstDirection := by
    intro hEqual
    exact data.directions_ne
      (secondOrderFirstMultiIndex_injective hEqual).symm
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06JacobianMinorDensityDerivative,
    programPT06JacobianMinorFirstPartialAtFirst, secondOrderAlphaFirst,
    secondOrderBetaFirst, secondOrderFirstProjection, hIndex]

private theorem programPT06JacobianMinorVerticalPartialOne_second
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06MultifieldJacobianMinorDensityEvaluation data)
        data.secondDirection =
      programPT06JacobianMinorFirstPartialAtSecond data := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06MultifieldJacobianMinorDensityEvaluation data) jet
      (programPT06SecondOrderFirstMultiIndex data.secondDirection) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06MultifieldJacobianMinorDensityEvaluation data) jet
    (programPT06SecondOrderFirstMultiIndex data.secondDirection)
    (programPT06JacobianMinorDensityDerivative data jet)
    (programPT06MultifieldJacobianMinorDensityEvaluation_hasFDerivAt data jet)]
  have hIndex :
      programPT06SecondOrderFirstMultiIndex data.firstDirection ≠
        programPT06SecondOrderFirstMultiIndex data.secondDirection := by
    intro hEqual
    exact data.directions_ne
      (secondOrderFirstMultiIndex_injective hEqual)
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06JacobianMinorDensityDerivative,
    programPT06JacobianMinorFirstPartialAtSecond, secondOrderAlphaFirst,
    secondOrderBetaFirst, secondOrderFirstProjection, hIndex]

private theorem programPT06JacobianMinorVerticalPartialOne_other
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (direction : Fin 3) (hFirst : direction ≠ data.firstDirection)
    (hSecond : direction ≠ data.secondDirection) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06MultifieldJacobianMinorDensityEvaluation data)
        direction = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06MultifieldJacobianMinorDensityEvaluation data) jet
      (programPT06SecondOrderFirstMultiIndex direction) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06MultifieldJacobianMinorDensityEvaluation data) jet
    (programPT06SecondOrderFirstMultiIndex direction)
    (programPT06JacobianMinorDensityDerivative data jet)
    (programPT06MultifieldJacobianMinorDensityEvaluation_hasFDerivAt data jet)]
  have hIndexFirst :
      programPT06SecondOrderFirstMultiIndex data.firstDirection ≠
        programPT06SecondOrderFirstMultiIndex direction := by
    intro hEqual
    exact hFirst (secondOrderFirstMultiIndex_injective hEqual).symm
  have hIndexSecond :
      programPT06SecondOrderFirstMultiIndex data.secondDirection ≠
        programPT06SecondOrderFirstMultiIndex direction := by
    intro hEqual
    exact hSecond (secondOrderFirstMultiIndex_injective hEqual).symm
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06JacobianMinorDensityDerivative, secondOrderAlphaFirst,
    secondOrderBetaFirst, secondOrderFirstProjection,
    hIndexFirst, hIndexSecond]

/-- Every order-one vertical partial of the minor is differentiable. -/
theorem programPT06JacobianMinorVerticalPartialOne_differentiable
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (direction : Fin 3) :
    Differentiable Real
      (programPT06SecondOrderLocalVerticalPartialOne
        (programPT06MultifieldJacobianMinorDensityEvaluation data)
        direction) := by
  by_cases hFirst : direction = data.firstDirection
  · subst direction
    rw [programPT06JacobianMinorVerticalPartialOne_first]
    exact (programPT06JacobianMinorFirstPartialAtFirst data).differentiable
  · by_cases hSecond : direction = data.secondDirection
    · subst direction
      rw [programPT06JacobianMinorVerticalPartialOne_second]
      exact (programPT06JacobianMinorFirstPartialAtSecond data).differentiable
    · rw [programPT06JacobianMinorVerticalPartialOne_other
          data direction hFirst hSecond]
      fun_prop

/-- The first-order minor has no second-jet vertical derivative. -/
theorem programPT06JacobianMinorVerticalPartialTwo
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06MultifieldJacobianMinorDensityEvaluation data)
        first second = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06MultifieldJacobianMinorDensityEvaluation data) jet
      (programPT06SecondOrderSecondMultiIndex first second) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06MultifieldJacobianMinorDensityEvaluation data) jet
    (programPT06SecondOrderSecondMultiIndex first second)
    (programPT06JacobianMinorDensityDerivative data jet)
    (programPT06MultifieldJacobianMinorDensityEvaluation_hasFDerivAt data jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06JacobianMinorDensityDerivative, secondOrderAlphaFirst,
    secondOrderBetaFirst, secondOrderFirstProjection,
    Ne.symm (secondOrderSecondMultiIndex_ne_first first second
      data.firstDirection),
    Ne.symm (secondOrderSecondMultiIndex_ne_first first second
      data.secondDirection)]

private theorem programPT06JacobianMinorEulerFirstTerm_formula
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06MultifieldJacobianMinorDensityEvaluation data)
        direction jet =
      if direction = data.firstDirection then
        programPT06JacobianMinorFirstPartialAtFirst data
          (throatSpatialTotalDerivative direction jet)
      else if direction = data.secondDirection then
        programPT06JacobianMinorFirstPartialAtSecond data
          (throatSpatialTotalDerivative direction jet)
      else 0 := by
  by_cases hFirst : direction = data.firstDirection
  · subst direction
    rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
      programPT06JacobianMinorVerticalPartialOne_first]
    simp
  · by_cases hSecond : direction = data.secondDirection
    · subst direction
      rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
        programPT06JacobianMinorVerticalPartialOne_second]
      simp [hFirst]
    · rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
        programPT06JacobianMinorVerticalPartialOne_other data direction
          hFirst hSecond]
      simp [hFirst, hSecond]

private theorem programPT06JacobianMinorFirstPartialCancellation
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (jet : ThirdJet (Fiber := Fiber)) :
    programPT06JacobianMinorFirstPartialAtFirst data
          (throatSpatialTotalDerivative data.firstDirection jet) +
        programPT06JacobianMinorFirstPartialAtSecond data
          (throatSpatialTotalDerivative data.secondDirection jet) = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06JacobianMinorFirstPartialAtFirst,
    programPT06JacobianMinorFirstPartialAtSecond,
    secondOrderAlphaFirst, secondOrderBetaFirst,
    secondOrderFirstProjection_totalDerivative,
    thirdOrderSecondMultiIndex_comm]

/-- The three first-total-derivative Euler contributions cancel. -/
theorem programPT06JacobianMinorEulerFirstSum
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (jet : ThirdJet (Fiber := Fiber)) :
    (∑ direction : Fin 3,
      programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06MultifieldJacobianMinorDensityEvaluation data)
        direction jet) = 0 := by
  simp_rw [programPT06JacobianMinorEulerFirstTerm_formula]
  rw [programPT06FinThree_sum_two_ite
    data.firstDirection data.secondDirection data.directions_ne]
  exact programPT06JacobianMinorFirstPartialCancellation data jet

private theorem programPT06JacobianMinorEulerSecondTerm
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (first second : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06MultifieldJacobianMinorDensityEvaluation data)
        first second jet = 0 := by
  rw [programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06JacobianMinorVerticalPartialTwo]
  simp

/-- Gate880 annihilates the Jacobian minor unconditionally. -/
theorem programPT06SecondOrderLocalEuler_multifieldJacobianMinor_eq_zero
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06MultifieldJacobianMinorDensityEvaluation data) jet = 0 := by
  rw [programPT06SecondOrderLocalEuler_formula,
    programPT06JacobianMinorVerticalPartialZero,
    programPT06JacobianMinorEulerFirstSum]
  simp [programPT06JacobianMinorEulerSecondTerm]

/-- The true Gate879 divergence formulation is Euler-null as well. -/
theorem programPT06SecondOrderLocalEuler_multifieldJacobianMinorDivergence_eq_zero
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06MultifieldJacobianMinorCurrentDivergence data) jet = 0 := by
  rw [programPT06MultifieldJacobianMinorCurrentDivergence_eq_density]
  exact programPT06SecondOrderLocalEuler_multifieldJacobianMinor_eq_zero data jet

@[simp] theorem programPT06MultifieldJacobianMinorDensity_alpha_zero
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (hAlpha : data.alpha = 0) :
    programPT06MultifieldJacobianMinorDensityEvaluation data = 0 := by
  funext jet
  simp [programPT06MultifieldJacobianMinorDensityEvaluation,
    secondOrderAlphaFirst, hAlpha]

@[simp] theorem programPT06MultifieldJacobianMinorDensity_beta_zero
    (data : ProgramPT06MultifieldJacobianMinorData4D Fiber)
    (hBeta : data.beta = 0) :
    programPT06MultifieldJacobianMinorDensityEvaluation data = 0 := by
  funext jet
  simp [programPT06MultifieldJacobianMinorDensityEvaluation,
    secondOrderBetaFirst, hBeta]

end
end P0EFTJanusProgramPT06MultifieldJacobianMinorNullLagrangian4D
end JanusFormal
