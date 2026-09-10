import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ScalarHessianMinorNullLagrangian4D

/-!
# Multifield Jacobian minor of first gradients

For a finite-dimensional real normed fiber, continuous covectors `alpha` and
`beta`, base directions `p`, `q`, and distinct divergence directions `i`, `j`,
this gate treats the genuine second-jet density

`alpha(u_{p i}) * beta(u_{q j}) - alpha(u_{p j}) * beta(u_{q i})`.

The order-two current has nonzero components
`J_i = alpha(u_p) * beta(u_{q j})` and
`J_j = -alpha(u_p) * beta(u_{q i})`.  Its Gate879 horizontal differential is
computed directly on third jets.  The two third-order terms cancel by honest
commutativity of the jet multi-index, leaving exactly the displayed density.

Gate880 is also evaluated directly.  One weighted contraction lemma reproduces
each unordered second-jet slot from the ordered direction sum, including every
possible alias among `(p,i)`, `(q,j)`, `(p,j)`, `(q,i)`; the remaining fourth
derivatives cancel by multi-index commutativity.  This gate proves one
decomposable minor and does not classify finite sums or the full kernel.  The
scalar Hessian-minor specialization is recorded explicitly below.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06MultifieldGradientJacobianMinorNullLagrangian4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06ScalarHessianMinorNullLagrangian4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
  [FiniteDimensional Real Fiber]

private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- Data selecting one decomposable Jacobian minor of two first gradients. -/
structure ProgramPT06MultifieldGradientJacobianMinorData4D
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber] where
  alpha : Fiber →L[Real] Real
  beta : Fiber →L[Real] Real
  alphaBaseDirection : Fin 3
  betaBaseDirection : Fin 3
  firstDirection : Fin 3
  secondDirection : Fin 3
  directions_ne : firstDirection ≠ secondDirection

private def secondOrderFirstProjection (direction : Fin 3) :
    SecondJet (Fiber := Fiber) →L[Real] Fiber :=
  ContinuousLinearMap.proj
    (programPT06SecondOrderFirstMultiIndex direction)

private def secondOrderSecondProjection (first second : Fin 3) :
    SecondJet (Fiber := Fiber) →L[Real] Fiber :=
  ContinuousLinearMap.proj
    (programPT06SecondOrderSecondMultiIndex first second)

private def thirdOrderFirstMultiIndex (direction : Fin 3) :
    ThroatSpatialTruncatedIndex 3 :=
  ⟨throatSpatialCoordinateMultiIndex direction, by simp⟩

private def thirdOrderSecondMultiIndex (first second : Fin 3) :
    ThroatSpatialTruncatedIndex 3 :=
  ⟨throatSpatialCoordinateMultiIndex first +
      throatSpatialCoordinateMultiIndex second, by
    rw [throatSpatialMultiIndexOrder_add]
    simp⟩

private def thirdOrderThirdMultiIndex
    (first second third : Fin 3) : ThroatSpatialTruncatedIndex 3 :=
  ⟨(throatSpatialCoordinateMultiIndex first +
      throatSpatialCoordinateMultiIndex second) +
      throatSpatialCoordinateMultiIndex third, by
    rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex,
      throatSpatialMultiIndexOrder_add]
    simp⟩

omit [FiniteDimensional Real Fiber] in
@[simp] private theorem secondOrderFirstProjection_truncate_third
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    secondOrderFirstProjection (Fiber := Fiber) direction
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) =
      jet (thirdOrderFirstMultiIndex direction) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

omit [FiniteDimensional Real Fiber] in
@[simp] private theorem secondOrderSecondProjection_truncate_third
    (first second : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    secondOrderSecondProjection (Fiber := Fiber) first second
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) =
      jet (thirdOrderSecondMultiIndex first second) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

omit [FiniteDimensional Real Fiber] in
@[simp] private theorem secondOrderFirstProjection_totalDerivative
    (horizontal slot : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    secondOrderFirstProjection (Fiber := Fiber) slot
        (throatSpatialTotalDerivative horizontal jet) =
      jet (thirdOrderSecondMultiIndex slot horizontal) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

omit [FiniteDimensional Real Fiber] in
@[simp] private theorem secondOrderSecondProjection_totalDerivative
    (first second horizontal : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    secondOrderSecondProjection (Fiber := Fiber) first second
        (throatSpatialTotalDerivative horizontal jet) =
      jet (thirdOrderThirdMultiIndex first second horizontal) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

private theorem thirdOrderThirdMultiIndex_last_comm
    (first second third : Fin 3) :
    thirdOrderThirdMultiIndex first second third =
      thirdOrderThirdMultiIndex first third second := by
  apply Subtype.ext
  dsimp [thirdOrderThirdMultiIndex]
  ac_rfl

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

private abbrev second00 : ThroatSpatialTruncatedIndex 2 :=
  programPT06SecondOrderSecondMultiIndex 0 0

private abbrev second01 : ThroatSpatialTruncatedIndex 2 :=
  programPT06SecondOrderSecondMultiIndex 0 1

private abbrev second02 : ThroatSpatialTruncatedIndex 2 :=
  programPT06SecondOrderSecondMultiIndex 0 2

private abbrev second11 : ThroatSpatialTruncatedIndex 2 :=
  programPT06SecondOrderSecondMultiIndex 1 1

private abbrev second12 : ThroatSpatialTruncatedIndex 2 :=
  programPT06SecondOrderSecondMultiIndex 1 2

private abbrev second22 : ThroatSpatialTruncatedIndex 2 :=
  programPT06SecondOrderSecondMultiIndex 2 2

@[simp] private theorem second10_eq_second01 :
    programPT06SecondOrderSecondMultiIndex 1 0 = second01 :=
  programPT06SecondOrderSecondMultiIndex_comm 1 0

@[simp] private theorem second20_eq_second02 :
    programPT06SecondOrderSecondMultiIndex 2 0 = second02 :=
  programPT06SecondOrderSecondMultiIndex_comm 2 0

@[simp] private theorem second21_eq_second12 :
    programPT06SecondOrderSecondMultiIndex 2 1 = second12 :=
  programPT06SecondOrderSecondMultiIndex_comm 2 1

private theorem secondOrderSecondMultiIndex_ne_of_coordinate
    (first second otherFirst otherSecond coordinate : Fin 3)
    (hCoordinate :
      (throatSpatialCoordinateMultiIndex first +
          throatSpatialCoordinateMultiIndex second) coordinate ≠
        (throatSpatialCoordinateMultiIndex otherFirst +
          throatSpatialCoordinateMultiIndex otherSecond) coordinate) :
    programPT06SecondOrderSecondMultiIndex first second ≠
      programPT06SecondOrderSecondMultiIndex otherFirst otherSecond := by
  intro hIndex
  apply hCoordinate
  exact congrArg
    (fun index : ThroatSpatialTruncatedIndex 2 => index.val coordinate) hIndex

@[simp] private theorem second00_ne_second01 : second00 ≠ second01 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 0 0 1 1
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second00_ne_second02 : second00 ≠ second02 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 0 0 2 2
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second00_ne_second11 : second00 ≠ second11 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 0 1 1 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second00_ne_second12 : second00 ≠ second12 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 0 1 2 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second00_ne_second22 : second00 ≠ second22 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 0 2 2 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second01_ne_second02 : second01 ≠ second02 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 1 0 2 1
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second01_ne_second11 : second01 ≠ second11 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 1 1 1 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second01_ne_second12 : second01 ≠ second12 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 1 1 2 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second01_ne_second22 : second01 ≠ second22 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 1 2 2 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second02_ne_second11 : second02 ≠ second11 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 2 1 1 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second02_ne_second12 : second02 ≠ second12 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 2 1 2 1
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second02_ne_second22 : second02 ≠ second22 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 0 2 2 2 0
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second11_ne_second12 : second11 ≠ second12 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 1 1 1 2 2
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second11_ne_second22 : second11 ≠ second22 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 1 1 2 2 1
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second12_ne_second22 : second12 ≠ second22 := by
  apply secondOrderSecondMultiIndex_ne_of_coordinate 1 2 2 2 1
  simp [throatSpatialCoordinateMultiIndex]

@[simp] private theorem second01_ne_second00 : second01 ≠ second00 :=
  Ne.symm second00_ne_second01

@[simp] private theorem second02_ne_second00 : second02 ≠ second00 :=
  Ne.symm second00_ne_second02

@[simp] private theorem second11_ne_second00 : second11 ≠ second00 :=
  Ne.symm second00_ne_second11

@[simp] private theorem second12_ne_second00 : second12 ≠ second00 :=
  Ne.symm second00_ne_second12

@[simp] private theorem second22_ne_second00 : second22 ≠ second00 :=
  Ne.symm second00_ne_second22

@[simp] private theorem second02_ne_second01 : second02 ≠ second01 :=
  Ne.symm second01_ne_second02

@[simp] private theorem second11_ne_second01 : second11 ≠ second01 :=
  Ne.symm second01_ne_second11

@[simp] private theorem second12_ne_second01 : second12 ≠ second01 :=
  Ne.symm second01_ne_second12

@[simp] private theorem second22_ne_second01 : second22 ≠ second01 :=
  Ne.symm second01_ne_second22

@[simp] private theorem second11_ne_second02 : second11 ≠ second02 :=
  Ne.symm second02_ne_second11

@[simp] private theorem second12_ne_second02 : second12 ≠ second02 :=
  Ne.symm second02_ne_second12

@[simp] private theorem second22_ne_second02 : second22 ≠ second02 :=
  Ne.symm second02_ne_second22

@[simp] private theorem second12_ne_second11 : second12 ≠ second11 :=
  Ne.symm second11_ne_second12

@[simp] private theorem second22_ne_second11 : second22 ≠ second11 :=
  Ne.symm second11_ne_second22

@[simp] private theorem second22_ne_second12 : second22 ≠ second12 :=
  Ne.symm second12_ne_second22

private def pairSelection
    (coordinate index : ThroatSpatialTruncatedIndex 2) : Real :=
  programPT06ThroatSpatialJetCoordinateInjection index (1 : Real) coordinate

@[simp] private theorem pairSelection_same
    (index : ThroatSpatialTruncatedIndex 2) :
    pairSelection index index = 1 := by
  unfold pairSelection
  exact programPT06ThroatSpatialJetCoordinateInjection_same index 1

@[simp] private theorem pairSelection_of_ne
    (coordinate index : ThroatSpatialTruncatedIndex 2)
    (hCoordinate : coordinate ≠ index) :
    pairSelection coordinate index = 0 := by
  unfold pairSelection
  exact programPT06ThroatSpatialJetCoordinateInjection_of_ne
    index coordinate hCoordinate 1

private theorem weightedPairSelection_contraction
    (targetFirst targetSecond : Fin 3)
    (values : Fin 3 → Fin 3 → Real)
    (hSymmetric : ∀ first second, values first second = values second first) :
    (∑ first : Fin 3, ∑ second : Fin 3,
      programPT06SecondOrderEulerSymmetryWeight first second *
        pairSelection
          (programPT06SecondOrderSecondMultiIndex targetFirst targetSecond)
          (programPT06SecondOrderSecondMultiIndex first second) *
        values first second) = values targetFirst targetSecond := by
  fin_cases targetFirst <;> fin_cases targetSecond <;>
    simp [Fin.sum_univ_three, programPT06SecondOrderEulerSymmetryWeight,
      hSymmetric] <;>
    ring_nf <;>
    simpa using hSymmetric _ _


private def secondOrderAlphaFirst
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  data.alpha.comp
    (secondOrderFirstProjection (Fiber := Fiber) data.alphaBaseDirection)

private def secondOrderAlphaSecond
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (direction : Fin 3) : SecondJet (Fiber := Fiber) →L[Real] Real :=
  data.alpha.comp
    (secondOrderSecondProjection (Fiber := Fiber)
      data.alphaBaseDirection direction)

private def secondOrderBetaSecond
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (direction : Fin 3) : SecondJet (Fiber := Fiber) →L[Real] Real :=
  data.beta.comp
    (secondOrderSecondProjection (Fiber := Fiber)
      data.betaBaseDirection direction)

private def thirdOrderAlphaFirst
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (jet : ThirdJet (Fiber := Fiber)) : Real :=
  data.alpha (jet (thirdOrderFirstMultiIndex data.alphaBaseDirection))

private def thirdOrderAlphaSecond
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber)) : Real :=
  data.alpha
    (jet (thirdOrderSecondMultiIndex data.alphaBaseDirection direction))

private def thirdOrderBetaSecond
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber)) : Real :=
  data.beta
    (jet (thirdOrderSecondMultiIndex data.betaBaseDirection direction))

private def thirdOrderBetaThird
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (first second : Fin 3) (jet : ThirdJet (Fiber := Fiber)) : Real :=
  data.beta
    (jet (thirdOrderThirdMultiIndex data.betaBaseDirection first second))

private theorem thirdOrderBetaThird_comm
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (first second : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    thirdOrderBetaThird data first second jet =
      thirdOrderBetaThird data second first jet := by
  rw [thirdOrderBetaThird, thirdOrderBetaThird,
    thirdOrderThirdMultiIndex_last_comm]

/-- The genuine second-jet gradient-Jacobian density. -/
def programPT06MultifieldGradientJacobianMinorDensityEvaluation
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber) :
    SecondJet (Fiber := Fiber) → Real :=
  fun jet =>
    secondOrderAlphaSecond data data.firstDirection jet *
        secondOrderBetaSecond data data.secondDirection jet -
      secondOrderAlphaSecond data data.secondDirection jet *
        secondOrderBetaSecond data data.firstDirection jet

private def densityDerivative
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  secondOrderBetaSecond data data.secondDirection jet •
      secondOrderAlphaSecond data data.firstDirection +
    secondOrderAlphaSecond data data.firstDirection jet •
      secondOrderBetaSecond data data.secondDirection -
    (secondOrderBetaSecond data data.firstDirection jet •
        secondOrderAlphaSecond data data.secondDirection +
      secondOrderAlphaSecond data data.secondDirection jet •
        secondOrderBetaSecond data data.firstDirection)

theorem programPT06MultifieldGradientJacobianMinorDensity_hasFDerivAt
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    HasFDerivAt
      (programPT06MultifieldGradientJacobianMinorDensityEvaluation data)
      (densityDerivative data jet) jet := by
  have hRaw :=
    (((secondOrderAlphaSecond data data.firstDirection).hasFDerivAt
      (x := jet)).mul
      ((secondOrderBetaSecond data data.secondDirection).hasFDerivAt
        (x := jet))).sub
    (((secondOrderAlphaSecond data data.secondDirection).hasFDerivAt
      (x := jet)).mul
      ((secondOrderBetaSecond data data.firstDirection).hasFDerivAt
        (x := jet)))
  refine hRaw.congr_fderiv ?_
  ext variation
  simp [densityDerivative]
  ring

private theorem verticalPartialZero
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06MultifieldGradientJacobianMinorDensityEvaluation data) = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06MultifieldGradientJacobianMinorDensityEvaluation data) jet
      programPT06SecondOrderZeroMultiIndex = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06MultifieldGradientJacobianMinorDensityEvaluation data) jet
    programPT06SecondOrderZeroMultiIndex (densityDerivative data jet)
    (programPT06MultifieldGradientJacobianMinorDensity_hasFDerivAt data jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [densityDerivative, secondOrderAlphaSecond, secondOrderBetaSecond,
    secondOrderSecondProjection, secondOrderSecondMultiIndex_ne_zero]

private theorem verticalPartialOne
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (direction : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06MultifieldGradientJacobianMinorDensityEvaluation data)
        direction = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06MultifieldGradientJacobianMinorDensityEvaluation data) jet
      (programPT06SecondOrderFirstMultiIndex direction) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06MultifieldGradientJacobianMinorDensityEvaluation data) jet
    (programPT06SecondOrderFirstMultiIndex direction)
    (densityDerivative data jet)
    (programPT06MultifieldGradientJacobianMinorDensity_hasFDerivAt data jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [densityDerivative, secondOrderAlphaSecond, secondOrderBetaSecond,
    secondOrderSecondProjection, secondOrderSecondMultiIndex_ne_first]

omit [FiniteDimensional Real Fiber] in
@[simp] private theorem covector_coordinateInjection_apply
    (functional : Fiber →L[Real] Real)
    (coordinate index : ThroatSpatialTruncatedIndex 2) (variation : Fiber) :
    functional
        (programPT06ThroatSpatialJetCoordinateInjection index variation
          coordinate) =
      pairSelection coordinate index * functional variation := by
  by_cases hCoordinate : coordinate = index
  · subst coordinate
    simp [pairSelection]
  · simp [pairSelection, hCoordinate]

private def selectedCovector
    (functional : Fiber →L[Real] Real)
    (targetFirst targetSecond actualFirst actualSecond : Fin 3) :
    Fiber →L[Real] Real :=
  pairSelection
      (programPT06SecondOrderSecondMultiIndex targetFirst targetSecond)
      (programPT06SecondOrderSecondMultiIndex actualFirst actualSecond) •
    functional

private def verticalTwoLinearMap
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (first second : Fin 3) :
    SecondJet (Fiber := Fiber) →L[Real] (Fiber →L[Real] Real) :=
  (secondOrderBetaSecond data data.secondDirection).smulRight
      (selectedCovector data.alpha data.alphaBaseDirection data.firstDirection
        first second) +
    (secondOrderAlphaSecond data data.firstDirection).smulRight
      (selectedCovector data.beta data.betaBaseDirection data.secondDirection
        first second) -
    ((secondOrderBetaSecond data data.firstDirection).smulRight
        (selectedCovector data.alpha data.alphaBaseDirection data.secondDirection
          first second) +
      (secondOrderAlphaSecond data data.secondDirection).smulRight
        (selectedCovector data.beta data.betaBaseDirection data.firstDirection
          first second))

private theorem verticalPartialTwo
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06MultifieldGradientJacobianMinorDensityEvaluation data)
        first second = verticalTwoLinearMap data first second := by
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06MultifieldGradientJacobianMinorDensityEvaluation data) jet
      (programPT06SecondOrderSecondMultiIndex first second) variation = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06MultifieldGradientJacobianMinorDensityEvaluation data) jet
    (programPT06SecondOrderSecondMultiIndex first second)
    (densityDerivative data jet)
    (programPT06MultifieldGradientJacobianMinorDensity_hasFDerivAt data jet)]
  simp [densityDerivative, verticalTwoLinearMap, selectedCovector,
    secondOrderAlphaSecond, secondOrderBetaSecond,
    secondOrderSecondProjection]

private def positiveCurrent
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber) :
    SecondJet (Fiber := Fiber) → Real :=
  fun jet =>
    secondOrderAlphaFirst data jet *
      secondOrderBetaSecond data data.secondDirection jet

private def negativeCurrent
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber) :
    SecondJet (Fiber := Fiber) → Real :=
  fun jet =>
    -(secondOrderAlphaFirst data jet *
      secondOrderBetaSecond data data.firstDirection jet)

/-- The order-two current, with exactly the two selected components nonzero. -/
def programPT06MultifieldGradientJacobianMinorCurrentComponent
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (direction : Fin 3) : SecondJet (Fiber := Fiber) → Real :=
  if direction = data.firstDirection then positiveCurrent data
  else if direction = data.secondDirection then negativeCurrent data
  else 0

/-- Every component of the explicit order-two current is differentiable. -/
theorem programPT06MultifieldGradientJacobianMinorCurrentComponent_differentiable
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (direction : Fin 3) :
    Differentiable Real
      (programPT06MultifieldGradientJacobianMinorCurrentComponent
        data direction) := by
  by_cases hFirst : direction = data.firstDirection
  · subst direction
    simp only [programPT06MultifieldGradientJacobianMinorCurrentComponent,
      if_pos]
    exact (secondOrderAlphaFirst data).differentiable.mul
      (secondOrderBetaSecond data data.secondDirection).differentiable
  · by_cases hSecond : direction = data.secondDirection
    · subst direction
      simp only [programPT06MultifieldGradientJacobianMinorCurrentComponent,
        hFirst, if_false, if_pos]
      exact ((secondOrderAlphaFirst data).differentiable.mul
        (secondOrderBetaSecond data data.firstDirection).differentiable).neg
    · simp only [programPT06MultifieldGradientJacobianMinorCurrentComponent,
        hFirst, hSecond, if_false]
      fun_prop

private def positiveCurrentDerivative
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  secondOrderBetaSecond data data.secondDirection jet •
      secondOrderAlphaFirst data +
    secondOrderAlphaFirst data jet •
      secondOrderBetaSecond data data.secondDirection

private theorem positiveCurrent_hasFDerivAt
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    HasFDerivAt (positiveCurrent data) (positiveCurrentDerivative data jet) jet := by
  have hRaw := ((secondOrderAlphaFirst data).hasFDerivAt (x := jet)).mul
    ((secondOrderBetaSecond data data.secondDirection).hasFDerivAt (x := jet))
  refine hRaw.congr_fderiv ?_
  ext variation
  simp [positiveCurrentDerivative]
  ring

private def negativeCurrentDerivative
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  -(secondOrderBetaSecond data data.firstDirection jet •
      secondOrderAlphaFirst data +
    secondOrderAlphaFirst data jet •
      secondOrderBetaSecond data data.firstDirection)

private theorem negativeCurrent_hasFDerivAt
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (jet : SecondJet (Fiber := Fiber)) :
    HasFDerivAt (negativeCurrent data) (negativeCurrentDerivative data jet) jet := by
  have hRaw := (((secondOrderAlphaFirst data).hasFDerivAt (x := jet)).mul
    ((secondOrderBetaSecond data data.firstDirection).hasFDerivAt
      (x := jet))).neg
  refine hRaw.congr_fderiv ?_
  ext variation
  simp [negativeCurrentDerivative]
  ring

private theorem positiveCurrent_totalDerivative
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (horizontal : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative horizontal
        (positiveCurrent data) jet =
      thirdOrderAlphaSecond data horizontal jet *
          thirdOrderBetaSecond data data.secondDirection jet +
        thirdOrderAlphaFirst data jet *
          thirdOrderBetaThird data data.secondDirection horizontal jet := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    horizontal _ jet
    (positiveCurrentDerivative data
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))
    (positiveCurrent_hasFDerivAt data
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  simp [positiveCurrentDerivative, secondOrderAlphaFirst,
    secondOrderBetaSecond, thirdOrderAlphaFirst, thirdOrderAlphaSecond,
    thirdOrderBetaSecond, thirdOrderBetaThird]
  ring

private theorem negativeCurrent_totalDerivative
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (horizontal : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative horizontal
        (negativeCurrent data) jet =
      -(thirdOrderAlphaSecond data horizontal jet *
          thirdOrderBetaSecond data data.firstDirection jet +
        thirdOrderAlphaFirst data jet *
          thirdOrderBetaThird data data.firstDirection horizontal jet) := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    horizontal _ jet
    (negativeCurrentDerivative data
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))
    (negativeCurrent_hasFDerivAt data
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))]
  simp [negativeCurrentDerivative, secondOrderAlphaFirst,
    secondOrderBetaSecond, thirdOrderAlphaFirst, thirdOrderAlphaSecond,
    thirdOrderBetaSecond, thirdOrderBetaThird]
  ring

private theorem currentComponent_totalDerivative
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (programPT06MultifieldGradientJacobianMinorCurrentComponent
          data direction) jet =
      if direction = data.firstDirection then
        thirdOrderAlphaSecond data direction jet *
            thirdOrderBetaSecond data data.secondDirection jet +
          thirdOrderAlphaFirst data jet *
            thirdOrderBetaThird data data.secondDirection direction jet
      else if direction = data.secondDirection then
        -(thirdOrderAlphaSecond data direction jet *
            thirdOrderBetaSecond data data.firstDirection jet +
          thirdOrderAlphaFirst data jet *
            thirdOrderBetaThird data data.firstDirection direction jet)
      else 0 := by
  by_cases hFirst : direction = data.firstDirection
  · subst direction
    rw [show
      programPT06MultifieldGradientJacobianMinorCurrentComponent
          data data.firstDirection = positiveCurrent data by
        simp [programPT06MultifieldGradientJacobianMinorCurrentComponent]]
    rw [positiveCurrent_totalDerivative]
    simp
  · by_cases hSecond : direction = data.secondDirection
    · subst direction
      rw [show
        programPT06MultifieldGradientJacobianMinorCurrentComponent
            data data.secondDirection = negativeCurrent data by
          simp [programPT06MultifieldGradientJacobianMinorCurrentComponent,
            hFirst]]
      rw [negativeCurrent_totalDerivative]
      simp [hFirst]
    · rw [show
        programPT06MultifieldGradientJacobianMinorCurrentComponent
            data direction = 0 by
          simp [programPT06MultifieldGradientJacobianMinorCurrentComponent,
            hFirst, hSecond]]
      simp [hFirst, hSecond]

private theorem finThree_sum_two_ite
    {Target : Type*} [AddCommMonoid Target]
    (first second : Fin 3) (hDirections : first ≠ second)
    (positive negative : Fin 3 → Target) :
    (∑ direction : Fin 3,
      if direction = first then positive direction
      else if direction = second then negative direction
      else 0) = positive first + negative second := by
  calc
    _ = ∑ direction : Fin 3,
        ((if direction = first then positive direction else 0) +
          (if direction = second then negative direction else 0)) := by
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
      rw [Fintype.sum_ite_eq' first positive,
        Fintype.sum_ite_eq' second negative]

/-- Genuine Gate879 horizontal differential of the explicit order-two
current, evaluated on third jets. -/
def programPT06MultifieldGradientJacobianMinorCurrentDH
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber) :
    ThirdJet (Fiber := Fiber) → Real :=
  fun jet => ∑ direction : Fin 3,
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
      (programPT06MultifieldGradientJacobianMinorCurrentComponent
        data direction) jet

/-- The third-order current terms cancel and the genuine Gate879 horizontal
differential equals the pulled-back gradient-Jacobian minor. -/
theorem programPT06MultifieldGradientJacobianMinorCurrentDH_eq_density
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (jet : ThirdJet (Fiber := Fiber)) :
    programPT06MultifieldGradientJacobianMinorCurrentDH data jet =
      programPT06MultifieldGradientJacobianMinorDensityEvaluation data
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) := by
  unfold programPT06MultifieldGradientJacobianMinorCurrentDH
  simp_rw [currentComponent_totalDerivative]
  rw [finThree_sum_two_ite data.firstDirection data.secondDirection
    data.directions_ne]
  rw [thirdOrderBetaThird_comm data
    data.secondDirection data.firstDirection jet]
  simp [programPT06MultifieldGradientJacobianMinorDensityEvaluation,
    secondOrderAlphaSecond, secondOrderBetaSecond, thirdOrderAlphaSecond,
    thirdOrderBetaSecond]
  ring

private def firstTotalLinearMap
    (direction : Fin 3)
    (linear : SecondJet (Fiber := Fiber) →L[Real] (Fiber →L[Real] Real)) :
    ThirdJet (Fiber := Fiber) →L[Real] (Fiber →L[Real] Real) :=
  (linear.toLinearMap.comp
    (throatSpatialTotalDerivativeLinear direction)).toContinuousLinearMap

private theorem firstTotalDerivative_linear
    (direction : Fin 3)
    (linear : SecondJet (Fiber := Fiber) →L[Real] (Fiber →L[Real] Real)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction linear =
      firstTotalLinearMap direction linear := by
  funext jet
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_linear]
  rfl

private theorem iteratedTotalDerivative_linear
    (first second : Fin 3)
    (linear : SecondJet (Fiber := Fiber) →L[Real] (Fiber →L[Real] Real))
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative first
        (programPT06ThroatSpatialLocalFunctionTotalDerivative second linear)
        jet =
      linear
        (throatSpatialTotalDerivative second
          (throatSpatialTotalDerivative first jet)) := by
  rw [firstTotalDerivative_linear]
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_linear]
  rfl

private def iteratedAlpha
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (slot : Fin 3) (jet : FourthJet (Fiber := Fiber))
    (first second : Fin 3) : Real :=
  secondOrderAlphaSecond data slot
    (throatSpatialTotalDerivative second
      (throatSpatialTotalDerivative first jet))

private def iteratedBeta
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (slot : Fin 3) (jet : FourthJet (Fiber := Fiber))
    (first second : Fin 3) : Real :=
  secondOrderBetaSecond data slot
    (throatSpatialTotalDerivative second
      (throatSpatialTotalDerivative first jet))

omit [FiniteDimensional Real Fiber] in
private theorem secondOrderSecondProjection_iterated_comm
    (base slot first second : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    secondOrderSecondProjection (Fiber := Fiber) base slot
        (throatSpatialTotalDerivative second
          (throatSpatialTotalDerivative first jet)) =
      secondOrderSecondProjection (Fiber := Fiber) base slot
        (throatSpatialTotalDerivative first
          (throatSpatialTotalDerivative second jet)) := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [programPT06SecondOrderSecondMultiIndex]
  ac_rfl

private theorem iteratedAlpha_symmetric
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (slot : Fin 3) (jet : FourthJet (Fiber := Fiber))
    (first second : Fin 3) :
    iteratedAlpha data slot jet first second =
      iteratedAlpha data slot jet second first := by
  unfold iteratedAlpha secondOrderAlphaSecond
  exact congrArg data.alpha
    (secondOrderSecondProjection_iterated_comm
      data.alphaBaseDirection slot first second jet)

private theorem iteratedBeta_symmetric
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (slot : Fin 3) (jet : FourthJet (Fiber := Fiber))
    (first second : Fin 3) :
    iteratedBeta data slot jet first second =
      iteratedBeta data slot jet second first := by
  unfold iteratedBeta secondOrderBetaSecond
  exact congrArg data.beta
    (secondOrderSecondProjection_iterated_comm
      data.betaBaseDirection slot first second jet)

private theorem secondEulerTerm_apply
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (first second : Fin 3) (jet : FourthJet (Fiber := Fiber))
    (variation : Fiber) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06MultifieldGradientJacobianMinorDensityEvaluation data)
        first second jet variation =
      pairSelection
          (programPT06SecondOrderSecondMultiIndex
            data.alphaBaseDirection data.firstDirection)
          (programPT06SecondOrderSecondMultiIndex first second) *
          (iteratedBeta data data.secondDirection jet first second *
            data.alpha variation) +
        pairSelection
          (programPT06SecondOrderSecondMultiIndex
            data.betaBaseDirection data.secondDirection)
          (programPT06SecondOrderSecondMultiIndex first second) *
          (iteratedAlpha data data.firstDirection jet first second *
            data.beta variation) -
        (pairSelection
            (programPT06SecondOrderSecondMultiIndex
              data.alphaBaseDirection data.secondDirection)
            (programPT06SecondOrderSecondMultiIndex first second) *
            (iteratedBeta data data.firstDirection jet first second *
              data.alpha variation) +
          pairSelection
            (programPT06SecondOrderSecondMultiIndex
              data.betaBaseDirection data.firstDirection)
            (programPT06SecondOrderSecondMultiIndex first second) *
            (iteratedAlpha data data.secondDirection jet first second *
              data.beta variation)) := by
  rw [programPT06SecondOrderLocalEulerSecondTotalTerm, verticalPartialTwo]
  rw [iteratedTotalDerivative_linear]
  simp [verticalTwoLinearMap, selectedCovector, iteratedAlpha, iteratedBeta]
  ring

private theorem betaFourthCancellation
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (jet : FourthJet (Fiber := Fiber)) :
    iteratedBeta data data.secondDirection jet
        data.alphaBaseDirection data.firstDirection =
      iteratedBeta data data.firstDirection jet
        data.alphaBaseDirection data.secondDirection := by
  unfold iteratedBeta secondOrderBetaSecond
  apply congrArg data.beta
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [programPT06SecondOrderSecondMultiIndex]
  ac_rfl

private theorem alphaFourthCancellation
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (jet : FourthJet (Fiber := Fiber)) :
    iteratedAlpha data data.firstDirection jet
        data.betaBaseDirection data.secondDirection =
      iteratedAlpha data data.secondDirection jet
        data.betaBaseDirection data.firstDirection := by
  unfold iteratedAlpha secondOrderAlphaSecond
  apply congrArg data.alpha
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  dsimp [programPT06SecondOrderSecondMultiIndex]
  ac_rfl

private theorem secondEulerSum_apply
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (jet : FourthJet (Fiber := Fiber)) (variation : Fiber) :
    (∑ first : Fin 3, ∑ second : Fin 3,
      programPT06SecondOrderEulerSymmetryWeight first second •
        programPT06SecondOrderLocalEulerSecondTotalTerm
          (programPT06MultifieldGradientJacobianMinorDensityEvaluation data)
          first second jet variation) = 0 := by
  let alphaPositive : Fin 3 → Fin 3 → Real := fun first second =>
    iteratedBeta data data.secondDirection jet first second *
      data.alpha variation
  let betaPositive : Fin 3 → Fin 3 → Real := fun first second =>
    iteratedAlpha data data.firstDirection jet first second *
      data.beta variation
  let alphaNegative : Fin 3 → Fin 3 → Real := fun first second =>
    iteratedBeta data data.firstDirection jet first second *
      data.alpha variation
  let betaNegative : Fin 3 → Fin 3 → Real := fun first second =>
    iteratedAlpha data data.secondDirection jet first second *
      data.beta variation
  have hAlphaPositive := weightedPairSelection_contraction
    data.alphaBaseDirection data.firstDirection alphaPositive (by
      intro first second
      simp only [alphaPositive]
      rw [iteratedBeta_symmetric])
  have hBetaPositive := weightedPairSelection_contraction
    data.betaBaseDirection data.secondDirection betaPositive (by
      intro first second
      simp only [betaPositive]
      rw [iteratedAlpha_symmetric])
  have hAlphaNegative := weightedPairSelection_contraction
    data.alphaBaseDirection data.secondDirection alphaNegative (by
      intro first second
      simp only [alphaNegative]
      rw [iteratedBeta_symmetric])
  have hBetaNegative := weightedPairSelection_contraction
    data.betaBaseDirection data.firstDirection betaNegative (by
      intro first second
      simp only [betaNegative]
      rw [iteratedAlpha_symmetric])
  simp_rw [secondEulerTerm_apply]
  simp only [smul_eq_mul]
  change
    (∑ first : Fin 3, ∑ second : Fin 3,
      programPT06SecondOrderEulerSymmetryWeight first second *
        (pairSelection
              (programPT06SecondOrderSecondMultiIndex
                data.alphaBaseDirection data.firstDirection)
              (programPT06SecondOrderSecondMultiIndex first second) *
              alphaPositive first second +
          pairSelection
              (programPT06SecondOrderSecondMultiIndex
                data.betaBaseDirection data.secondDirection)
              (programPT06SecondOrderSecondMultiIndex first second) *
              betaPositive first second -
          (pairSelection
                (programPT06SecondOrderSecondMultiIndex
                  data.alphaBaseDirection data.secondDirection)
                (programPT06SecondOrderSecondMultiIndex first second) *
                alphaNegative first second +
            pairSelection
                (programPT06SecondOrderSecondMultiIndex
                  data.betaBaseDirection data.firstDirection)
                (programPT06SecondOrderSecondMultiIndex first second) *
                betaNegative first second))) = 0
  calc
    _ =
        (∑ first : Fin 3, ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight first second *
            pairSelection
              (programPT06SecondOrderSecondMultiIndex
                data.alphaBaseDirection data.firstDirection)
              (programPT06SecondOrderSecondMultiIndex first second) *
            alphaPositive first second) +
        (∑ first : Fin 3, ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight first second *
            pairSelection
              (programPT06SecondOrderSecondMultiIndex
                data.betaBaseDirection data.secondDirection)
              (programPT06SecondOrderSecondMultiIndex first second) *
            betaPositive first second) -
        ((∑ first : Fin 3, ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight first second *
            pairSelection
              (programPT06SecondOrderSecondMultiIndex
                data.alphaBaseDirection data.secondDirection)
              (programPT06SecondOrderSecondMultiIndex first second) *
            alphaNegative first second) +
        (∑ first : Fin 3, ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight first second *
            pairSelection
              (programPT06SecondOrderSecondMultiIndex
                data.betaBaseDirection data.firstDirection)
              (programPT06SecondOrderSecondMultiIndex first second) *
            betaNegative first second)) := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      ring
    _ = alphaPositive data.alphaBaseDirection data.firstDirection +
          betaPositive data.betaBaseDirection data.secondDirection -
          (alphaNegative data.alphaBaseDirection data.secondDirection +
            betaNegative data.betaBaseDirection data.firstDirection) := by
      rw [hAlphaPositive, hBetaPositive, hAlphaNegative, hBetaNegative]
    _ = 0 := by
      simp only [alphaPositive, betaPositive, alphaNegative, betaNegative]
      rw [betaFourthCancellation data jet, alphaFourthCancellation data jet]
      ring

/-- Gate880 directly annihilates every generic gradient-Jacobian minor.  The
weighted slot contraction includes diagonal, off-diagonal, and aliased pairs. -/
theorem programPT06SecondOrderLocalEuler_multifieldGradientJacobianMinor_eq_zero
    (data : ProgramPT06MultifieldGradientJacobianMinorData4D Fiber)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06MultifieldGradientJacobianMinorDensityEvaluation data)
        jet = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  rw [programPT06SecondOrderLocalEuler_apply, verticalPartialZero]
  have hFirst :
      (∑ direction : Fin 3,
        programPT06SecondOrderLocalEulerFirstTotalTerm
          (programPT06MultifieldGradientJacobianMinorDensityEvaluation data)
          direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)
          variation) = 0 := by
    apply Finset.sum_eq_zero
    intro direction _
    rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
      verticalPartialOne]
    simp
  rw [hFirst, secondEulerSum_apply data jet variation]
  simp


/-- The scalar Hessian minor is the specialization `alpha = beta = id`,
`p = i`, `q = j`. -/
def programPT06MultifieldGradientJacobianOfScalarHessianMinor
    (minor : ProgramPT06ScalarHessianMinor4D) :
    ProgramPT06MultifieldGradientJacobianMinorData4D Real where
  alpha := ContinuousLinearMap.id Real Real
  beta := ContinuousLinearMap.id Real Real
  alphaBaseDirection := minor.first
  betaBaseDirection := minor.second
  firstDirection := minor.first
  secondDirection := minor.second
  directions_ne := minor.distinct

theorem programPT06MultifieldGradientJacobian_scalarHessianMinor_density
    (minor : ProgramPT06ScalarHessianMinor4D) :
    programPT06MultifieldGradientJacobianMinorDensityEvaluation
        (programPT06MultifieldGradientJacobianOfScalarHessianMinor minor) =
      programPT06ScalarHessianMinorDensityEvaluation minor := by
  funext jet
  rw [programPT06ScalarHessianMinorDensityEvaluation_apply]
  simp [programPT06MultifieldGradientJacobianMinorDensityEvaluation,
    programPT06MultifieldGradientJacobianOfScalarHessianMinor,
    secondOrderAlphaSecond, secondOrderBetaSecond,
    secondOrderSecondProjection,
    programPT06SecondOrderSecondMultiIndex_comm, pow_two]

theorem programPT06MultifieldGradientJacobian_scalarHessianMinor_currentDH
    (minor : ProgramPT06ScalarHessianMinor4D)
    (jet : ThroatSpatialMultiindexJet3 Real) :
    programPT06MultifieldGradientJacobianMinorCurrentDH
        (programPT06MultifieldGradientJacobianOfScalarHessianMinor minor) jet =
      programPT06ScalarHessianMinorDensityEvaluation minor
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) := by
  rw [programPT06MultifieldGradientJacobianMinorCurrentDH_eq_density]
  exact congrFun
    (programPT06MultifieldGradientJacobian_scalarHessianMinor_density minor)
    (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)

/-- Gate880 vanishes on the scalar Hessian-minor specialization, consistently
with both direct computations. -/
theorem programPT06SecondOrderLocalEuler_gradientJacobian_scalarSpecialization_eq_zero
    (minor : ProgramPT06ScalarHessianMinor4D)
    (jet : ThroatSpatialMultiindexJet4 Real) :
    programPT06SecondOrderLocalEuler
          (programPT06MultifieldGradientJacobianMinorDensityEvaluation
            (programPT06MultifieldGradientJacobianOfScalarHessianMinor minor))
          jet = 0 := by
  rw [programPT06MultifieldGradientJacobian_scalarHessianMinor_density]
  exact programPT06SecondOrderLocalEuler_scalarHessianMinor_eq_zero minor jet

end
end P0EFTJanusProgramPT06MultifieldGradientJacobianMinorNullLagrangian4D
end JanusFormal
