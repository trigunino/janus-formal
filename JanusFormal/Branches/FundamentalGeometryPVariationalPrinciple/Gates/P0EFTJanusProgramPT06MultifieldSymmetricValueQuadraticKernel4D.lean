import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06MultifieldFirstOrderQuadraticKernel4D

/-!
# An arbitrary symmetric value-quadratic Euler kernel

This gate extends the normalized rank-one value square of Gate908 to an
arbitrary continuous symmetric bilinear form on a finite-dimensional real
normed fiber.  The density also contains a constant, an arbitrary linear
value coefficient, and every three-direction finite-rank bilinear value
current from Gate898.  The current supplies mixed `u`--`u_i` terms.

The genuine Gate880 Euler operator is computed directly from Frechet
derivatives.  It vanishes exactly when the linear value coefficient and the
whole symmetric bilinear value form vanish.  In that case the density is its
constant plus the genuine Gate898 horizontal divergence, giving an explicit
algebraic homotopy on this multifield subclass.

Gradient-gradient couplings, genuine second-jet densities, geometric
invariance or covariance, and polynomial degrees three and four remain open.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06MultifieldSymmetricValueQuadraticKernel4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D
open P0EFTJanusProgramPT06FiniteRankBilinearValueCurrent4D
open P0EFTJanusProgramPT06MultifieldFirstOrderQuadraticKernel4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u v

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
  [FiniteDimensional Real Fiber]
variable {Rank : Type v} [Fintype Rank]

private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- A multifield density with an arbitrary symmetric value bilinear form and
a full Gate898 finite-rank boundary current. -/
structure ProgramPT06MultifieldSymmetricValueQuadraticDensity4D
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber]
    (Rank : Type v) [Fintype Rank] where
  constant : Real
  valueLinear : Fiber →L[Real] Real
  valueQuadratic : Fiber →L[Real] (Fiber →L[Real] Real)
  valueQuadratic_symmetric : forall first second,
    valueQuadratic first second = valueQuadratic second first
  boundaryCurrent : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank

private def secondOrderValueProjection :
    SecondJet (Fiber := Fiber) →L[Real] Fiber :=
  ContinuousLinearMap.proj programPT06SecondOrderZeroMultiIndex

private def secondOrderLinearValueCovector
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  density.valueLinear.comp (secondOrderValueProjection (Fiber := Fiber))

private def fourthOrderZeroMultiIndex : ThroatSpatialTruncatedIndex 4 :=
  ⟨0, by simp⟩

omit [FiniteDimensional Real Fiber] in
@[simp] private theorem secondOrderValueProjection_truncate_fourth
    (jet : FourthJet (Fiber := Fiber)) :
    secondOrderValueProjection (Fiber := Fiber)
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet) =
      jet fourthOrderZeroMultiIndex := by
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

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

/-- The stored quadratic coefficient is symmetric in its two fiber slots. -/
theorem programPT06MultifieldSymmetricValueQuadratic_valueQuadratic_symmetric
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (first second : Fiber) :
    density.valueQuadratic first second =
      density.valueQuadratic second first :=
  density.valueQuadratic_symmetric first second

private def programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank) :
    SecondJet (Fiber := Fiber) -> Real :=
  fun jet =>
    density.constant + secondOrderLinearValueCovector density jet +
      density.valueQuadratic
        (secondOrderValueProjection (Fiber := Fiber) jet)
        (secondOrderValueProjection (Fiber := Fiber) jet) / 2

/-- Evaluation of the complete autonomous first-order quadratic density. -/
def programPT06MultifieldSymmetricValueQuadraticDensityEvaluation
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank) :
    SecondJet (Fiber := Fiber) -> Real :=
  fun jet =>
    programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density jet +
      programPT06FiniteRankBilinearValueDensityEvaluation
        density.boundaryCurrent jet

private def programPT06MultifieldSymmetricValueQuadraticObstructionDerivative
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (jet : SecondJet (Fiber := Fiber)) :
    SecondJet (Fiber := Fiber) →L[Real] Real :=
  secondOrderLinearValueCovector density +
    (density.valueQuadratic
      (secondOrderValueProjection (Fiber := Fiber) jet)).comp
        (secondOrderValueProjection (Fiber := Fiber))

private theorem
    programPT06MultifieldSymmetricValueQuadraticObstruction_hasFDerivAt
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (jet : SecondJet (Fiber := Fiber)) :
    HasFDerivAt
      (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density)
      (programPT06MultifieldSymmetricValueQuadraticObstructionDerivative density jet)
      jet := by
  have hQuadratic :=
    (((density.valueQuadratic.comp
          (secondOrderValueProjection (Fiber := Fiber))).hasFDerivAt
        (x := jet)).clm_apply
      ((secondOrderValueProjection (Fiber := Fiber)).hasFDerivAt
        (x := jet))).const_mul (1 / 2 : Real)
  have hRaw :=
    ((hasFDerivAt_const (x := jet) (c := density.constant)).add
      (secondOrderLinearValueCovector density).hasFDerivAt).add
        hQuadratic
  convert hRaw using 1
  · funext candidate
    dsimp [programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation]
    ring
  · ext variation
    simp [programPT06MultifieldSymmetricValueQuadraticObstructionDerivative]
    rw [density.valueQuadratic_symmetric
      (secondOrderValueProjection (Fiber := Fiber) variation)
      (secondOrderValueProjection (Fiber := Fiber) jet)]
    ring

private theorem programPT06FiniteRankBoundaryDensity_differentiableAt
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (jet : SecondJet (Fiber := Fiber)) :
    DifferentiableAt Real
      (programPT06FiniteRankBilinearValueDensityEvaluation
        density.boundaryCurrent) jet := by
  unfold programPT06FiniteRankBilinearValueDensityEvaluation
  let derivative : SecondJet (Fiber := Fiber) →L[Real] Real :=
    ∑ index : Fin 3 × Rank,
      density.boundaryCurrent.coefficient index.1 index.2 •
        fderiv Real
          (programPT06DirectedQuadraticValueDensityEvaluation
            (programPT06FiniteRankBilinearValueAtom
              density.boundaryCurrent index)) jet
  have hDerivative : HasFDerivAt
      (fun candidate : SecondJet (Fiber := Fiber) =>
        ∑ index : Fin 3 × Rank,
          density.boundaryCurrent.coefficient index.1 index.2 •
            programPT06DirectedQuadraticValueDensityEvaluation
              (programPT06FiniteRankBilinearValueAtom
                density.boundaryCurrent index) candidate)
      derivative jet := by
    apply HasFDerivAt.fun_sum
    intro index _
    exact
      ((programPT06DirectedQuadraticValueDensityEvaluation_hasFDerivAt
          (programPT06FiniteRankBilinearValueAtom
            density.boundaryCurrent index) jet).differentiableAt.hasFDerivAt).const_smul
          (density.boundaryCurrent.coefficient index.1 index.2)
  exact hDerivative.differentiableAt

private theorem
    programPT06MultifieldSymmetricValueQuadraticVerticalPartial_add
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (jet : SecondJet (Fiber := Fiber))
    (index : ThroatSpatialTruncatedIndex 2) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density)
        jet index =
      programPT06ThroatSpatialVerticalPartialDerivative
          (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density)
          jet index +
        programPT06ThroatSpatialVerticalPartialDerivative
          (programPT06FiniteRankBilinearValueDensityEvaluation
            density.boundaryCurrent) jet index := by
  apply ContinuousLinearMap.ext
  intro variation
  change
    fderiv Real
        (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density +
          programPT06FiniteRankBilinearValueDensityEvaluation
            density.boundaryCurrent)
        jet
        (programPT06ThroatSpatialJetCoordinateInjection index variation) = _
  rw [fderiv_add
    (programPT06MultifieldSymmetricValueQuadraticObstruction_hasFDerivAt
      density jet).differentiableAt
    (programPT06FiniteRankBoundaryDensity_differentiableAt density jet)]
  rfl

private theorem
    programPT06MultifieldSymmetricValueQuadraticObstructionVerticalPartialZero
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (jet : SecondJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density)
        jet =
      density.valueLinear +
        density.valueQuadratic
          (secondOrderValueProjection (Fiber := Fiber) jet) := by
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density) jet
      programPT06SecondOrderZeroMultiIndex = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density) jet
    programPT06SecondOrderZeroMultiIndex
    (programPT06MultifieldSymmetricValueQuadraticObstructionDerivative density jet)
    (programPT06MultifieldSymmetricValueQuadraticObstruction_hasFDerivAt density jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06MultifieldSymmetricValueQuadraticObstructionDerivative,
    secondOrderLinearValueCovector,
    secondOrderValueProjection]

private theorem
    programPT06MultifieldSymmetricValueQuadraticObstructionVerticalPartialOne
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (direction : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density)
        direction = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density) jet
      (programPT06SecondOrderFirstMultiIndex direction) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density) jet
    (programPT06SecondOrderFirstMultiIndex direction)
    (programPT06MultifieldSymmetricValueQuadraticObstructionDerivative density jet)
    (programPT06MultifieldSymmetricValueQuadraticObstruction_hasFDerivAt density jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06MultifieldSymmetricValueQuadraticObstructionDerivative,
    secondOrderLinearValueCovector,
    secondOrderValueProjection,
    Ne.symm (secondOrderFirstMultiIndex_ne_zero direction)]

private theorem
    programPT06MultifieldSymmetricValueQuadraticObstructionVerticalPartialTwo
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density)
        first second = 0 := by
  funext jet
  change programPT06ThroatSpatialVerticalPartialDerivative
    (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density) jet
      (programPT06SecondOrderSecondMultiIndex first second) = _
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density) jet
    (programPT06SecondOrderSecondMultiIndex first second)
    (programPT06MultifieldSymmetricValueQuadraticObstructionDerivative density jet)
    (programPT06MultifieldSymmetricValueQuadraticObstruction_hasFDerivAt density jet)]
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06MultifieldSymmetricValueQuadraticObstructionDerivative,
    secondOrderLinearValueCovector,
    secondOrderValueProjection,
    Ne.symm (secondOrderSecondMultiIndex_ne_zero first second)]

private theorem programPT06MultifieldSymmetricValueQuadraticVerticalPartialZero
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density) =
      fun jet =>
        density.valueLinear +
          density.valueQuadratic
            (secondOrderValueProjection (Fiber := Fiber) jet) +
          programPT06SecondOrderLocalVerticalPartialZero
            (programPT06FiniteRankBilinearValueDensityEvaluation
              density.boundaryCurrent) jet := by
  funext jet
  rw [show
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density) jet =
      programPT06SecondOrderLocalVerticalPartialZero
          (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density)
          jet +
        programPT06SecondOrderLocalVerticalPartialZero
          (programPT06FiniteRankBilinearValueDensityEvaluation
            density.boundaryCurrent) jet from
      programPT06MultifieldSymmetricValueQuadraticVerticalPartial_add density jet
        programPT06SecondOrderZeroMultiIndex]
  rw [programPT06MultifieldSymmetricValueQuadraticObstructionVerticalPartialZero]

private theorem programPT06MultifieldSymmetricValueQuadraticVerticalPartialOne
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (direction : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density)
        direction =
      programPT06SecondOrderLocalVerticalPartialOne
        (programPT06FiniteRankBilinearValueDensityEvaluation
          density.boundaryCurrent) direction := by
  funext jet
  rw [show
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density)
        direction jet =
      programPT06SecondOrderLocalVerticalPartialOne
          (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density)
          direction jet +
        programPT06SecondOrderLocalVerticalPartialOne
          (programPT06FiniteRankBilinearValueDensityEvaluation
            density.boundaryCurrent) direction jet from
      programPT06MultifieldSymmetricValueQuadraticVerticalPartial_add density jet
        (programPT06SecondOrderFirstMultiIndex direction)]
  rw [programPT06MultifieldSymmetricValueQuadraticObstructionVerticalPartialOne]
  simp

private theorem programPT06MultifieldSymmetricValueQuadraticVerticalPartialTwo
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density)
        first second =
      programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06FiniteRankBilinearValueDensityEvaluation
          density.boundaryCurrent) first second := by
  funext jet
  rw [show
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density)
        first second jet =
      programPT06SecondOrderLocalVerticalPartialTwo
          (programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation density)
          first second jet +
        programPT06SecondOrderLocalVerticalPartialTwo
          (programPT06FiniteRankBilinearValueDensityEvaluation
            density.boundaryCurrent) first second jet from
      programPT06MultifieldSymmetricValueQuadraticVerticalPartial_add density jet
        (programPT06SecondOrderSecondMultiIndex first second)]
  rw [programPT06MultifieldSymmetricValueQuadraticObstructionVerticalPartialTwo]
  simp

private theorem programPT06MultifieldSymmetricValueQuadraticEulerFirstTerm
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (direction : Fin 3) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density)
        direction =
      programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06FiniteRankBilinearValueDensityEvaluation
          density.boundaryCurrent) direction := by
  rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
    programPT06MultifieldSymmetricValueQuadraticVerticalPartialOne]
  rfl

private theorem programPT06MultifieldSymmetricValueQuadraticEulerSecondTerm
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (first second : Fin 3) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density)
        first second =
      programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06FiniteRankBilinearValueDensityEvaluation
          density.boundaryCurrent) first second := by
  rw [programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06MultifieldSymmetricValueQuadraticVerticalPartialTwo]
  rfl

/-- Exact Gate880 Euler formula for the arbitrary symmetric value-quadratic
multifield family. -/
theorem programPT06SecondOrderLocalEuler_multifieldSymmetricValueQuadratic_formula
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density) jet =
      density.valueLinear +
        density.valueQuadratic (jet fourthOrderZeroMultiIndex) := by
  rw [programPT06SecondOrderLocalEuler_formula,
    programPT06MultifieldSymmetricValueQuadraticVerticalPartialZero]
  simp_rw [programPT06MultifieldSymmetricValueQuadraticEulerFirstTerm,
    programPT06MultifieldSymmetricValueQuadraticEulerSecondTerm]
  rw [secondOrderValueProjection_truncate_fourth]
  have hBoundary :=
    programPT06SecondOrderLocalEuler_finiteRankBilinearValueDensity_eq_zero
      density.boundaryCurrent jet
  rw [programPT06SecondOrderLocalEuler_formula] at hBoundary
  calc
    (density.valueLinear +
          density.valueQuadratic (jet fourthOrderZeroMultiIndex) +
          programPT06SecondOrderLocalVerticalPartialZero
            (programPT06FiniteRankBilinearValueDensityEvaluation
              density.boundaryCurrent)
            (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet)) -
        (∑ direction : Fin 3,
          programPT06SecondOrderLocalEulerFirstTotalTerm
            (programPT06FiniteRankBilinearValueDensityEvaluation
              density.boundaryCurrent) direction
            (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)) +
        ∑ first : Fin 3, ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight first second •
            programPT06SecondOrderLocalEulerSecondTotalTerm
              (programPT06FiniteRankBilinearValueDensityEvaluation
                density.boundaryCurrent) first second jet =
      (density.valueLinear +
          density.valueQuadratic (jet fourthOrderZeroMultiIndex)) +
        (programPT06SecondOrderLocalVerticalPartialZero
              (programPT06FiniteRankBilinearValueDensityEvaluation
                density.boundaryCurrent)
              (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet) -
          (∑ direction : Fin 3,
            programPT06SecondOrderLocalEulerFirstTotalTerm
              (programPT06FiniteRankBilinearValueDensityEvaluation
                density.boundaryCurrent) direction
              (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)) +
          ∑ first : Fin 3, ∑ second : Fin 3,
            programPT06SecondOrderEulerSymmetryWeight first second •
              programPT06SecondOrderLocalEulerSecondTotalTerm
                (programPT06FiniteRankBilinearValueDensityEvaluation
                  density.boundaryCurrent) first second jet) := by
        abel
    _ = density.valueLinear +
          density.valueQuadratic (jet fourthOrderZeroMultiIndex) := by
      rw [hBoundary]
      simp

/-- Testing arbitrary value jets and fiber variations makes Euler vanishing
equivalent to vanishing of both value coefficients. -/
theorem programPT06_multifieldSymmetricValueQuadratic_euler_eq_zero_iff
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank) :
    (forall jet : FourthJet (Fiber := Fiber),
      programPT06SecondOrderLocalEuler
        (programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density)
        jet = 0) <->
      density.valueLinear = 0 ∧ density.valueQuadratic = 0 := by
  constructor
  · intro hEuler
    have hAtZero := hEuler 0
    rw [programPT06SecondOrderLocalEuler_multifieldSymmetricValueQuadratic_formula]
      at hAtZero
    have hLinear : density.valueLinear = 0 := by
      simpa using hAtZero
    have hQuadratic : density.valueQuadratic = 0 := by
      apply ContinuousLinearMap.ext
      intro value
      apply ContinuousLinearMap.ext
      intro variation
      have hAtValue := congrArg
        (fun covector : Fiber →L[Real] Real => covector variation)
        (hEuler
          (programPT06ThroatSpatialJetCoordinateInjection
            fourthOrderZeroMultiIndex value))
      rw [programPT06SecondOrderLocalEuler_multifieldSymmetricValueQuadratic_formula]
        at hAtValue
      simpa [hLinear] using hAtValue
    exact ⟨hLinear, hQuadratic⟩
  · rintro ⟨hLinear, hQuadratic⟩ jet
    rw [programPT06SecondOrderLocalEuler_multifieldSymmetricValueQuadratic_formula]
    simp [hLinear, hQuadratic]

/-- Gate898's current is the explicit horizontal primitive of the quadratic
kernel part. -/
def programPT06MultifieldSymmetricValueQuadraticKernelCurrent
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank) :
    ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank :=
  density.boundaryCurrent

/-- Under the coefficient kernel conditions, the density is a constant plus
the genuine Gate898 horizontal divergence. -/
theorem programPT06MultifieldSymmetricValueQuadratic_eq_constant_add_dH
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank)
    (hLinear : density.valueLinear = 0)
    (hQuadratic : density.valueQuadratic = 0)
    (jet : SecondJet (Fiber := Fiber)) :
    programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density jet =
      density.constant +
        programPT06FiniteRankBilinearValueCurrentDivergence
          (programPT06MultifieldSymmetricValueQuadraticKernelCurrent density) jet := by
  rw [programPT06FiniteRankBilinearValueCurrentDivergence_eq_density]
  simp [programPT06MultifieldSymmetricValueQuadraticDensityEvaluation,
    programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation,
    programPT06MultifieldSymmetricValueQuadraticKernelCurrent,
    secondOrderLinearValueCovector, hLinear, hQuadratic]

/-- Exact coefficient-and-homotopy classification on this symmetric
value-quadratic multifield subclass. -/
theorem programPT06_multifieldSymmetricValueQuadratic_euler_eq_zero_iff_divergence_form
    (density : ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank) :
    (forall jet : FourthJet (Fiber := Fiber),
      programPT06SecondOrderLocalEuler
        (programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density)
        jet = 0) <->
      density.valueLinear = 0 ∧ density.valueQuadratic = 0 ∧
        forall jet : SecondJet (Fiber := Fiber),
          programPT06MultifieldSymmetricValueQuadraticDensityEvaluation density jet =
            density.constant +
              programPT06FiniteRankBilinearValueCurrentDivergence
                (programPT06MultifieldSymmetricValueQuadraticKernelCurrent density)
                jet := by
  constructor
  · intro hEuler
    rcases
        (programPT06_multifieldSymmetricValueQuadratic_euler_eq_zero_iff density).mp
          hEuler with
      ⟨hLinear, hQuadratic⟩
    exact ⟨hLinear, hQuadratic,
      programPT06MultifieldSymmetricValueQuadratic_eq_constant_add_dH
        density hLinear hQuadratic⟩
  · rintro ⟨hLinear, hQuadratic, _hDivergence⟩
    exact
      (programPT06_multifieldSymmetricValueQuadratic_euler_eq_zero_iff density).mpr
        ⟨hLinear, hQuadratic⟩

/-- Every Gate898 finite-rank current embeds into the symmetric kernel
family. -/
def programPT06MultifieldSymmetricValueQuadraticOfFiniteRank
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank) :
    ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank where
  constant := 0
  valueLinear := 0
  valueQuadratic := 0
  valueQuadratic_symmetric := by simp
  boundaryCurrent := current

@[simp] theorem
    programPT06MultifieldSymmetricValueQuadraticOfFiniteRank_evaluation
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (jet : SecondJet (Fiber := Fiber)) :
    programPT06MultifieldSymmetricValueQuadraticDensityEvaluation
        (programPT06MultifieldSymmetricValueQuadraticOfFiniteRank current) jet =
      programPT06FiniteRankBilinearValueDensityEvaluation current jet := by
  simp [programPT06MultifieldSymmetricValueQuadraticDensityEvaluation,
    programPT06MultifieldSymmetricValueQuadraticObstructionEvaluation,
    programPT06MultifieldSymmetricValueQuadraticOfFiniteRank,
    secondOrderLinearValueCovector]

/-- Gate908 embeds by viewing twice its normalized rank-one form as the
bilinear coefficient of the one-half normalized quadratic term. -/
def programPT06MultifieldSymmetricValueQuadraticOfGate908
    (density : ProgramPT06MultifieldFirstOrderQuadraticDensity4D Fiber Rank) :
    ProgramPT06MultifieldSymmetricValueQuadraticDensity4D Fiber Rank where
  constant := density.constant
  valueLinear := density.valueLinear
  valueQuadratic :=
    2 • programPT06MultifieldFirstOrderQuadraticValueBilinear density
  valueQuadratic_symmetric := by
    intro first second
    simp only [smul_apply]
    rw [programPT06MultifieldFirstOrderQuadraticValueBilinear_symmetric]
  boundaryCurrent := density.boundaryCurrent

end
end P0EFTJanusProgramPT06MultifieldSymmetricValueQuadraticKernel4D
end JanusFormal


\n