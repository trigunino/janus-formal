import Mathlib.LinearAlgebra.Dual.Lemmas
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D

/-!
# Exact affine second-order throat variational complex

For autonomous affine functions on the genuine spatial second-jet carrier,
the local Euler operator is exactly the value-slot coefficient.  Every linear
coefficient with vanishing value slot factors through the three genuine total
derivatives.  Consequently its Euler kernel is exactly constants plus affine
horizontal divergences.

This is a complete converse on the explicitly bounded affine second-order
class.  It does not classify the nonlinear degree-four T02 polynomial.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AffineSecondOrderExactness4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
  [FiniteDimensional Real Fiber]

private abbrev FirstJet := ThroatSpatialMultiindexJet1 Fiber
private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber
private abbrev CombinedFirstJet := Fin 3 → FirstJet (Fiber := Fiber)

/-- Autonomous affine functions on genuine spatial second jets. -/
abbrev ProgramPT06AffineSecondOrderLocalDensity4D :=
  Real × (SecondJet (Fiber := Fiber) →L[Real] Real)

/-- Linear parts of affine order-one horizontal currents. -/
abbrev ProgramPT06LinearFirstOrderHorizontalCurrent4D :=
  Fin 3 → (FirstJet (Fiber := Fiber) →L[Real] Real)

/-- Evaluation of an affine second-order local density. -/
def programPT06AffineSecondOrderLocalDensityEvaluation
    (density : ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber)) :
    SecondJet (Fiber := Fiber) → Real :=
  (fun _ : SecondJet (Fiber := Fiber) => density.1) +
    (density.2 : SecondJet (Fiber := Fiber) → Real)

/-- The three first total derivatives, retained as one linear map. -/
def programPT06CombinedFirstTotalDerivative :
    SecondJet (Fiber := Fiber) →ₗ[Real] CombinedFirstJet (Fiber := Fiber) where
  toFun jet direction := throatSpatialTotalDerivative direction jet
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- An affine current with the supplied linear part and zero irrelevant
constant part. -/
def programPT06LinearCurrentToAffineCurrent
    (current :
      ProgramPT06LinearFirstOrderHorizontalCurrent4D (Fiber := Fiber)) :
    ProgramPT06AffineHorizontalCurrent4D Fiber where
  constant := 0
  linear := current

/-- Linear coefficient of the actual horizontal divergence. -/
def programPT06AffineSecondOrderLocalDH :
    ProgramPT06LinearFirstOrderHorizontalCurrent4D (Fiber := Fiber) →ₗ[Real]
      (SecondJet (Fiber := Fiber) →L[Real] Real) where
  toFun current :=
    (∑ direction : Fin 3,
      (current direction).toLinearMap.comp
        (throatSpatialTotalDerivativeLinear direction)).toContinuousLinearMap
  map_add' first second := by
    apply ContinuousLinearMap.ext
    intro jet
    simp
    rw [Finset.sum_add_distrib]
  map_smul' scalar current := by
    apply ContinuousLinearMap.ext
    intro jet
    simp
    rw [Finset.mul_sum]

/-- Add a free constant to a horizontal divergence. -/
def programPT06AffineSecondOrderAugmentedDH :
    (Real ×
      ProgramPT06LinearFirstOrderHorizontalCurrent4D (Fiber := Fiber)) →ₗ[Real]
      ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber) where
  toFun input :=
    (input.1, programPT06AffineSecondOrderLocalDH (Fiber := Fiber) input.2)
  map_add' first second := by
    apply Prod.ext
    · rfl
    · exact map_add (programPT06AffineSecondOrderLocalDH (Fiber := Fiber))
        first.2 second.2
  map_smul' scalar input := by
    apply Prod.ext
    · rfl
    · exact map_smul (programPT06AffineSecondOrderLocalDH (Fiber := Fiber))
        scalar input.2

/-- On affine second-order densities, the Euler operator is the value-slot
coefficient. -/
def programPT06AffineSecondOrderLocalEuler :
    ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber) →ₗ[Real]
      (Fiber →L[Real] Real) where
  toFun density :=
    density.2.comp
      (programPT06ThroatSpatialJetCoordinateInjection
        programPT06SecondOrderZeroMultiIndex)
  map_add' first second := by
    ext variation
    rfl
  map_smul' scalar density := by
    ext variation
    rfl

theorem programPT06CombinedFirstTotalDerivative_eq_zero_positive
    (jet : SecondJet (Fiber := Fiber))
    (hJet : programPT06CombinedFirstTotalDerivative (Fiber := Fiber) jet = 0)
    (index : ThroatSpatialTruncatedIndex 2)
    (hIndex : index ≠ programPT06SecondOrderZeroMultiIndex) :
    jet index = 0 := by
  have hUnderlying : index.1 ≠ 0 := by
    intro hZero
    apply hIndex
    apply Subtype.ext
    exact hZero
  obtain ⟨direction, hDirection⟩ :=
    Finsupp.support_nonempty_iff.mpr hUnderlying
  have hCoefficient : index.1 direction ≠ 0 := by
    simpa using hDirection
  let predecessorRaw : ThroatSpatialMultiIndex :=
    index.1 - Finsupp.single direction 1
  have hReconstruct :
      predecessorRaw + throatSpatialCoordinateMultiIndex direction = index.1 := by
    exact Finsupp.sub_add_single_one_cancel hCoefficient
  have hPredecessorOrder :
      throatSpatialMultiIndexOrder predecessorRaw ≤ 1 := by
    have hOrder := congrArg throatSpatialMultiIndexOrder hReconstruct
    rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex] at hOrder
    omega
  let predecessor : ThroatSpatialTruncatedIndex 1 :=
    ⟨predecessorRaw, hPredecessorOrder⟩
  have hDirectionZero := congrFun hJet direction
  change throatSpatialTotalDerivative direction jet = 0 at hDirectionZero
  have hCoefficientZero := congrFun hDirectionZero predecessor
  change
    jet ⟨predecessor.1 + throatSpatialCoordinateMultiIndex direction, by
      rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
      omega⟩ = 0 at hCoefficientZero
  rw [show
    (⟨predecessor.1 + throatSpatialCoordinateMultiIndex direction, by
      rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
      omega⟩ : ThroatSpatialTruncatedIndex 2) = index by
        apply Subtype.ext
        exact hReconstruct] at hCoefficientZero
  exact hCoefficientZero

private theorem programPT06CombinedFirstTotalDerivative_ker_le
    (linear : SecondJet (Fiber := Fiber) →L[Real] Real)
    (hValue :
      linear.comp
        (programPT06ThroatSpatialJetCoordinateInjection
          programPT06SecondOrderZeroMultiIndex) = 0) :
    LinearMap.ker
        (programPT06CombinedFirstTotalDerivative (Fiber := Fiber)) ≤
      LinearMap.ker linear.toLinearMap := by
  intro jet hJet
  rw [LinearMap.mem_ker] at hJet ⊢
  have hPositive :=
    programPT06CombinedFirstTotalDerivative_eq_zero_positive jet hJet
  have hDecomposition :
      jet =
        programPT06ThroatSpatialJetCoordinateInjection
          programPT06SecondOrderZeroMultiIndex
          (jet programPT06SecondOrderZeroMultiIndex) := by
    funext index
    by_cases hIndex : index = programPT06SecondOrderZeroMultiIndex
    · subst index
      simp
    · rw [hPositive index hIndex]
      exact
        (programPT06ThroatSpatialJetCoordinateInjection_of_ne
          programPT06SecondOrderZeroMultiIndex index hIndex
          (jet programPT06SecondOrderZeroMultiIndex)).symm
  rw [hDecomposition]
  have hApply := DFunLike.congr_fun hValue
    (jet programPT06SecondOrderZeroMultiIndex)
  simpa using hApply

/-- Converse to Gate883 soundness on the full affine second-order class:
every affine linear coefficient with zero value slot is an actual horizontal
divergence coefficient. -/
theorem programPT06AffineSecondOrder_exists_current_of_value_eq_zero
    (linear : SecondJet (Fiber := Fiber) →L[Real] Real)
    (hValue :
      linear.comp
        (programPT06ThroatSpatialJetCoordinateInjection
          programPT06SecondOrderZeroMultiIndex) = 0) :
    ∃ current :
        ProgramPT06LinearFirstOrderHorizontalCurrent4D (Fiber := Fiber),
      programPT06AffineSecondOrderLocalDH (Fiber := Fiber) current = linear := by
  let totalDerivative :=
    programPT06CombinedFirstTotalDerivative (Fiber := Fiber)
  have hKernel :
      LinearMap.ker totalDerivative ≤ LinearMap.ker linear.toLinearMap :=
    programPT06CombinedFirstTotalDerivative_ker_le linear hValue
  have hAnnihilator :
      linear.toLinearMap ∈
        (LinearMap.ker totalDerivative).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro jet hJet
    exact hKernel hJet
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker totalDerivative] at hAnnihilator
  obtain ⟨factor, hFactor⟩ := hAnnihilator
  let current :
      ProgramPT06LinearFirstOrderHorizontalCurrent4D (Fiber := Fiber) :=
    fun direction =>
      (factor.comp
        (LinearMap.single Real
          (fun _ : Fin 3 => FirstJet (Fiber := Fiber)) direction)).toContinuousLinearMap
  refine ⟨current, ?_⟩
  apply ContinuousLinearMap.ext
  intro jet
  have hFactorJet := LinearMap.congr_fun hFactor jet
  change factor (totalDerivative jet) = linear jet at hFactorJet
  change
    (∑ direction : Fin 3,
      factor
        (Pi.single direction
          (throatSpatialTotalDerivative direction jet))) = linear jet
  rw [← map_sum]
  have hSum :
      (∑ direction : Fin 3,
        Pi.single direction
          (throatSpatialTotalDerivative direction jet)) =
        totalDerivative jet := by
    funext direction
    simp [totalDerivative, programPT06CombinedFirstTotalDerivative]
  rw [hSum]
  exact hFactorJet

@[simp] theorem programPT06AffineSecondOrderLocalDH_comp_value_eq_zero
    (current :
      ProgramPT06LinearFirstOrderHorizontalCurrent4D (Fiber := Fiber)) :
    (programPT06AffineSecondOrderLocalDH (Fiber := Fiber) current).comp
        (programPT06ThroatSpatialJetCoordinateInjection
          programPT06SecondOrderZeroMultiIndex) = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06AffineSecondOrderLocalDH,
    throatSpatialTotalDerivativeLinear]

/-- Exact bounded classification:
`ker Euler = constants + range dH` for all affine second-order densities. -/
theorem programPT06_affineSecondOrderLocalEuler_ker_eq_augmentedDH_range :
    LinearMap.ker
        (programPT06AffineSecondOrderLocalEuler (Fiber := Fiber)) =
      LinearMap.range
        (programPT06AffineSecondOrderAugmentedDH (Fiber := Fiber)) := by
  ext density
  constructor
  · intro hDensity
    change
      density.2.comp
          (programPT06ThroatSpatialJetCoordinateInjection
            programPT06SecondOrderZeroMultiIndex) = 0 at hDensity
    obtain ⟨current, hCurrent⟩ :=
      programPT06AffineSecondOrder_exists_current_of_value_eq_zero
        density.2 hDensity
    refine ⟨(density.1, current), ?_⟩
    apply Prod.ext
    · rfl
    · exact hCurrent
  · rintro ⟨input, rfl⟩
    exact programPT06AffineSecondOrderLocalDH_comp_value_eq_zero input.2

/-- The augmented differential evaluates as a constant plus the genuine
Gate883 horizontal divergence. -/
theorem programPT06AffineSecondOrderAugmentedDH_evaluation
    (input : Real ×
      ProgramPT06LinearFirstOrderHorizontalCurrent4D (Fiber := Fiber))
    (jet : SecondJet (Fiber := Fiber)) :
    programPT06AffineSecondOrderLocalDensityEvaluation
        (programPT06AffineSecondOrderAugmentedDH (Fiber := Fiber) input) jet =
      input.1 +
        programPT06AffineHorizontalCurrentDivergence
          (programPT06LinearCurrentToAffineCurrent input.2) jet := by
  simp [programPT06AffineSecondOrderLocalDensityEvaluation,
    programPT06AffineSecondOrderAugmentedDH,
    programPT06AffineSecondOrderLocalDH,
    programPT06LinearCurrentToAffineCurrent]
  apply Finset.sum_congr rfl
  intro direction _
  rfl

theorem programPT06AffineSecondOrderLocalDensityEvaluation_hasFDerivAt
    (density : ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber))
    (jet : SecondJet (Fiber := Fiber)) :
    HasFDerivAt
      (programPT06AffineSecondOrderLocalDensityEvaluation density)
      density.2 jet := by
  have hConstant :
      HasFDerivAt
        (fun _ : SecondJet (Fiber := Fiber) => density.1) 0 jet :=
    hasFDerivAt_const (𝕜 := Real) density.1 jet
  simpa [programPT06AffineSecondOrderLocalDensityEvaluation] using
    hConstant.add density.2.hasFDerivAt

@[simp] theorem programPT06AffineSecondOrderVerticalPartial
    (density : ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber))
    (jet : SecondJet (Fiber := Fiber))
    (index : ThroatSpatialTruncatedIndex 2) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AffineSecondOrderLocalDensityEvaluation density) jet index =
      density.2.comp
        (programPT06ThroatSpatialJetCoordinateInjection index) := by
  exact
    programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
      (programPT06AffineSecondOrderLocalDensityEvaluation density) jet index
      density.2
      (programPT06AffineSecondOrderLocalDensityEvaluation_hasFDerivAt
        density jet)

@[simp] theorem programPT06AffineSecondOrderVerticalPartialZero
    (density : ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber)) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06AffineSecondOrderLocalDensityEvaluation density) =
      fun _ => density.2.comp
        (programPT06ThroatSpatialJetCoordinateInjection
          programPT06SecondOrderZeroMultiIndex) := by
  funext jet
  exact programPT06AffineSecondOrderVerticalPartial density jet
    programPT06SecondOrderZeroMultiIndex

@[simp] theorem programPT06AffineSecondOrderVerticalPartialOne
    (density : ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber))
    (direction : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06AffineSecondOrderLocalDensityEvaluation density) direction =
      fun _ => density.2.comp
        (programPT06ThroatSpatialJetCoordinateInjection
          (programPT06SecondOrderFirstMultiIndex direction)) := by
  funext jet
  exact programPT06AffineSecondOrderVerticalPartial density jet
    (programPT06SecondOrderFirstMultiIndex direction)

@[simp] theorem programPT06AffineSecondOrderVerticalPartialTwo
    (density : ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber))
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06AffineSecondOrderLocalDensityEvaluation density)
        first second =
      fun _ => density.2.comp
        (programPT06ThroatSpatialJetCoordinateInjection
          (programPT06SecondOrderSecondMultiIndex first second)) := by
  funext jet
  exact programPT06AffineSecondOrderVerticalPartial density jet
    (programPT06SecondOrderSecondMultiIndex first second)

/-- Gate880's genuine jet Euler agrees with the algebraic affine Euler. -/
theorem programPT06SecondOrderLocalEuler_affine
    (density : ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber))
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06AffineSecondOrderLocalDensityEvaluation density) jet =
      programPT06AffineSecondOrderLocalEuler (Fiber := Fiber) density := by
  simp [programPT06SecondOrderLocalEuler,
    programPT06SecondOrderLocalEulerFirstTotalTerm,
    programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06AffineSecondOrderLocalEuler]

/-- Function-level form of exactness for the genuine Gate880 Euler. -/
theorem programPT06SecondOrderLocalEuler_affine_eq_zero_iff
    (density : ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber)) :
    (∀ jet : FourthJet (Fiber := Fiber),
      programPT06SecondOrderLocalEuler
        (programPT06AffineSecondOrderLocalDensityEvaluation density) jet = 0) ↔
      density ∈ LinearMap.range
        (programPT06AffineSecondOrderAugmentedDH (Fiber := Fiber)) := by
  have hKernel := SetLike.ext_iff.mp
    (programPT06_affineSecondOrderLocalEuler_ker_eq_augmentedDH_range
      (Fiber := Fiber)) density
  simpa [LinearMap.mem_ker, programPT06SecondOrderLocalEuler_affine] using
    hKernel

end
end P0EFTJanusProgramPT06AffineSecondOrderExactness4D
end JanusFormal
