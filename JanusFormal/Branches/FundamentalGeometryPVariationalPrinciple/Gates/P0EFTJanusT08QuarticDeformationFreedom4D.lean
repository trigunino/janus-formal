import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08InvariantDeformationFreedom4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08ValuePotentialEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08StableMassDeformation4D

/-!
# T08: a nonlinear coupling invisible to the fixed-background Hessian

The centered potential `coupling * (LLMeasure - reference)^4` is an actual
member of T02's invariant degree-at-most-four carrier. It preserves the
installed Abelian scalar-ghost gauge shifts and is nonnegative for nonnegative
coupling. At any jet with LL measure equal to the chosen reference, its value,
first derivative and Hessian vanish, while the coupling remains identifiable
away from that background. The reference may be nonzero.

Only the Hessian at one marked scalar reference is fixed; no global Hessian
family or preservation of the separate T12 data is asserted.

This establishes freedom under these stated tests, not full nonlinear BV or
diffeomorphism invariance and not a physical Janus background solution.
-/

namespace JanusFormal
namespace P0EFTJanusT08QuarticDeformationFreedom4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuadraticFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeTwoFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantCubicFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeThreeFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuarticFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06FullPhysicalScalarGhostBRSTJetComplex4D
open P0EFTJanusT08InvariantDeformationFreedom4D
open P0EFTJanusT08ValuePotentialEuler4D
open P0EFTJanusT08StableMassDeformation4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

local instance : NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D.actualLLNormedAddCommGroup
local instance : NormedSpace Real ActualLLSecondOrderJetFiber :=
  P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D.actualLLNormedSpace
local instance : FiniteDimensional Real ActualPhysicalSecondOrderJetProductFiber :=
  actualPhysicalFiniteDimensional
attribute [local instance]
  actualPhysicalValueProductNormedAddCommGroup actualPhysicalValueProductNormedSpace
  actualPhysicalValueProductFinsuppSecondJetFiniteDimensional

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber
private abbrev ValueFiber := ActualPhysicalValueProductFiber

private def measureBilinear : Fiber →L[Real] Fiber →L[Real] Real :=
  t08LLMeasureValue.smulRight t08LLMeasureValue

private def measureTrilinear : Fiber →L[Real] Fiber →L[Real] Fiber →L[Real] Real :=
  t08LLMeasureValue.smulRight measureBilinear

private def measureQuadrilinear :
    Fiber →L[Real] Fiber →L[Real] Fiber →L[Real] Fiber →L[Real] Real :=
  t08LLMeasureValue.smulRight measureTrilinear

variable (period : Real) (hPeriod : period ≠ 0)

local instance : ChartedSpace ThroatCoverModel
    (MappingTorus (fixedEquatorData period hPeriod)) :=
  fixedThroatQuotientChartedSpace period hPeriod

private theorem measureBilinear_invariant :
    IsActualPhysicalSecondOrderJetInvariantSymmetricBilinearForm
      period hPeriod measureBilinear := by
  constructor
  · intro first second
    change t08LLMeasureValue first * t08LLMeasureValue second =
      t08LLMeasureValue second * t08LLMeasureValue first
    ring
  · intro first second base hBase firstJet secondJet
    simp only [measureBilinear, ContinuousLinearMap.smulRight_apply,
      _root_.smul_apply, smul_eq_mul]
    rw [t08LLMeasureValue_transitionInvariant period hPeriod first second base hBase,
      t08LLMeasureValue_transitionInvariant period hPeriod first second base hBase]

private theorem measureTrilinear_invariant :
    IsActualPhysicalSecondOrderJetInvariantSymmetricTrilinearForm
      period hPeriod measureTrilinear := by
  refine ⟨?_, ?_, ?_⟩
  · intro first second third
    change t08LLMeasureValue first * (t08LLMeasureValue second * t08LLMeasureValue third) =
      t08LLMeasureValue second * (t08LLMeasureValue first * t08LLMeasureValue third)
    ring
  · intro first second third
    change t08LLMeasureValue first * (t08LLMeasureValue second * t08LLMeasureValue third) =
      t08LLMeasureValue first * (t08LLMeasureValue third * t08LLMeasureValue second)
    ring
  · intro first second base hBase firstJet secondJet thirdJet
    simp only [measureTrilinear, measureBilinear, ContinuousLinearMap.smulRight_apply,
      _root_.smul_apply, smul_eq_mul]
    rw [t08LLMeasureValue_transitionInvariant period hPeriod first second base hBase,
      t08LLMeasureValue_transitionInvariant period hPeriod first second base hBase,
      t08LLMeasureValue_transitionInvariant period hPeriod first second base hBase]

private theorem measureQuadrilinear_invariant :
    IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod measureQuadrilinear := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro first second third fourth
    change t08LLMeasureValue first * (t08LLMeasureValue second *
      (t08LLMeasureValue third * t08LLMeasureValue fourth)) =
      t08LLMeasureValue second * (t08LLMeasureValue first *
        (t08LLMeasureValue third * t08LLMeasureValue fourth))
    ring
  · intro first second third fourth
    change t08LLMeasureValue first * (t08LLMeasureValue second *
      (t08LLMeasureValue third * t08LLMeasureValue fourth)) =
      t08LLMeasureValue first * (t08LLMeasureValue third *
        (t08LLMeasureValue second * t08LLMeasureValue fourth))
    ring
  · intro first second third fourth
    change t08LLMeasureValue first * (t08LLMeasureValue second *
      (t08LLMeasureValue third * t08LLMeasureValue fourth)) =
      t08LLMeasureValue first * (t08LLMeasureValue second *
        (t08LLMeasureValue fourth * t08LLMeasureValue third))
    ring
  · intro first second base hBase firstJet secondJet thirdJet fourthJet
    simp only [measureQuadrilinear, measureTrilinear, measureBilinear,
      ContinuousLinearMap.smulRight_apply, _root_.smul_apply, smul_eq_mul]
    rw [t08LLMeasureValue_transitionInvariant period hPeriod first second base hBase,
      t08LLMeasureValue_transitionInvariant period hPeriod first second base hBase,
      t08LLMeasureValue_transitionInvariant period hPeriod first second base hBase,
      t08LLMeasureValue_transitionInvariant period hPeriod first second base hBase]

/-- Explicit binomial expansion inside the already classified T02 carrier. -/
def t08CenteredQuarticInvariantDeformation (reference coupling : Real) :
    ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional period hPeriod where
  lower :=
    { lower :=
        { constant := coupling * reference ^ 4
          linear := (-4 * coupling * reference ^ 3) •
            ⟨t08LLMeasureValue, t08LLMeasureValue_transitionInvariant period hPeriod⟩
          quadratic := (6 * coupling * reference ^ 2) •
            ⟨measureBilinear, measureBilinear_invariant period hPeriod⟩ }
      cubic := (-4 * coupling * reference) •
        ⟨measureTrilinear, measureTrilinear_invariant period hPeriod⟩ }
  quartic := coupling •
    ⟨measureQuadrilinear, measureQuadrilinear_invariant period hPeriod⟩

@[simp] theorem t08CenteredQuarticInvariantDeformation_evaluation
    (reference coupling : Real) (jet : Fiber) :
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
      (t08CenteredQuarticInvariantDeformation period hPeriod reference coupling) jet =
        coupling * (t08LLMeasureValue jet - reference) ^ 4 := by
  simp [t08CenteredQuarticInvariantDeformation,
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
    actualPhysicalSecondOrderJetInvariantQuadraticEvaluation,
    actualPhysicalSecondOrderJetInvariantCubicEvaluation,
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation,
    measureQuadrilinear, measureTrilinear, measureBilinear]
  ring

theorem t08CenteredQuarticInvariantDeformation_injective (reference : Real) :
    Function.Injective
      (t08CenteredQuarticInvariantDeformation period hPeriod reference) := by
  intro first second hEqual
  have h := congrArg (fun functional =>
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
      functional ((reference + 1) • t08LLMeasureUnitJet)) hEqual
  simpa only [t08CenteredQuarticInvariantDeformation_evaluation, map_smul,
    t08LLMeasureValue_unit, smul_eq_mul, mul_one, add_sub_cancel_left,
    one_pow, mul_one] using h

/-- Same centered quartic in T06's physical spatial-jet carrier. -/
def t08CenteredQuarticSpatialDeformation (reference coupling : Real)
    (jet : ThroatSpatialMultiindexJet2 ValueFiber) : Real :=
  coupling * (t08LLMeasureSpatialDeformation 1 jet - reference) ^ 4

theorem t08CenteredQuarticSpatialDeformation_eq_T02
    (reference coupling : Real) (jet : ThroatSpatialMultiindexJet2 ValueFiber) :
    t08CenteredQuarticSpatialDeformation reference coupling jet =
      actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        (t08CenteredQuarticInvariantDeformation period hPeriod reference coupling)
        (programPT06ActualPhysicalValueProductFinsuppSecondJetLinearEquiv jet) := by
  rw [t08CenteredQuarticInvariantDeformation_evaluation]
  simp only [t08CenteredQuarticSpatialDeformation,
    t08LLMeasureSpatialDeformation,
    ContinuousLinearMap.comp_apply, one_smul]
  rfl

theorem t08CenteredQuarticSpatialDeformation_eq_valueOnly (reference coupling : Real) :
    t08CenteredQuarticSpatialDeformation reference coupling =
      valueOnly (centeredPower t08LLMeasureValueCoordinate coupling reference 4) := by
  funext jet
  simp [t08CenteredQuarticSpatialDeformation, valueOnly, centeredPower]

/-- The actual T06 Euler operator detects the quartic away from its marked
reference, even though its Hessian vanishes at that reference. -/
theorem t08CenteredQuarticSpatialDeformation_euler
    (reference coupling : Real) (jet : ThroatSpatialMultiindexJet4 ValueFiber)
    (variation : ValueFiber) :
    programPT06SecondOrderLocalEuler (t08CenteredQuarticSpatialDeformation reference coupling)
      jet variation =
      4 * coupling * (t08LLMeasureValueCoordinate (jet ⟨0, by simp⟩) - reference) ^ 3 *
        t08LLMeasureValueCoordinate variation := by
  rw [t08CenteredQuarticSpatialDeformation_eq_valueOnly, centeredPower_euler]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub]
  ring

theorem t08CenteredQuarticSpatialDeformation_euler_injective (reference : Real) :
    Function.Injective (fun coupling =>
      programPT06SecondOrderLocalEuler
        (t08CenteredQuarticSpatialDeformation reference coupling)) := by
  intro first second hEqual
  let witness : ThroatSpatialMultiindexJet4 ValueFiber :=
    programPT06ThroatSpatialJetCoordinateInjection ⟨0, by simp⟩
      ((reference + 1) • t08LLMeasureUnitVariation)
  have hValue : t08LLMeasureValueCoordinate (witness ⟨0, by simp⟩) = reference + 1 := by
    change t08LLMeasureValueCoordinate
      (programPT06ThroatSpatialJetCoordinateInjection (⟨0, by simp⟩ : ThroatSpatialTruncatedIndex 4)
        ((reference + 1) • t08LLMeasureUnitVariation) ⟨0, by simp⟩) = reference + 1
    rw [programPT06ThroatSpatialJetCoordinateInjection_same,
      map_smul, t08LLMeasureValueCoordinate_unit]
    simp
  have h := congrArg (fun expression => expression witness t08LLMeasureUnitVariation) hEqual
  simp only [t08CenteredQuarticSpatialDeformation_euler,
    t08LLMeasureValueCoordinate_unit, hValue, mul_one, add_sub_cancel_left, one_pow] at h
  linarith

theorem t08CenteredQuarticSpatialDeformation_nonneg
    (reference coupling : Real) (hCoupling : 0 ≤ coupling)
    (jet : ThroatSpatialMultiindexJet2 ValueFiber) :
    0 ≤ t08CenteredQuarticSpatialDeformation reference coupling jet :=
  mul_nonneg hCoupling (by positivity)

/-- Exact installed Abelian BRST invariance, for every finite amplitude. -/
theorem t08CenteredQuarticSpatialDeformation_abelianBRST_shift
    (reference coupling amplitude : Real)
    (state : ProgramPT06FullPhysicalScalarGhostJetState4D 2) :
    t08CenteredQuarticSpatialDeformation reference coupling
        (state.1 + amplitude •
          (programPT06FullPhysicalScalarGhostJetBRST 2 state).1) =
      t08CenteredQuarticSpatialDeformation reference coupling state.1 := by
  unfold t08CenteredQuarticSpatialDeformation
  rw [t08LLMeasureSpatialDeformation_abelianBRST_shift]

/-- Derivative formula valid on any normed real carrier with a marked linear
coordinate. This includes nonzero choices of the reference value. -/
theorem centeredQuartic_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (coordinate : E →L[Real] Real) (reference coupling : Real) (point : E) :
    HasFDerivAt (fun jet => coupling * (coordinate jet - reference) ^ 4)
      ((coupling * (4 * (coordinate point - reference) ^ 3)) • coordinate) point := by
  simpa only [Nat.reduceSub, Nat.cast_ofNat, nsmul_eq_mul, smul_smul] using
    (((coordinate.hasFDerivAt (x := point)).sub_const reference).pow 4).const_mul coupling

/-- Both Frechet derivatives vanish at every jet matching the marked
reference, although the nonlinear potential is not fixed by these data. -/
theorem centeredQuartic_twoJet_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (coordinate : E →L[Real] Real) (reference coupling : Real) (point : E)
    (hReference : coordinate point = reference) :
    coupling * (coordinate point - reference) ^ 4 = 0 ∧
    fderiv Real (fun jet => coupling * (coordinate jet - reference) ^ 4) point = 0 ∧
    fderiv Real
        (fderiv Real (fun jet => coupling * (coordinate jet - reference) ^ 4)) point = 0 := by
  have hDerivative :
      fderiv Real (fun jet => coupling * (coordinate jet - reference) ^ 4) =
        fun jet => (coupling * (4 * (coordinate jet - reference) ^ 3)) • coordinate := by
    funext jet
    exact (centeredQuartic_hasFDerivAt coordinate reference coupling jet).fderiv
  refine ⟨by simp [hReference], ?_, ?_⟩
  · rw [hDerivative]
    simp [hReference]
  · rw [hDerivative]
    have hScalar : HasFDerivAt
        (fun jet => coupling * (4 * (coordinate jet - reference) ^ 3))
        (0 : E →L[Real] Real) point := by
      simpa [hReference] using
        ((((coordinate.hasFDerivAt (x := point)).sub_const reference).pow 3).const_mul 4).const_mul coupling
    simpa using (hScalar.smul_const coordinate).fderiv

/-- Concrete T06 specialization: every centered quartic leaves the value,
linearization and Hessian unchanged at the marked measure background. -/
theorem t08CenteredQuarticSpatialDeformation_twoJet_zero
    (reference coupling : Real) (jet : ThroatSpatialMultiindexJet2 ValueFiber)
    (hReference : t08LLMeasureSpatialDeformation 1 jet = reference) :
    t08CenteredQuarticSpatialDeformation reference coupling jet = 0 ∧
    fderiv Real (t08CenteredQuarticSpatialDeformation reference coupling) jet = 0 ∧
    fderiv Real
      (fderiv Real (t08CenteredQuarticSpatialDeformation reference coupling)) jet = 0 :=
  centeredQuartic_twoJet_zero (t08LLMeasureSpatialDeformation 1)
    reference coupling jet hReference

/-- The fixed quadratic term makes the quartic a relative coupling, rather
than an overall rescaling of a pure quartic action. -/
def t08NormalizedQuarticInvariantDeformation (reference coupling : Real) :
    ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional period hPeriod where
  lower :=
    { lower :=
        { constant := reference ^ 2 + coupling * reference ^ 4
          linear := (-2 * reference - 4 * coupling * reference ^ 3) •
            ⟨t08LLMeasureValue, t08LLMeasureValue_transitionInvariant period hPeriod⟩
          quadratic := (1 + 6 * coupling * reference ^ 2) •
            ⟨measureBilinear, measureBilinear_invariant period hPeriod⟩ }
      cubic := (-4 * coupling * reference) •
        ⟨measureTrilinear, measureTrilinear_invariant period hPeriod⟩ }
  quartic := coupling •
    ⟨measureQuadrilinear, measureQuadrilinear_invariant period hPeriod⟩

@[simp] theorem t08NormalizedQuarticInvariantDeformation_evaluation
    (reference coupling : Real) (jet : Fiber) :
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
      (t08NormalizedQuarticInvariantDeformation period hPeriod reference coupling) jet =
        (t08LLMeasureValue jet - reference) ^ 2 +
          coupling * (t08LLMeasureValue jet - reference) ^ 4 := by
  simp [t08NormalizedQuarticInvariantDeformation,
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
    actualPhysicalSecondOrderJetInvariantQuadraticEvaluation,
    actualPhysicalSecondOrderJetInvariantCubicEvaluation,
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation,
    measureQuadrilinear, measureTrilinear, measureBilinear]
  ring

/-- Distinct relative quartic couplings cannot be absorbed into a global
action scale once the quadratic coefficient is fixed. -/
theorem t08NormalizedQuarticInvariantDeformation_scale_rigid
    (reference first second scale : Real)
    (hScale : ∀ jet,
      actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        (t08NormalizedQuarticInvariantDeformation period hPeriod reference first) jet =
      scale * actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        (t08NormalizedQuarticInvariantDeformation period hPeriod reference second) jet) :
    scale = 1 ∧ first = second := by
  have hOne := hScale ((reference + 1) • t08LLMeasureUnitJet)
  have hTwo := hScale ((reference + 2) • t08LLMeasureUnitJet)
  simp only [t08NormalizedQuarticInvariantDeformation_evaluation, map_smul,
    t08LLMeasureValue_unit, smul_eq_mul, mul_one, add_sub_cancel_left] at hOne hTwo
  norm_num at hOne hTwo
  have hScaleOne : scale = 1 := by nlinarith
  refine ⟨hScaleOne, ?_⟩
  rw [hScaleOne] at hOne
  linarith

/-- Normalized nonlinear potential, defined on the genuine spatial jets. -/
def t08NormalizedQuarticSpatialDeformation (reference coupling : Real)
    (jet : ThroatSpatialMultiindexJet2 ValueFiber) : Real :=
  (t08LLMeasureSpatialDeformation 1 jet - reference) ^ 2 +
    t08CenteredQuarticSpatialDeformation reference coupling jet

theorem t08NormalizedQuarticSpatialDeformation_eq_T02
    (reference coupling : Real) (jet : ThroatSpatialMultiindexJet2 ValueFiber) :
    t08NormalizedQuarticSpatialDeformation reference coupling jet =
      actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        (t08NormalizedQuarticInvariantDeformation period hPeriod reference coupling)
        (programPT06ActualPhysicalValueProductFinsuppSecondJetLinearEquiv jet) := by
  rw [t08NormalizedQuarticInvariantDeformation_evaluation]
  simp only [t08NormalizedQuarticSpatialDeformation, t08CenteredQuarticSpatialDeformation,
    t08LLMeasureSpatialDeformation,
    ContinuousLinearMap.comp_apply, one_smul]
  rfl

theorem t08NormalizedQuarticSpatialDeformation_nonneg
    (reference coupling : Real) (hCoupling : 0 ≤ coupling)
    (jet : ThroatSpatialMultiindexJet2 ValueFiber) :
    0 ≤ t08NormalizedQuarticSpatialDeformation reference coupling jet :=
  add_nonneg (sq_nonneg _) (t08CenteredQuarticSpatialDeformation_nonneg
    reference coupling hCoupling jet)

theorem t08NormalizedQuarticSpatialDeformation_abelianBRST_shift
    (reference coupling amplitude : Real)
    (state : ProgramPT06FullPhysicalScalarGhostJetState4D 2) :
    t08NormalizedQuarticSpatialDeformation reference coupling
        (state.1 + amplitude •
          (programPT06FullPhysicalScalarGhostJetBRST 2 state).1) =
      t08NormalizedQuarticSpatialDeformation reference coupling state.1 := by
  unfold t08NormalizedQuarticSpatialDeformation
  rw [t08LLMeasureSpatialDeformation_abelianBRST_shift,
    t08CenteredQuarticSpatialDeformation_abelianBRST_shift]

/-- At the marked reference, the normalized potentials all have zero value
and first variation, and exactly the same quadratic Hessian. -/
theorem normalizedQuartic_twoJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (coordinate : E →L[Real] Real) (reference coupling : Real) (point : E)
    (hReference : coordinate point = reference) :
    let potential := fun jet : E =>
      (coordinate jet - reference) ^ 2 + coupling * (coordinate jet - reference) ^ 4
    potential point = 0 ∧ fderiv Real potential point = 0 ∧
      fderiv Real (fderiv Real potential) point =
        ((2 : Real) • coordinate).smulRight coordinate := by
  dsimp only
  have hDerivative :
      fderiv Real (fun jet => (coordinate jet - reference) ^ 2 +
          coupling * (coordinate jet - reference) ^ 4) =
        fun jet => (2 * (coordinate jet - reference)) • coordinate +
          (coupling * (4 * (coordinate jet - reference) ^ 3)) • coordinate := by
    funext jet
    have hSquare := ((coordinate.hasFDerivAt (x := jet)).sub_const reference).pow 2
    have hQuartic := centeredQuartic_hasFDerivAt coordinate reference coupling jet
    simpa [Pi.add_apply, nsmul_eq_mul] using (hSquare.fun_add hQuartic).fderiv
  refine ⟨by simp [hReference], ?_, ?_⟩
  · rw [hDerivative]
    simp [hReference]
  · rw [hDerivative]
    have hSquare : HasFDerivAt
        (fun jet => 2 * (coordinate jet - reference))
        ((2 : Real) • coordinate) point :=
      ((coordinate.hasFDerivAt (x := point)).sub_const reference).const_mul 2
    have hQuartic : HasFDerivAt
        (fun jet => coupling * (4 * (coordinate jet - reference) ^ 3))
        (0 : E →L[Real] Real) point := by
      simpa [hReference] using
        ((((coordinate.hasFDerivAt (x := point)).sub_const reference).pow 3).const_mul 4).const_mul coupling
    simpa only [Pi.add_apply, ContinuousLinearMap.zero_smulRight, add_zero] using ((hSquare.smul_const coordinate).fun_add
      (hQuartic.smul_const coordinate)).fderiv

theorem t08NormalizedQuarticSpatialDeformation_twoJet
    (reference coupling : Real) (jet : ThroatSpatialMultiindexJet2 ValueFiber)
    (hReference : t08LLMeasureSpatialDeformation 1 jet = reference) :
    t08NormalizedQuarticSpatialDeformation reference coupling jet = 0 ∧
    fderiv Real (t08NormalizedQuarticSpatialDeformation reference coupling) jet = 0 ∧
    fderiv Real
        (fderiv Real (t08NormalizedQuarticSpatialDeformation reference coupling)) jet =
      ((2 : Real) • t08LLMeasureSpatialDeformation 1).smulRight
        (t08LLMeasureSpatialDeformation 1) :=
  normalizedQuartic_twoJet (t08LLMeasureSpatialDeformation 1)
    reference coupling jet hReference

/-- Off the marked reference the Hessian changes: its scalar coefficient is
`2 + 12 * coupling * (coordinate - reference)^2`. -/
theorem normalizedQuartic_hessian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (coordinate : E →L[Real] Real) (reference coupling : Real) (point : E) :
    fderiv Real (fderiv Real (fun jet => (coordinate jet - reference) ^ 2 +
      coupling * (coordinate jet - reference) ^ 4)) point =
      ((2 + 12 * coupling * (coordinate point - reference) ^ 2) • coordinate).smulRight
        coordinate := by
  have hDerivative :
      fderiv Real (fun jet => (coordinate jet - reference) ^ 2 +
          coupling * (coordinate jet - reference) ^ 4) =
        fun jet => (2 * (coordinate jet - reference)) • coordinate +
          (coupling * (4 * (coordinate jet - reference) ^ 3)) • coordinate := by
    funext jet
    have hSquare := ((coordinate.hasFDerivAt (x := jet)).sub_const reference).pow 2
    have hQuartic := centeredQuartic_hasFDerivAt coordinate reference coupling jet
    simpa [Pi.add_apply, nsmul_eq_mul] using (hSquare.fun_add hQuartic).fderiv
  rw [hDerivative]
  have hSquare : HasFDerivAt (fun jet => 2 * (coordinate jet - reference))
      ((2 : Real) • coordinate) point :=
    ((coordinate.hasFDerivAt (x := point)).sub_const reference).const_mul 2
  have hQuartic : HasFDerivAt
      (fun jet => coupling * (4 * (coordinate jet - reference) ^ 3))
      ((coupling * 4 * 3 * (coordinate point - reference) ^ 2) • coordinate) point := by
    simpa [nsmul_eq_mul, smul_smul, mul_assoc] using
      ((((coordinate.hasFDerivAt (x := point)).sub_const reference).pow 3).const_mul 4).const_mul coupling
  have hSecond := ((hSquare.smul_const coordinate).fun_add (hQuartic.smul_const coordinate)).fderiv
  rw [hSecond]
  ext first second
  simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

/-- One off-reference potential value selects the relative coupling. -/
theorem normalizedQuartic_coupling_from_response
    (displacement coupling response : Real) (hDisplacement : displacement ≠ 0)
    (hResponse : response = displacement ^ 2 + coupling * displacement ^ 4) :
    coupling = (response - displacement ^ 2) / displacement ^ 4 := by
  apply (eq_div_iff (pow_ne_zero 4 hDisplacement)).2
  rw [hResponse]
  ring

end
end P0EFTJanusT08QuarticDeformationFreedom4D
end JanusFormal
