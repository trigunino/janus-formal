import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeThreeFunctionalBasis4D

/-!
# Invariant homogeneous quartic functionals

This gate classifies continuous symmetric quadrilinear forms invariant under
the genuine actual-physical second-jet transitions. Injectivity of diagonal
evaluation is proved by three small polarization steps, avoiding a large
sixteen-term expansion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuarticFunctionalBasis4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open Set
open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D

local instance quarticActualLLNormedAddCommGroup :
    NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  actualLLNormedAddCommGroup

local instance quarticActualLLNormedSpace :
    NormedSpace Real ActualLLSecondOrderJetFiber :=
  actualLLNormedSpace

local instance quarticActualPhysicalFiniteDimensional :
    FiniteDimensional Real ActualPhysicalSecondOrderJetProductFiber :=
  actualPhysicalFiniteDimensional

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber

private abbrev LinearForm := Fiber →L[Real] Real

private abbrev BilinearForm := Fiber →L[Real] LinearForm

private abbrev TrilinearForm := Fiber →L[Real] BilinearForm

local instance quarticActualPhysicalNormedAddCommGroup :
    NormedAddCommGroup Fiber :=
  inferInstance

local instance quarticActualPhysicalNormedSpace :
    NormedSpace Real Fiber :=
  inferInstance

local instance quarticLinearNormedAddCommGroup :
    NormedAddCommGroup LinearForm := inferInstance
local instance quarticLinearNormedSpace : NormedSpace Real LinearForm := inferInstance
local instance quarticBilinearNormedAddCommGroup :
    NormedAddCommGroup BilinearForm := inferInstance
local instance quarticBilinearNormedSpace : NormedSpace Real BilinearForm := inferInstance
local instance quarticTrilinearNormedAddCommGroup :
    NormedAddCommGroup TrilinearForm := inferInstance
local instance quarticTrilinearNormedSpace : NormedSpace Real TrilinearForm := inferInstance

private abbrev QuadrilinearForm := Fiber →L[Real] TrilinearForm

local instance quarticQuadrilinearNormedAddCommGroup :
    NormedAddCommGroup QuadrilinearForm := inferInstance
local instance quarticQuadrilinearNormedSpace :
    NormedSpace Real QuadrilinearForm := inferInstance

local instance quarticLinearFiniteDimensional :
    FiniteDimensional Real LinearForm := inferInstance
local instance quarticBilinearFiniteDimensional :
    FiniteDimensional Real BilinearForm := inferInstance
local instance quarticTrilinearFiniteDimensional :
    FiniteDimensional Real TrilinearForm := inferInstance
local instance quarticQuadrilinearFiniteDimensional :
    FiniteDimensional Real QuadrilinearForm := inferInstance

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Chart :=
  ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod

private abbrev Base := MappingTorus (fixedEquatorData period hPeriod)

private def IsQuadrilinearSwap12 (form : QuadrilinearForm) : Prop :=
  ∀ first second third fourth,
    form first second third fourth = form second first third fourth

private def IsQuadrilinearSwap23 (form : QuadrilinearForm) : Prop :=
  ∀ first second third fourth,
    form first second third fourth = form first third second fourth

private def IsQuadrilinearSwap34 (form : QuadrilinearForm) : Prop :=
  ∀ first second third fourth,
    form first second third fourth = form first second fourth third

private def IsQuadrilinearTransitionInvariant (form : QuadrilinearForm) : Prop :=
  ∀ (first second : Chart period hPeriod) (base : Base period hPeriod),
    base ∈
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet first ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet second →
      ∀ firstJet secondJet thirdJet fourthJet,
        form
            ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
              .positiveQuarter).coordChange first second base firstJet)
            ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
              .positiveQuarter).coordChange first second base secondJet)
            ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
              .positiveQuarter).coordChange first second base thirdJet)
            ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
              .positiveQuarter).coordChange first second base fourthJet) =
          form firstJet secondJet thirdJet fourthJet

/-- An admissible quadrilinear form is symmetric under the three adjacent
transpositions and invariant under simultaneous transition of its arguments. -/
def IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
    (form : QuadrilinearForm) : Prop :=
  IsQuadrilinearSwap12 form ∧ IsQuadrilinearSwap23 form ∧
    IsQuadrilinearSwap34 form ∧
      IsQuadrilinearTransitionInvariant period hPeriod form

private theorem quadrilinear_add_swap12
    {firstForm secondForm : QuadrilinearForm}
    (hFirst : IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod firstForm)
    (hSecond : IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod secondForm) :
    IsQuadrilinearSwap12 (firstForm + secondForm) := by
  intro first second third fourth
  simp only [add_apply]
  rw [hFirst.1 first second third fourth, hSecond.1 first second third fourth]

private theorem quadrilinear_add_swap23
    {firstForm secondForm : QuadrilinearForm}
    (hFirst : IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod firstForm)
    (hSecond : IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod secondForm) :
    IsQuadrilinearSwap23 (firstForm + secondForm) := by
  intro first second third fourth
  simp only [add_apply]
  rw [hFirst.2.1 first second third fourth,
    hSecond.2.1 first second third fourth]

private theorem quadrilinear_add_swap34
    {firstForm secondForm : QuadrilinearForm}
    (hFirst : IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod firstForm)
    (hSecond : IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod secondForm) :
    IsQuadrilinearSwap34 (firstForm + secondForm) := by
  intro first second third fourth
  simp only [add_apply]
  rw [hFirst.2.2.1 first second third fourth,
    hSecond.2.2.1 first second third fourth]

private theorem quadrilinear_add_invariant
    {firstForm secondForm : QuadrilinearForm}
    (hFirst : IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod firstForm)
    (hSecond : IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod secondForm) :
    IsQuadrilinearTransitionInvariant period hPeriod
      (firstForm + secondForm) := by
  intro first second base hBase firstJet secondJet thirdJet fourthJet
  simp only [add_apply]
  rw [hFirst.2.2.2 first second base hBase firstJet secondJet thirdJet fourthJet,
    hSecond.2.2.2 first second base hBase firstJet secondJet thirdJet fourthJet]

private theorem quadrilinear_smul_swap12
    (scalar : Real) {form : QuadrilinearForm}
    (hForm : IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod form) :
    IsQuadrilinearSwap12 (scalar • form) := by
  intro first second third fourth
  simp only [smul_apply]
  rw [hForm.1 first second third fourth]

private theorem quadrilinear_smul_swap23
    (scalar : Real) {form : QuadrilinearForm}
    (hForm : IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod form) :
    IsQuadrilinearSwap23 (scalar • form) := by
  intro first second third fourth
  simp only [smul_apply]
  rw [hForm.2.1 first second third fourth]

private theorem quadrilinear_smul_swap34
    (scalar : Real) {form : QuadrilinearForm}
    (hForm : IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod form) :
    IsQuadrilinearSwap34 (scalar • form) := by
  intro first second third fourth
  simp only [smul_apply]
  rw [hForm.2.2.1 first second third fourth]

private theorem quadrilinear_smul_invariant
    (scalar : Real) {form : QuadrilinearForm}
    (hForm : IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
      period hPeriod form) :
    IsQuadrilinearTransitionInvariant period hPeriod (scalar • form) := by
  intro first second base hBase firstJet secondJet thirdJet fourthJet
  simp only [smul_apply]
  rw [hForm.2.2.2 first second base hBase firstJet secondJet thirdJet fourthJet]

/-- The invariant symmetric continuous quadrilinear forms are a real
subspace. -/
def actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms :
    Submodule Real QuadrilinearForm where
  carrier := IsActualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForm
    period hPeriod
  zero_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro first second third fourth
      simp only [zero_apply]
    · intro first second third fourth
      simp only [zero_apply]
    · intro first second third fourth
      simp only [zero_apply]
    · intro first second base hBase firstJet secondJet thirdJet fourthJet
      simp only [zero_apply]
  add_mem' := by
    intro firstForm secondForm hFirst hSecond
    exact ⟨quadrilinear_add_swap12 period hPeriod hFirst hSecond,
      quadrilinear_add_swap23 period hPeriod hFirst hSecond,
      quadrilinear_add_swap34 period hPeriod hFirst hSecond,
      quadrilinear_add_invariant period hPeriod hFirst hSecond⟩
  smul_mem' := by
    intro scalar form hForm
    exact ⟨quadrilinear_smul_swap12 period hPeriod scalar hForm,
      quadrilinear_smul_swap23 period hPeriod scalar hForm,
      quadrilinear_smul_swap34 period hPeriod scalar hForm,
      quadrilinear_smul_invariant period hPeriod scalar hForm⟩

local instance invariantSymmetricQuadrilinearFormsAddCommGroup :
    AddCommGroup
      (actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod) :=
  (actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod).toAddSubgroup.toAddCommGroup

/-- The invariant symmetric quadrilinear class is finite-dimensional. -/
theorem actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms_finiteDimensional :
    FiniteDimensional Real
      (actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period
        hPeriod) :=
  inferInstance

local instance invariantSymmetricQuadrilinearFormsFiniteDimensional :
    FiniteDimensional Real
      (actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period
        hPeriod) :=
  actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms_finiteDimensional
    period hPeriod

/-- Finite coefficient index of invariant homogeneous quartics. -/
abbrev ActualPhysicalSecondOrderJetInvariantQuarticFunctionalIndex :=
  Module.Basis.ofVectorSpaceIndex Real
    (actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)

/-- A finite basis of all invariant symmetric continuous quadrilinear forms. -/
def actualPhysicalSecondOrderJetInvariantQuarticFunctionalBasis :
    Module.Basis
      (ActualPhysicalSecondOrderJetInvariantQuarticFunctionalIndex period hPeriod)
      Real
      (actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod) :=
  Module.Basis.ofVectorSpace Real
    (actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)

/-- Exact finite coordinates of an invariant quadrilinear form. -/
def actualPhysicalSecondOrderJetInvariantQuarticFunctionalCoordinateEquiv :
    actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod ≃ₗ[Real]
      (ActualPhysicalSecondOrderJetInvariantQuarticFunctionalIndex period hPeriod → Real) :=
  (actualPhysicalSecondOrderJetInvariantQuarticFunctionalBasis period hPeriod).equivFun

/-- The homogeneous quartic obtained by diagonal evaluation. -/
def actualPhysicalSecondOrderJetInvariantQuarticEvaluation
    (form : actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)
    (jet : Fiber) : Real :=
  form.1 jet jet jet jet

/-- Every represented quartic is invariant under every genuine transition. -/
theorem actualPhysicalSecondOrderJetInvariantQuarticEvaluation_transitionInvariant
    (form : actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : Fiber) :
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod form
        ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).coordChange first second base jet) =
      actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod form jet :=
  form.property.2.2.2 first second base hBase jet jet jet jet

private theorem quartic_xyxy_eq_xxyy
    (form : actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)
    (first second : Fiber) :
    form.1 first second first second = form.1 first first second second :=
  form.property.2.1 first second first second

private theorem quartic_xyyx_eq_xxyy
    (form : actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)
    (first second : Fiber) :
    form.1 first second second first = form.1 first first second second := by
  exact (form.property.2.2.1 first second second first).trans
    (quartic_xyxy_eq_xxyy period hPeriod form first second)

private theorem quartic_yxxy_eq_xxyy
    (form : actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)
    (first second : Fiber) :
    form.1 second first first second = form.1 first first second second :=
  (form.property.1 first second first second).symm.trans
    (quartic_xyxy_eq_xxyy period hPeriod form first second)

private theorem quartic_yxyx_eq_xxyy
    (form : actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)
    (first second : Fiber) :
    form.1 second first second first = form.1 first first second second := by
  exact (form.property.1 second first second first).trans
    (quartic_xyyx_eq_xxyy period hPeriod form first second)

private theorem quartic_yyxx_eq_xxyy
    (form : actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)
    (first second : Fiber) :
    form.1 second second first first = form.1 first first second second := by
  exact (form.property.2.1 second second first first).trans
    (quartic_yxyx_eq_xxyy period hPeriod form first second)

/-- First polarization step: diagonal quartic values recover the paired value
`T(x,x,y,y)`. -/
theorem actualPhysicalSecondOrderJetInvariantQuarticEvaluation_pairPolarization
    (form : actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)
    (first second : Fiber) :
    12 * form.1 first first second second =
      actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod form
          (first + second) +
        actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod form
          (first - second) -
        2 * actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod form first -
        2 * actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod form second := by
  have hXYXY := quartic_xyxy_eq_xxyy period hPeriod form first second
  have hXYYX := quartic_xyyx_eq_xxyy period hPeriod form first second
  have hYXXY := quartic_yxxy_eq_xxyy period hPeriod form first second
  have hYXYX := quartic_yxyx_eq_xxyy period hPeriod form first second
  have hYYXX := quartic_yyxx_eq_xxyy period hPeriod form first second
  unfold actualPhysicalSecondOrderJetInvariantQuarticEvaluation
  simp only [map_add, map_sub, add_apply, sub_apply]
  linear_combination -2 * hXYXY - 2 * hXYYX - 2 * hYXXY - 2 * hYXYX - 2 * hYYXX

private theorem quartic_pair_eq_of_evaluation_eq
    (firstForm secondForm :
      actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)
    (hEvaluation :
      actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod firstForm =
        actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod secondForm) :
    ∀ first second : Fiber,
      firstForm.1 first first second second =
        secondForm.1 first first second second := by
  intro first second
  have hAdd := congrFun hEvaluation (first + second)
  have hSub := congrFun hEvaluation (first - second)
  have hFirst := congrFun hEvaluation first
  have hSecond := congrFun hEvaluation second
  have hFirstPolarization :=
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation_pairPolarization
      period hPeriod firstForm first second
  have hSecondPolarization :=
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation_pairPolarization
      period hPeriod secondForm first second
  linarith

private theorem quartic_first_pair_eq
    (firstForm secondForm :
      actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)
    (hPair : ∀ first second : Fiber,
      firstForm.1 first first second second =
        secondForm.1 first first second second) :
    ∀ first second third : Fiber,
      firstForm.1 first second third third =
        secondForm.1 first second third third := by
  intro first second third
  have hAdd := hPair (first + second) third
  have hFirst := hPair first third
  have hSecond := hPair second third
  have hFirstSwap := firstForm.property.1 second first third third
  have hSecondSwap := secondForm.property.1 second first third third
  simp only [map_add, add_apply] at hAdd
  linarith

private theorem quartic_full_eq
    (firstForm secondForm :
      actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)
    (hFirstPair : ∀ first second third : Fiber,
      firstForm.1 first second third third =
        secondForm.1 first second third third) :
    ∀ first second third fourth : Fiber,
      firstForm.1 first second third fourth =
        secondForm.1 first second third fourth := by
  intro first second third fourth
  have hAdd := hFirstPair first second (third + fourth)
  have hThird := hFirstPair first second third
  have hFourth := hFirstPair first second fourth
  have hFirstSwap := firstForm.property.2.2.1 first second fourth third
  have hSecondSwap := secondForm.property.2.2.1 first second fourth third
  simp only [map_add, add_apply] at hAdd
  linarith

private theorem quadrilinear_subtype_ext
    (firstForm secondForm :
      actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod)
    (hFull : ∀ first second third fourth : Fiber,
      firstForm.1 first second third fourth =
        secondForm.1 first second third fourth) :
    firstForm = secondForm := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  apply ContinuousLinearMap.ext
  intro third
  apply ContinuousLinearMap.ext
  intro fourth
  exact hFull first second third fourth

/-- Diagonal evaluation is injective on symmetric quadrilinear forms. -/
theorem actualPhysicalSecondOrderJetInvariantQuarticEvaluation_injective :
    Function.Injective
      (fun form :
          actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod =>
        actualPhysicalSecondOrderJetInvariantQuarticEvaluation period hPeriod form) := by
  intro firstForm secondForm hEvaluation
  have hPair := quartic_pair_eq_of_evaluation_eq period hPeriod
    firstForm secondForm hEvaluation
  have hFirstPair := quartic_first_pair_eq period hPeriod firstForm secondForm hPair
  have hFull := quartic_full_eq period hPeriod firstForm secondForm hFirstPair
  exact quadrilinear_subtype_ext period hPeriod firstForm secondForm hFull

/-- Every invariant homogeneous quartic has a unique complete finite
coefficient family. -/
theorem actualPhysicalSecondOrderJetInvariantQuarticFunctional_existsUnique_coefficients
    (form : actualPhysicalSecondOrderJetInvariantSymmetricQuadrilinearForms period hPeriod) :
    ∃! coefficients :
        ActualPhysicalSecondOrderJetInvariantQuarticFunctionalIndex period hPeriod → Real,
      (actualPhysicalSecondOrderJetInvariantQuarticFunctionalCoordinateEquiv
        period hPeriod).symm coefficients = form := by
  refine ⟨actualPhysicalSecondOrderJetInvariantQuarticFunctionalCoordinateEquiv
      period hPeriod form, ?_, ?_⟩
  · exact (actualPhysicalSecondOrderJetInvariantQuarticFunctionalCoordinateEquiv
      period hPeriod).symm_apply_apply form
  · intro coefficients hCoefficients
    apply (actualPhysicalSecondOrderJetInvariantQuarticFunctionalCoordinateEquiv
      period hPeriod).symm.injective
    exact hCoefficients.trans
      ((actualPhysicalSecondOrderJetInvariantQuarticFunctionalCoordinateEquiv
        period hPeriod).symm_apply_apply form).symm

end
end P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuarticFunctionalBasis4D
end JanusFormal
