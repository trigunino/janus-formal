import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeTwoFunctionalBasis4D

/-!
# Invariant homogeneous cubic functionals

This gate classifies continuous symmetric trilinear forms fixed by every
genuine transition of the actual common physical second-jet bundle. Their
diagonal evaluations are invariant homogeneous cubic local functionals.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantCubicFunctionalBasis4D

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

local instance cubicActualLLNormedAddCommGroup :
    NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  actualLLNormedAddCommGroup

local instance cubicActualLLNormedSpace :
    NormedSpace Real ActualLLSecondOrderJetFiber :=
  actualLLNormedSpace

local instance cubicActualPhysicalFiniteDimensional :
    FiniteDimensional Real ActualPhysicalSecondOrderJetProductFiber :=
  actualPhysicalFiniteDimensional

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber

private abbrev LinearForm := Fiber →L[Real] Real

private abbrev BilinearForm := Fiber →L[Real] LinearForm

private abbrev TrilinearForm := Fiber →L[Real] BilinearForm

local instance cubicActualPhysicalNormedAddCommGroup :
    NormedAddCommGroup Fiber :=
  inferInstance

local instance cubicActualPhysicalNormedSpace :
    NormedSpace Real Fiber :=
  inferInstance

local instance cubicLinearAddCommGroup :
    AddCommGroup LinearForm :=
  inferInstance

local instance cubicLinearModule :
    Module Real LinearForm :=
  inferInstance

local instance cubicBilinearAddCommGroup :
    AddCommGroup BilinearForm :=
  inferInstance

local instance cubicBilinearModule :
    Module Real BilinearForm :=
  inferInstance

local instance cubicTrilinearAddCommGroup :
    AddCommGroup TrilinearForm :=
  inferInstance

local instance cubicTrilinearModule :
    Module Real TrilinearForm :=
  inferInstance

local instance cubicLinearFiniteDimensional :
    FiniteDimensional Real LinearForm :=
  inferInstance

local instance cubicBilinearFiniteDimensional :
    FiniteDimensional Real BilinearForm :=
  inferInstance

local instance cubicTrilinearFiniteDimensional :
    FiniteDimensional Real TrilinearForm :=
  inferInstance

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Chart :=
  ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod

private abbrev Base := MappingTorus (fixedEquatorData period hPeriod)

/-- An admissible continuous trilinear form is symmetric under the two
generating adjacent transpositions and invariant under simultaneous transport
of all three arguments. -/
def IsActualPhysicalSecondOrderJetInvariantSymmetricTrilinearForm
    (form : TrilinearForm) : Prop :=
  (∀ first second third, form first second third = form second first third) ∧
    (∀ first second third, form first second third = form first third second) ∧
      ∀ (first second : Chart period hPeriod) (base : Base period hPeriod),
        base ∈
            (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
              .positiveQuarter).baseSet first ∩
            (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
              .positiveQuarter).baseSet second →
          ∀ firstJet secondJet thirdJet,
            form
                ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
                  .positiveQuarter).coordChange first second base firstJet)
                ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
                  .positiveQuarter).coordChange first second base secondJet)
                ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
                  .positiveQuarter).coordChange first second base thirdJet) =
              form firstJet secondJet thirdJet

/-- The invariant symmetric continuous trilinear forms are a real subspace. -/
def actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms :
    Submodule Real TrilinearForm where
  carrier := IsActualPhysicalSecondOrderJetInvariantSymmetricTrilinearForm
    period hPeriod
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro first second third
      simp
    · intro first second third
      simp
    · intro first second base hBase firstJet secondJet thirdJet
      simp
  add_mem' := by
    intro firstForm secondForm hFirst hSecond
    refine ⟨?_, ?_, ?_⟩
    · intro first second third
      simp only [add_apply]
      rw [hFirst.1 first second third, hSecond.1 first second third]
    · intro first second third
      simp only [add_apply]
      rw [hFirst.2.1 first second third, hSecond.2.1 first second third]
    · intro first second base hBase firstJet secondJet thirdJet
      simp only [add_apply]
      rw [hFirst.2.2 first second base hBase firstJet secondJet thirdJet,
        hSecond.2.2 first second base hBase firstJet secondJet thirdJet]
  smul_mem' := by
    intro scalar form hForm
    refine ⟨?_, ?_, ?_⟩
    · intro first second third
      simp only [smul_apply]
      rw [hForm.1 first second third]
    · intro first second third
      simp only [smul_apply]
      rw [hForm.2.1 first second third]
    · intro first second base hBase firstJet secondJet thirdJet
      simp only [smul_apply]
      rw [hForm.2.2 first second base hBase firstJet secondJet thirdJet]

local instance invariantSymmetricTrilinearFormsAddCommGroup :
    AddCommGroup
      (actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod) :=
  (actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod).toAddSubgroup.toAddCommGroup

/-- The complete invariant symmetric trilinear class is finite-dimensional. -/
theorem actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms_finiteDimensional :
    FiniteDimensional Real
      (actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period
        hPeriod) :=
  inferInstance

local instance invariantSymmetricTrilinearFormsFiniteDimensional :
    FiniteDimensional Real
      (actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period
        hPeriod) :=
  actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms_finiteDimensional
    period hPeriod

/-- Finite coefficient index of the invariant homogeneous cubic class. -/
abbrev ActualPhysicalSecondOrderJetInvariantCubicFunctionalIndex :=
  Module.Basis.ofVectorSpaceIndex Real
    (actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod)

/-- A finite basis of all invariant symmetric continuous trilinear forms. -/
def actualPhysicalSecondOrderJetInvariantCubicFunctionalBasis :
    Module.Basis
      (ActualPhysicalSecondOrderJetInvariantCubicFunctionalIndex period hPeriod)
      Real
      (actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod) :=
  Module.Basis.ofVectorSpace Real
    (actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod)

/-- Exact finite coordinates of an invariant symmetric trilinear form. -/
def actualPhysicalSecondOrderJetInvariantCubicFunctionalCoordinateEquiv :
    actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod ≃ₗ[Real]
      (ActualPhysicalSecondOrderJetInvariantCubicFunctionalIndex period hPeriod → Real) :=
  (actualPhysicalSecondOrderJetInvariantCubicFunctionalBasis period hPeriod).equivFun

/-- The homogeneous cubic functional represented by an invariant symmetric
trilinear form. -/
def actualPhysicalSecondOrderJetInvariantCubicEvaluation
    (form : actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod)
    (jet : Fiber) : Real :=
  form.1 jet jet jet

/-- Every represented cubic functional is invariant under every genuine
second-jet transition. -/
theorem actualPhysicalSecondOrderJetInvariantCubicEvaluation_transitionInvariant
    (form : actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : Fiber) :
    actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod form
        ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).coordChange first second base jet) =
      actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod form jet :=
  form.property.2.2 first second base hBase jet jet jet

/-- Polarization identity for diagonal evaluation of a symmetric trilinear
form. -/
theorem actualPhysicalSecondOrderJetInvariantCubicEvaluation_polarization
    (form : actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod)
    (first second third : Fiber) :
    6 * form.1 first second third =
      actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod form
          (first + second + third) -
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod form
          (first + second) -
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod form
          (first + third) -
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod form
          (second + third) +
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod form first +
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod form second +
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod form third := by
  have hACB : form.1 first third second = form.1 first second third :=
    (form.property.2.1 first second third).symm
  have hBAC : form.1 second first third = form.1 first second third :=
    (form.property.1 first second third).symm
  have hBCA : form.1 second third first = form.1 first second third := by
    rw [form.property.1 second third first,
      form.property.2.1 third second first,
      form.property.1 third first second, hACB]
  have hCAB : form.1 third first second = form.1 first second third := by
    rw [form.property.1 third first second, hACB]
  have hCBA : form.1 third second first = form.1 first second third := by
    rw [form.property.2.1 third second first, hCAB]
  unfold actualPhysicalSecondOrderJetInvariantCubicEvaluation
  simp only [map_add, add_apply]
  simp only [hACB, hBAC, hBCA, hCAB, hCBA]
  ring

/-- Diagonal evaluation is injective on symmetric trilinear forms. -/
theorem actualPhysicalSecondOrderJetInvariantCubicEvaluation_injective :
    Function.Injective
      (fun form :
          actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod =>
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod form) := by
  intro firstForm secondForm hEvaluation
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  apply ContinuousLinearMap.ext
  intro third
  have hAll :
      actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm
          (first + second + third) =
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm
          (first + second + third) :=
    congrFun hEvaluation (first + second + third)
  have hFirstSecond :
      actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm
          (first + second) =
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm
          (first + second) :=
    congrFun hEvaluation (first + second)
  have hFirstThird :
      actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm
          (first + third) =
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm
          (first + third) :=
    congrFun hEvaluation (first + third)
  have hSecondThird :
      actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm
          (second + third) =
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm
          (second + third) :=
    congrFun hEvaluation (second + third)
  have hFirst :
      actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm first =
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm first :=
    congrFun hEvaluation first
  have hSecond :
      actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm second =
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm second :=
    congrFun hEvaluation second
  have hThird :
      actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm third =
        actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm third :=
    congrFun hEvaluation third
  have hSix :
      6 * firstForm.1 first second third =
        6 * secondForm.1 first second third := by
    calc
      6 * firstForm.1 first second third =
          actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm
              (first + second + third) -
            actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm
              (first + second) -
            actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm
              (first + third) -
            actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm
              (second + third) +
            actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm first +
            actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm second +
            actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod firstForm third :=
        actualPhysicalSecondOrderJetInvariantCubicEvaluation_polarization
          period hPeriod firstForm first second third
      _ = actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm
              (first + second + third) -
            actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm
              (first + second) -
            actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm
              (first + third) -
            actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm
              (second + third) +
            actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm first +
            actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm second +
            actualPhysicalSecondOrderJetInvariantCubicEvaluation period hPeriod secondForm third := by
        rw [hAll, hFirstSecond, hFirstThird, hSecondThird, hFirst, hSecond, hThird]
      _ = 6 * secondForm.1 first second third :=
        (actualPhysicalSecondOrderJetInvariantCubicEvaluation_polarization
          period hPeriod secondForm first second third).symm
  linarith

/-- Every invariant homogeneous cubic functional has a unique complete finite
coefficient family. -/
theorem actualPhysicalSecondOrderJetInvariantCubicFunctional_existsUnique_coefficients
    (form : actualPhysicalSecondOrderJetInvariantSymmetricTrilinearForms period hPeriod) :
    ∃! coefficients :
        ActualPhysicalSecondOrderJetInvariantCubicFunctionalIndex period hPeriod → Real,
      (actualPhysicalSecondOrderJetInvariantCubicFunctionalCoordinateEquiv
        period hPeriod).symm coefficients = form := by
  refine ⟨actualPhysicalSecondOrderJetInvariantCubicFunctionalCoordinateEquiv
      period hPeriod form, ?_, ?_⟩
  · exact (actualPhysicalSecondOrderJetInvariantCubicFunctionalCoordinateEquiv
      period hPeriod).symm_apply_apply form
  · intro coefficients hCoefficients
    apply (actualPhysicalSecondOrderJetInvariantCubicFunctionalCoordinateEquiv
      period hPeriod).symm.injective
    exact hCoefficients.trans
      ((actualPhysicalSecondOrderJetInvariantCubicFunctionalCoordinateEquiv
        period hPeriod).symm_apply_apply form).symm

end
end P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantCubicFunctionalBasis4D
end JanusFormal
