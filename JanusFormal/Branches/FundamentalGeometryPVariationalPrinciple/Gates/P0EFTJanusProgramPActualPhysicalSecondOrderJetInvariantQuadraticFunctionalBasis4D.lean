import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D

/-!
# Invariant quadratic functionals on the actual physical second-jet fiber

This gate classifies the explicitly bounded class of homogeneous quadratic
local functionals represented by continuous symmetric bilinear forms fixed by
every genuine transition of the actual common physical second-jet bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuadraticFunctionalBasis4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open Set
open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D

local instance quadraticActualLLNormedAddCommGroup :
    NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  actualLLNormedAddCommGroup

local instance quadraticActualLLNormedSpace :
    NormedSpace Real ActualLLSecondOrderJetFiber :=
  actualLLNormedSpace

local instance quadraticActualPhysicalFiniteDimensional :
    FiniteDimensional Real ActualPhysicalSecondOrderJetProductFiber :=
  actualPhysicalFiniteDimensional

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber

private abbrev BilinearForm := Fiber →L[Real] Fiber →L[Real] Real

local instance quadraticActualPhysicalNormedAddCommGroup :
    NormedAddCommGroup Fiber :=
  inferInstance

local instance quadraticActualPhysicalNormedSpace :
    NormedSpace Real Fiber :=
  inferInstance

local instance quadraticActualPhysicalBilinearAddCommGroup :
    AddCommGroup BilinearForm :=
  inferInstance

local instance quadraticActualPhysicalBilinearModule :
    Module Real BilinearForm :=
  inferInstance

local instance quadraticActualPhysicalDualFiniteDimensional :
    FiniteDimensional Real (Fiber →L[Real] Real) :=
  inferInstance

local instance quadraticActualPhysicalBilinearFiniteDimensional :
    FiniteDimensional Real BilinearForm :=
  inferInstance

private abbrev Chart :=
  ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod

private abbrev Base := MappingTorus (fixedEquatorData period hPeriod)

/-- A continuous bilinear form is admissible when it is symmetric and fixed
by simultaneous transport of both arguments through every genuine overlap. -/
def IsActualPhysicalSecondOrderJetInvariantSymmetricBilinearForm
    (form : BilinearForm) : Prop :=
  (∀ first second, form first second = form second first) ∧
    ∀ (first second : Chart period hPeriod) (base : Base period hPeriod),
      base ∈
          (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
            .positiveQuarter).baseSet first ∩
          (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
            .positiveQuarter).baseSet second →
        ∀ firstJet secondJet,
          form
              ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
                .positiveQuarter).coordChange first second base firstJet)
              ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
                .positiveQuarter).coordChange first second base secondJet) =
            form firstJet secondJet

/-- The invariant symmetric continuous bilinear forms are a real subspace. -/
def actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms :
    Submodule Real BilinearForm where
  carrier :=
    IsActualPhysicalSecondOrderJetInvariantSymmetricBilinearForm period hPeriod
  zero_mem' := by
    constructor
    · intro first second
      rfl
    · intro first second base hBase firstJet secondJet
      rfl
  add_mem' := by
    intro firstForm secondForm hFirst hSecond
    constructor
    · intro first second
      simp only [add_apply]
      rw [hFirst.1 first second, hSecond.1 first second]
    · intro first second base hBase firstJet secondJet
      simp only [add_apply]
      rw [hFirst.2 first second base hBase firstJet secondJet,
        hSecond.2 first second base hBase firstJet secondJet]
  smul_mem' := by
    intro scalar form hForm
    constructor
    · intro first second
      simp only [smul_apply]
      rw [hForm.1 first second]
    · intro first second base hBase firstJet secondJet
      simp only [smul_apply]
      rw [hForm.2 first second base hBase firstJet secondJet]

local instance invariantSymmetricBilinearFormsAddCommGroup :
    AddCommGroup
      (actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period hPeriod) :=
  (actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period hPeriod).toAddSubgroup.toAddCommGroup

/-- The complete invariant symmetric bilinear class is finite-dimensional. -/
theorem actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms_finiteDimensional :
    FiniteDimensional Real
      (actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period
        hPeriod) :=
  inferInstance

local instance invariantSymmetricBilinearFormsFiniteDimensional :
    FiniteDimensional Real
      (actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period
        hPeriod) :=
  actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms_finiteDimensional
    period hPeriod

/-- Finite coefficient index of the invariant homogeneous quadratic class. -/
abbrev ActualPhysicalSecondOrderJetInvariantQuadraticFunctionalIndex :=
  Module.Basis.ofVectorSpaceIndex Real
    (actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period hPeriod)

/-- A finite basis of every invariant symmetric continuous bilinear form. -/
def actualPhysicalSecondOrderJetInvariantQuadraticFunctionalBasis :
    Module.Basis
      (ActualPhysicalSecondOrderJetInvariantQuadraticFunctionalIndex period hPeriod)
      Real
      (actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period hPeriod) :=
  Module.Basis.ofVectorSpace Real
    (actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period hPeriod)

/-- Exact finite coordinates of an invariant symmetric bilinear form. -/
def actualPhysicalSecondOrderJetInvariantQuadraticFunctionalCoordinateEquiv :
    actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period hPeriod ≃ₗ[Real]
      (ActualPhysicalSecondOrderJetInvariantQuadraticFunctionalIndex period hPeriod → Real) :=
  (actualPhysicalSecondOrderJetInvariantQuadraticFunctionalBasis period hPeriod).equivFun

/-- The homogeneous quadratic functional represented by an invariant symmetric
bilinear form. -/
def actualPhysicalSecondOrderJetInvariantQuadraticEvaluation
    (form : actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period hPeriod)
    (jet : Fiber) : Real :=
  form.1 jet jet

/-- Every represented quadratic functional is unchanged by every genuine
second-jet transition. -/
theorem actualPhysicalSecondOrderJetInvariantQuadraticEvaluation_transitionInvariant
    (form : actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : Fiber) :
    actualPhysicalSecondOrderJetInvariantQuadraticEvaluation period hPeriod form
        ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).coordChange first second base jet) =
      actualPhysicalSecondOrderJetInvariantQuadraticEvaluation period hPeriod form jet :=
  form.property.2 first second base hBase jet jet

/-- Polarization makes diagonal evaluation injective on symmetric bilinear
forms, so distinct classified forms define distinct quadratic functionals. -/
theorem actualPhysicalSecondOrderJetInvariantQuadraticEvaluation_injective :
    Function.Injective
      (fun form :
          actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period hPeriod =>
        actualPhysicalSecondOrderJetInvariantQuadraticEvaluation period hPeriod form) := by
  intro firstForm secondForm hEvaluation
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro firstJet
  apply ContinuousLinearMap.ext
  intro secondJet
  have hSum := congrFun hEvaluation (firstJet + secondJet)
  have hFirst := congrFun hEvaluation firstJet
  have hSecond := congrFun hEvaluation secondJet
  have firstPolarization :
      2 * firstForm.1 firstJet secondJet =
        firstForm.1 (firstJet + secondJet) (firstJet + secondJet) -
          firstForm.1 firstJet firstJet - firstForm.1 secondJet secondJet := by
    simp only [map_add, add_apply]
    rw [firstForm.property.1 secondJet firstJet]
    ring
  have secondPolarization :
      2 * secondForm.1 firstJet secondJet =
        secondForm.1 (firstJet + secondJet) (firstJet + secondJet) -
          secondForm.1 firstJet firstJet - secondForm.1 secondJet secondJet := by
    simp only [map_add, add_apply]
    rw [secondForm.property.1 secondJet firstJet]
    ring
  dsimp [actualPhysicalSecondOrderJetInvariantQuadraticEvaluation] at hSum hFirst hSecond
  have hTwice :
      2 * firstForm.1 firstJet secondJet =
        2 * secondForm.1 firstJet secondJet := by
    calc
      2 * firstForm.1 firstJet secondJet =
          firstForm.1 (firstJet + secondJet) (firstJet + secondJet) -
            firstForm.1 firstJet firstJet - firstForm.1 secondJet secondJet :=
        firstPolarization
      _ = secondForm.1 (firstJet + secondJet) (firstJet + secondJet) -
            secondForm.1 firstJet firstJet - secondForm.1 secondJet secondJet := by
        rw [hSum, hFirst, hSecond]
      _ = 2 * secondForm.1 firstJet secondJet := secondPolarization.symm
  linarith

/-- Every invariant homogeneous quadratic functional has a unique complete
finite coefficient family. -/
theorem actualPhysicalSecondOrderJetInvariantQuadraticFunctional_existsUnique_coefficients
    (form : actualPhysicalSecondOrderJetInvariantSymmetricBilinearForms period hPeriod) :
    ∃! coefficients :
        ActualPhysicalSecondOrderJetInvariantQuadraticFunctionalIndex period hPeriod → Real,
      (actualPhysicalSecondOrderJetInvariantQuadraticFunctionalCoordinateEquiv
        period hPeriod).symm coefficients = form := by
  refine ⟨actualPhysicalSecondOrderJetInvariantQuadraticFunctionalCoordinateEquiv
      period hPeriod form, ?_, ?_⟩
  · exact (actualPhysicalSecondOrderJetInvariantQuadraticFunctionalCoordinateEquiv
      period hPeriod).symm_apply_apply form
  · intro coefficients hCoefficients
    apply (actualPhysicalSecondOrderJetInvariantQuadraticFunctionalCoordinateEquiv
      period hPeriod).symm.injective
    exact hCoefficients.trans
      ((actualPhysicalSecondOrderJetInvariantQuadraticFunctionalCoordinateEquiv
        period hPeriod).symm_apply_apply form).symm

end
end P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuadraticFunctionalBasis4D
end JanusFormal
