import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetNormedSpace4D
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Invariant bounded linear functionals on the actual physical second-jet fiber

The actual common physical second-jet fiber is finite-dimensional.  This gate
cuts out the subspace of bounded linear functionals fixed by every genuine
bundle coordinate change and gives that subspace finite coordinates.  It is an
exhaustive classification for this explicitly bounded linear class only; no
classification of nonlinear local functionals is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open Set
open scoped RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

private abbrev RawLLSecondOrderJetFiber :=
  ((FramedSecondOrderJet ThroatCoverCoordinates LLMetricFiber ×
      FramedSecondOrderJet ThroatCoverCoordinates Real) ×
    FramedSecondOrderJet ThroatCoverCoordinates LLFieldFiber)

local instance actualLLNormedAddCommGroup :
    NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  inferInstanceAs (NormedAddCommGroup RawLLSecondOrderJetFiber)

local instance actualLLNormedSpace :
    NormedSpace Real ActualLLSecondOrderJetFiber :=
  inferInstanceAs (NormedSpace Real RawLLSecondOrderJetFiber)

local instance actualLLFiniteDimensional :
    FiniteDimensional Real ActualLLSecondOrderJetFiber :=
  inferInstanceAs (FiniteDimensional Real RawLLSecondOrderJetFiber)

private abbrev RawGaugeLLSecondOrderJetFiber :=
  ActualGaugeSecondOrderJetProductFiber × ActualLLSecondOrderJetFiber

private abbrev RawGaugeLLMetricSecondOrderJetFiber :=
  RawGaugeLLSecondOrderJetFiber × ActualMetricSecondOrderJetProductFiber

private abbrev RawPhysicalSecondOrderJetFiber :=
  RawGaugeLLMetricSecondOrderJetFiber ×
    ActualSpinCSecondOrderJetProductFiber

local instance rawGaugeLLFiniteDimensional :
    FiniteDimensional Real RawGaugeLLSecondOrderJetFiber :=
  inferInstance

local instance rawGaugeLLMetricFiniteDimensional :
    FiniteDimensional Real RawGaugeLLMetricSecondOrderJetFiber :=
  inferInstance

local instance actualPhysicalFiniteDimensional :
    FiniteDimensional Real ActualPhysicalSecondOrderJetProductFiber :=
  inferInstanceAs (FiniteDimensional Real RawPhysicalSecondOrderJetFiber)

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber

private abbrev Chart :=
  ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod

private abbrev Base :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- A bounded linear local functional is invariant when it is unchanged by
every actual physical second-jet transition on every genuine overlap. -/
def IsActualPhysicalSecondOrderJetTransitionInvariant
    (functional : Fiber →L[Real] Real) : Prop :=
  ∀ (first second : Chart period hPeriod) (base : Base period hPeriod),
    base ∈
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet first ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet second →
      ∀ jet,
        functional
            ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
              .positiveQuarter).coordChange first second base jet) =
          functional jet

/-- The transition-invariant bounded linear local functionals form a real
linear subspace of the continuous dual of the actual physical second-jet
fiber. -/
def actualPhysicalSecondOrderJetTransitionInvariantFunctionals :
    Submodule Real (Fiber →L[Real] Real) where
  carrier := IsActualPhysicalSecondOrderJetTransitionInvariant period hPeriod
  zero_mem' := by
    intro first second base hBase jet
    rfl
  add_mem' := by
    intro firstFunctional secondFunctional hFirst hSecond first second base hBase jet
    simp only [add_apply]
    rw [hFirst first second base hBase jet,
      hSecond first second base hBase jet]
  smul_mem' := by
    intro scalar functional hFunctional first second base hBase jet
    simp only [smul_apply]
    rw [hFunctional first second base hBase jet]

/-- The invariant bounded-linear class is finite-dimensional because it is a
subspace of the continuous dual of the finite-dimensional actual fiber. -/
theorem actualPhysicalSecondOrderJetTransitionInvariantFunctionals_finiteDimensional :
    FiniteDimensional Real
      (actualPhysicalSecondOrderJetTransitionInvariantFunctionals period
        hPeriod) :=
  inferInstance

local instance actualPhysicalSecondOrderJetInvariantFiniteDimensional :
    FiniteDimensional Real
      (actualPhysicalSecondOrderJetTransitionInvariantFunctionals period
        hPeriod) :=
  actualPhysicalSecondOrderJetTransitionInvariantFunctionals_finiteDimensional
    period hPeriod

/-- Finite coefficient index of the invariant bounded-linear class. -/
abbrev ActualPhysicalSecondOrderJetInvariantFunctionalIndex :=
  Module.Basis.ofVectorSpaceIndex Real
    (actualPhysicalSecondOrderJetTransitionInvariantFunctionals period hPeriod)

/-- A finite basis of the full transition-invariant bounded-linear class. -/
def actualPhysicalSecondOrderJetInvariantFunctionalBasis :
    Module.Basis
      (ActualPhysicalSecondOrderJetInvariantFunctionalIndex period hPeriod)
      Real
      (actualPhysicalSecondOrderJetTransitionInvariantFunctionals period hPeriod) :=
  Module.Basis.ofVectorSpace Real
    (actualPhysicalSecondOrderJetTransitionInvariantFunctionals period hPeriod)

/-- Linear equivalence between invariant bounded functionals and their full
finite coefficient families. -/
def actualPhysicalSecondOrderJetInvariantFunctionalCoordinateEquiv :
    actualPhysicalSecondOrderJetTransitionInvariantFunctionals period hPeriod ≃ₗ[Real]
      (ActualPhysicalSecondOrderJetInvariantFunctionalIndex period hPeriod → Real) :=
  (actualPhysicalSecondOrderJetInvariantFunctionalBasis period hPeriod).equivFun

/-- Exact finite coordinates of an invariant bounded linear functional. -/
def actualPhysicalSecondOrderJetInvariantFunctionalCoordinates
    (functional :
      actualPhysicalSecondOrderJetTransitionInvariantFunctionals period hPeriod) :
    ActualPhysicalSecondOrderJetInvariantFunctionalIndex period hPeriod → Real :=
  actualPhysicalSecondOrderJetInvariantFunctionalCoordinateEquiv period hPeriod
    functional

/-- Synthesis of an invariant bounded linear functional from its complete
finite coefficient family. -/
def actualPhysicalSecondOrderJetInvariantFunctionalSynthesis
    (coefficients :
      ActualPhysicalSecondOrderJetInvariantFunctionalIndex period hPeriod → Real) :
    actualPhysicalSecondOrderJetTransitionInvariantFunctionals period hPeriod :=
  (actualPhysicalSecondOrderJetInvariantFunctionalCoordinateEquiv period hPeriod).symm
    coefficients

/-- Every invariant bounded linear local functional is reconstructed exactly
from its finite coefficient family. -/
@[simp]
theorem actualPhysicalSecondOrderJetInvariantFunctional_reconstruction
    (functional :
      actualPhysicalSecondOrderJetTransitionInvariantFunctionals period hPeriod) :
    actualPhysicalSecondOrderJetInvariantFunctionalSynthesis period hPeriod
        (actualPhysicalSecondOrderJetInvariantFunctionalCoordinates period hPeriod
          functional) =
      functional :=
  (actualPhysicalSecondOrderJetInvariantFunctionalCoordinateEquiv period hPeriod)
    |>.symm_apply_apply functional

/-- The complete coefficient family of an invariant bounded linear local
functional exists and is unique. -/
theorem actualPhysicalSecondOrderJetInvariantFunctional_existsUnique_coefficients
    (functional :
      actualPhysicalSecondOrderJetTransitionInvariantFunctionals period hPeriod) :
    ∃! coefficients :
        ActualPhysicalSecondOrderJetInvariantFunctionalIndex period hPeriod → Real,
      actualPhysicalSecondOrderJetInvariantFunctionalSynthesis period hPeriod
          coefficients = functional := by
  refine ⟨actualPhysicalSecondOrderJetInvariantFunctionalCoordinates period hPeriod
      functional, ?_, ?_⟩
  · exact actualPhysicalSecondOrderJetInvariantFunctional_reconstruction
      period hPeriod functional
  · intro coefficients hCoefficients
    apply
      (actualPhysicalSecondOrderJetInvariantFunctionalCoordinateEquiv period hPeriod).symm.injective
    exact hCoefficients.trans
      (actualPhysicalSecondOrderJetInvariantFunctional_reconstruction
        period hPeriod functional).symm

end
end P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
end JanusFormal
