import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

/-!
# Shifted coercivity from a positive square decomposition

The canonical shifted form is coercive whenever its quadratic part splits as

`Bρ(u,u) = ‖Q u‖² + gap * ‖u‖²`

with `gap > 0`.  This is the natural endpoint of a completion-of-squares or
positive-square-root argument.  The nonnegative square term immediately gives
the Lax--Milgram coercivity inequality with constant `gap`.

Thus the final analytic interface may supply an exact positive decomposition
instead of repeating a separate coercivity proof and constant.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTriplePositiveShiftedForm4D
end P0EFTJanusMappingTorusScalarCompletedBoundaryTriplePositiveShiftedForm4D

namespace P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

variable {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core}

/-- Positive square decomposition of one canonical shifted form. -/
structure LagrangianShiftedPositiveDecompositionData
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) where
  positivePart :
    triple.lagrangianDomainSubmodule condition →L[Real]
      triple.lagrangianDomainSubmodule condition
  gap : Real
  gap_pos : 0 < gap
  form_eq : ∀ field : triple.lagrangianDomainSubmodule condition,
    triple.lagrangianShiftedForm condition spectralParameter field field =
      ‖positivePart field‖ ^ 2 + gap * ‖field‖ ^ 2

namespace LagrangianShiftedPositiveDecompositionData

/-- Positive decomposition implies the canonical shifted coercivity inequality. -/
theorem coercive
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (positive : triple.LagrangianShiftedPositiveDecompositionData
      condition spectralParameter)
    (field : triple.lagrangianDomainSubmodule condition) :
    positive.gap * ‖field‖ * ‖field‖ ≤
      triple.lagrangianShiftedForm condition spectralParameter field field := by
  rw [positive.form_eq]
  nlinarith [sq_nonneg ‖positive.positivePart field‖]

/-- Conversion to the canonical shifted-form coercivity package. -/
def toShiftedFormCoerciveData
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (positive : triple.LagrangianShiftedPositiveDecompositionData
      condition spectralParameter) :
    triple.LagrangianShiftedFormCoerciveData condition spectralParameter where
  constant := positive.gap
  constant_pos := positive.gap_pos
  coercive := positive.coercive triple condition spectralParameter

/-- Positive decomposition produces the bounded direct resolvent. -/
noncomputable def boundedResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (positive : triple.LagrangianShiftedPositiveDecompositionData
      condition spectralParameter)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :=
  (positive.toShiftedFormCoerciveData triple condition spectralParameter)
    |>.boundedResolvent triple condition spectralParameter hDense

/-- Positive shifted-form certificate. -/
theorem certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (positive : triple.LagrangianShiftedPositiveDecompositionData
      condition spectralParameter) :
    (∀ field : triple.lagrangianDomainSubmodule condition,
      triple.lagrangianShiftedForm condition spectralParameter field field =
        ‖positive.positivePart field‖ ^ 2 + positive.gap * ‖field‖ ^ 2) ∧
      (∀ field : triple.lagrangianDomainSubmodule condition,
        positive.gap * ‖field‖ * ‖field‖ ≤
          triple.lagrangianShiftedForm condition spectralParameter field field) :=
  ⟨positive.form_eq,
    positive.coercive triple condition spectralParameter⟩

end LagrangianShiftedPositiveDecompositionData

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
end JanusFormal
