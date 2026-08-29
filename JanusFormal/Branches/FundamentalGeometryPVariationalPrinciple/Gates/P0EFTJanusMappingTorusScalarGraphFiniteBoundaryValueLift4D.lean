import Mathlib.Analysis.Normed.Module.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphPoissonFromDirichletResolvent4D

/-!
# Automatic finite-dimensional boundary value lift

The completed paired trace is surjective.  Therefore its value component is
surjective.  If the trace Hilbert space is finite-dimensional, projectivity gives
an algebraic linear right inverse and finite-dimensionality makes that inverse
automatically continuous.

Thus, in finite-dimensional boundary reductions, the continuous value-boundary
lift required for the Poisson construction is not an additional analytic
hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphFiniteBoundaryValueLift4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonFromDirichletResolvent4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  [FiniteDimensional Real Trace]

/-- Surjectivity of the paired completed trace implies surjectivity of the value
trace. -/
theorem canonicalScalarCompletedValueTrace_surjective
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Function.Surjective
      (canonicalScalarCompletedValueTrace data traceBound) := by
  intro boundaryValue
  obtain ⟨field, hField⟩ :=
    canonicalScalarCompletedBoundaryTrace_surjective
      data traceBound (boundaryValue, 0)
  refine ⟨field, ?_⟩
  exact congrArg Prod.fst hField

/-- Algebraic right inverse of the completed value trace in finite dimension. -/
noncomputable def canonicalScalarCompletedValueTraceLinearRightInverse
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Trace →ₗ[Real] CanonicalScalarOperatorGraphSpace data := by
  let valueTrace := (canonicalScalarCompletedValueTrace data traceBound).toLinearMap
  have hRange : LinearMap.range valueTrace = ⊤ :=
    LinearMap.range_eq_top.mpr
      (canonicalScalarCompletedValueTrace_surjective data traceBound)
  exact Classical.choose (valueTrace.exists_rightInverse_of_surjective hRange)

/-- The algebraic right inverse really splits the value trace. -/
theorem canonicalScalarCompletedValueTraceLinearRightInverse_rightInverse
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    (canonicalScalarCompletedValueTrace data traceBound).toLinearMap.comp
        (canonicalScalarCompletedValueTraceLinearRightInverse data traceBound) =
      LinearMap.id := by
  let valueTrace := (canonicalScalarCompletedValueTrace data traceBound).toLinearMap
  have hRange : LinearMap.range valueTrace = ⊤ :=
    LinearMap.range_eq_top.mpr
      (canonicalScalarCompletedValueTrace_surjective data traceBound)
  exact Classical.choose_spec
    (valueTrace.exists_rightInverse_of_surjective hRange)

/-- The finite-dimensional algebraic right inverse as a continuous linear map. -/
noncomputable def canonicalScalarCompletedValueTraceContinuousRightInverse
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Trace →L[Real] CanonicalScalarOperatorGraphSpace data :=
  (canonicalScalarCompletedValueTraceLinearRightInverse
    data traceBound).toContinuousLinearMap

/-- Continuous right-inverse identity. -/
theorem canonicalScalarCompletedValueTraceContinuousRightInverse_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (boundary : Trace) :
    canonicalScalarCompletedValueTrace data traceBound
        (canonicalScalarCompletedValueTraceContinuousRightInverse
          data traceBound boundary) = boundary := by
  have hSplit := DFunLike.congr_fun
    (canonicalScalarCompletedValueTraceLinearRightInverse_rightInverse
      data traceBound) boundary
  exact hSplit

/-- Automatic boundary-lift package in finite trace dimension. -/
noncomputable def canonicalScalarGraphFiniteBoundaryValueLiftData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    CanonicalScalarGraphBoundaryValueLiftData data traceBound where
  lift := canonicalScalarCompletedValueTraceContinuousRightInverse
    data traceBound
  value_trace := canonicalScalarCompletedValueTraceContinuousRightInverse_apply
    data traceBound

/-- Finite-dimensional boundary lift certificate. -/
theorem canonicalScalarGraphFiniteBoundaryValueLift_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Function.Surjective
        (canonicalScalarCompletedValueTrace data traceBound) ∧
      (∀ boundary : Trace,
        canonicalScalarCompletedValueTrace data traceBound
          ((canonicalScalarGraphFiniteBoundaryValueLiftData
            data traceBound).lift boundary) = boundary) :=
  ⟨canonicalScalarCompletedValueTrace_surjective data traceBound,
    (canonicalScalarGraphFiniteBoundaryValueLiftData
      data traceBound).value_trace⟩

end
end P0EFTJanusMappingTorusScalarGraphFiniteBoundaryValueLift4D
end JanusFormal
