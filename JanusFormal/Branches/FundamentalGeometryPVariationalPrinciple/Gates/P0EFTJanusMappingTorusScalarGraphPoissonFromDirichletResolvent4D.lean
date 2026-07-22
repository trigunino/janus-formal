import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarBoundaryReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D

/-!
# Construction of the Poisson operator from a boundary lift

A Poisson operator need not be an independent analytic input.  Given:

* a continuous lift of arbitrary value boundary data into the completed graph;
* a bounded Dirichlet resolvent at the chosen spectral parameter;

one corrects the lift by the Dirichlet resolvent of its bulk residual.  The
result has the same value trace and solves the homogeneous shifted equation.
Dirichlet uniqueness proves uniqueness of the corrected solution.

This is the standard extension-minus-resolvent construction of the Poisson
operator.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphPoissonFromDirichletResolvent4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Continuous right inverse of the completed value trace. -/
structure CanonicalScalarGraphBoundaryValueLiftData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) where
  lift : Trace →L[Real] CanonicalScalarOperatorGraphSpace data
  value_trace : ∀ boundary : Trace,
    canonicalScalarCompletedValueTrace data traceBound (lift boundary) = boundary

/-- Bulk residual of a raw boundary lift. -/
def canonicalScalarGraphBoundaryLiftResidual
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (liftData : CanonicalScalarGraphBoundaryValueLiftData data traceBound) :
    Trace →L[Real] Ambient :=
  (canonicalScalarGraphShiftedOperator data spectralParameter).comp liftData.lift

/-- Corrected Poisson operator `E - R_D (A-lambda) E`. -/
def canonicalScalarGraphPoissonOfBoundaryLift
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (liftData : CanonicalScalarGraphBoundaryValueLiftData data traceBound)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter) :
    Trace →L[Real] CanonicalScalarOperatorGraphSpace data :=
  liftData.lift -
    dirichlet.resolvent.comp
      (canonicalScalarGraphBoundaryLiftResidual
        data traceBound spectralParameter liftData)

@[simp] theorem canonicalScalarGraphPoissonOfBoundaryLift_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (liftData : CanonicalScalarGraphBoundaryValueLiftData data traceBound)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (boundary : Trace) :
    canonicalScalarGraphPoissonOfBoundaryLift
        data traceBound spectralParameter liftData dirichlet boundary =
      liftData.lift boundary -
        dirichlet.resolvent
          (canonicalScalarGraphShiftedOperator
            data spectralParameter (liftData.lift boundary)) :=
  rfl

/-- The corrected Poisson operator preserves the prescribed value trace. -/
theorem canonicalScalarGraphPoissonOfBoundaryLift_value_trace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (liftData : CanonicalScalarGraphBoundaryValueLiftData data traceBound)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (boundary : Trace) :
    canonicalScalarCompletedValueTrace data traceBound
        (canonicalScalarGraphPoissonOfBoundaryLift
          data traceBound spectralParameter liftData dirichlet boundary) =
      boundary := by
  rw [canonicalScalarGraphPoissonOfBoundaryLift_apply, map_sub,
    liftData.value_trace, dirichlet.value_zero, sub_zero]

/-- The corrected Poisson operator solves the homogeneous shifted equation. -/
theorem canonicalScalarGraphPoissonOfBoundaryLift_homogeneous
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (liftData : CanonicalScalarGraphBoundaryValueLiftData data traceBound)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (boundary : Trace) :
    canonicalScalarGraphShiftedOperator data spectralParameter
        (canonicalScalarGraphPoissonOfBoundaryLift
          data traceBound spectralParameter liftData dirichlet boundary) = 0 := by
  rw [canonicalScalarGraphPoissonOfBoundaryLift_apply, map_sub,
    dirichlet.equation, sub_self]

/-- Uniqueness of the corrected Poisson solution. -/
theorem canonicalScalarGraphPoissonOfBoundaryLift_unique
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (liftData : CanonicalScalarGraphBoundaryValueLiftData data traceBound)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (field : CanonicalScalarOperatorGraphSpace data) (boundary : Trace)
    (hValue : canonicalScalarCompletedValueTrace data traceBound field = boundary)
    (hEquation : canonicalScalarGraphShiftedOperator
      data spectralParameter field = 0) :
    field = canonicalScalarGraphPoissonOfBoundaryLift
      data traceBound spectralParameter liftData dirichlet boundary := by
  let poisson := canonicalScalarGraphPoissonOfBoundaryLift
    data traceBound spectralParameter liftData dirichlet
  let difference := field - poisson boundary
  have hDifferenceEquation :
      canonicalScalarGraphShiftedOperator data spectralParameter difference = 0 := by
    change canonicalScalarGraphShiftedOperator data spectralParameter
      (field - canonicalScalarGraphPoissonOfBoundaryLift
        data traceBound spectralParameter liftData dirichlet boundary) = 0
    rw [map_sub, hEquation,
      canonicalScalarGraphPoissonOfBoundaryLift_homogeneous,
      sub_self]
  have hDifferenceValue :
      canonicalScalarCompletedValueTrace data traceBound difference = 0 := by
    change canonicalScalarCompletedValueTrace data traceBound
      (field - canonicalScalarGraphPoissonOfBoundaryLift
        data traceBound spectralParameter liftData dirichlet boundary) = 0
    rw [map_sub, hValue,
      canonicalScalarGraphPoissonOfBoundaryLift_value_trace,
      sub_self]
  have hDifferenceDirichlet := dirichlet.unique difference 0
    hDifferenceEquation hDifferenceValue
  have hResolventZero : dirichlet.resolvent 0 = 0 := map_zero _
  rw [hResolventZero] at hDifferenceDirichlet
  have hDifferenceZero : difference = 0 := hDifferenceDirichlet
  exact sub_eq_zero.mp hDifferenceZero

/-- Complete Poisson-data package constructed from lift and Dirichlet
resolvent. -/
def canonicalScalarGraphDirichletPoissonDataOfBoundaryLift
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (liftData : CanonicalScalarGraphBoundaryValueLiftData data traceBound)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter) :
    CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter where
  poisson := canonicalScalarGraphPoissonOfBoundaryLift
    data traceBound spectralParameter liftData dirichlet
  value_trace := canonicalScalarGraphPoissonOfBoundaryLift_value_trace
    data traceBound spectralParameter liftData dirichlet
  homogeneous := canonicalScalarGraphPoissonOfBoundaryLift_homogeneous
    data traceBound spectralParameter liftData dirichlet
  unique := canonicalScalarGraphPoissonOfBoundaryLift_unique
    data traceBound spectralParameter liftData dirichlet

/-- The resulting Dirichlet-to-Neumann operator is therefore determined by a
boundary lift and the Dirichlet resolvent. -/
def canonicalScalarGraphDirichletToNeumannOfBoundaryLift
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (liftData : CanonicalScalarGraphBoundaryValueLiftData data traceBound)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter) : Trace →L[Real] Trace :=
  canonicalScalarGraphDirichletToNeumann
    data traceBound spectralParameter
      (canonicalScalarGraphDirichletPoissonDataOfBoundaryLift
        data traceBound spectralParameter liftData dirichlet)

/-- Boundary-lift construction certificate. -/
theorem canonicalScalarGraphPoissonFromDirichletResolvent_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (liftData : CanonicalScalarGraphBoundaryValueLiftData data traceBound)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter) :
    (∀ boundary : Trace,
      canonicalScalarCompletedValueTrace data traceBound
          (canonicalScalarGraphPoissonOfBoundaryLift
            data traceBound spectralParameter liftData dirichlet boundary) =
        boundary) ∧
      (∀ boundary : Trace,
        canonicalScalarGraphShiftedOperator data spectralParameter
          (canonicalScalarGraphPoissonOfBoundaryLift
            data traceBound spectralParameter liftData dirichlet boundary) = 0) ∧
      (canonicalScalarGraphDirichletToNeumannOfBoundaryLift
        data traceBound spectralParameter liftData dirichlet).toLinearMap.IsSymmetric :=
  ⟨canonicalScalarGraphPoissonOfBoundaryLift_value_trace
      data traceBound spectralParameter liftData dirichlet,
    canonicalScalarGraphPoissonOfBoundaryLift_homogeneous
      data traceBound spectralParameter liftData dirichlet,
    canonicalScalarGraphDirichletToNeumann_isSymmetric
      data traceBound spectralParameter
        (canonicalScalarGraphDirichletPoissonDataOfBoundaryLift
          data traceBound spectralParameter liftData dirichlet)⟩

end
end P0EFTJanusMappingTorusScalarGraphPoissonFromDirichletResolvent4D
end JanusFormal
