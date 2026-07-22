import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphFiniteBoundaryDeterminant4D

/-!
# Boundary Schur crossing forms

A differentiable family of symmetric boundary Schur operators carries a
canonical quadratic crossing form on the kernel at a singular parameter.  The
sign of that form is the finite-dimensional local orientation used in spectral
flow and determinant-line crossing formulas.

This file keeps differentiability, Robin symmetry and simplicity explicit.  It
relates every boundary crossing vector to the corresponding homogeneous Robin
bulk mode via the Poisson equivalence.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphBoundaryCrossingForm4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D
open P0EFTJanusMappingTorusScalarGraphBoundaryReducedAction4D
open P0EFTJanusMappingTorusScalarGraphFiniteBoundaryDeterminant4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

variable
  {data : CanonicalScalarHilbertGreenSystem
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data}
  {robin : Trace →L[Real] Trace}

/-- Differentiable symmetric family of boundary endomorphisms. -/
structure CanonicalScalarBoundaryOperatorCurve where
  operator : Real → Trace →L[Real] Trace
  derivative : Real → Trace →L[Real] Trace
  hasDerivAt_apply : ∀ (spectralParameter : Real) (boundary : Trace),
    HasDerivAt (fun parameter => operator parameter boundary)
      (derivative spectralParameter boundary) spectralParameter
  symmetric : ∀ spectralParameter,
    (operator spectralParameter).toLinearMap.IsSymmetric
  derivative_symmetric : ∀ spectralParameter,
    (derivative spectralParameter).toLinearMap.IsSymmetric

/-- Kernel crossing space at one parameter. -/
def CanonicalScalarBoundaryOperatorCurve.crossingSubmodule
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace))
    (spectralParameter : Real) : Submodule Real Trace :=
  LinearMap.ker (curve.operator spectralParameter).toLinearMap

/-- Bilinear crossing form on the kernel. -/
def CanonicalScalarBoundaryOperatorCurve.crossingPairing
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace))
    (spectralParameter : Real)
    (first second : curve.crossingSubmodule spectralParameter) : Real :=
  inner Real first.1 (curve.derivative spectralParameter second.1)

/-- Quadratic crossing form. -/
def CanonicalScalarBoundaryOperatorCurve.crossingQuadratic
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace))
    (spectralParameter : Real)
    (boundary : curve.crossingSubmodule spectralParameter) : Real :=
  curve.crossingPairing spectralParameter boundary boundary

/-- Symmetry of the crossing pairing. -/
theorem CanonicalScalarBoundaryOperatorCurve.crossingPairing_comm
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace))
    (spectralParameter : Real)
    (first second : curve.crossingSubmodule spectralParameter) :
    curve.crossingPairing spectralParameter first second =
      curve.crossingPairing spectralParameter second first := by
  unfold CanonicalScalarBoundaryOperatorCurve.crossingPairing
  calc
    inner Real first.1 (curve.derivative spectralParameter second.1) =
        inner Real (curve.derivative spectralParameter first.1) second.1 :=
      (curve.derivative_symmetric spectralParameter first.1 second.1).symm
    _ = inner Real second.1 (curve.derivative spectralParameter first.1) :=
      real_inner_comm _ _

/-- Regular crossing: the derivative pairing is nondegenerate on the crossing
kernel. -/
def CanonicalScalarBoundaryOperatorCurve.RegularCrossing
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace))
    (spectralParameter : Real) : Prop :=
  ∀ boundary : curve.crossingSubmodule spectralParameter,
    (∀ test : curve.crossingSubmodule spectralParameter,
      curve.crossingPairing spectralParameter boundary test = 0) →
    boundary = 0

/-- Positive crossing. -/
def CanonicalScalarBoundaryOperatorCurve.PositiveCrossing
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace))
    (spectralParameter : Real) : Prop :=
  ∀ boundary : curve.crossingSubmodule spectralParameter,
    boundary ≠ 0 → 0 < curve.crossingQuadratic spectralParameter boundary

/-- Negative crossing. -/
def CanonicalScalarBoundaryOperatorCurve.NegativeCrossing
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace))
    (spectralParameter : Real) : Prop :=
  ∀ boundary : curve.crossingSubmodule spectralParameter,
    boundary ≠ 0 → curve.crossingQuadratic spectralParameter boundary < 0

/-- Positive crossings are regular. -/
theorem CanonicalScalarBoundaryOperatorCurve.regularCrossing_of_positive
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace))
    (spectralParameter : Real)
    (hPositive : curve.PositiveCrossing spectralParameter) :
    curve.RegularCrossing spectralParameter := by
  intro boundary hOrthogonal
  by_contra hBoundary
  have hSelf := hOrthogonal boundary
  exact (ne_of_gt (hPositive boundary hBoundary)) hSelf

/-- Negative crossings are regular. -/
theorem CanonicalScalarBoundaryOperatorCurve.regularCrossing_of_negative
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace))
    (spectralParameter : Real)
    (hNegative : curve.NegativeCrossing spectralParameter) :
    curve.RegularCrossing spectralParameter := by
  intro boundary hOrthogonal
  by_contra hBoundary
  have hSelf := hOrthogonal boundary
  exact (ne_of_lt (hNegative boundary hBoundary)) hSelf

/-- Simple oriented crossing data. -/
structure CanonicalScalarBoundarySimpleCrossingData
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace))
    (spectralParameter : Real) where
  generator : curve.crossingSubmodule spectralParameter
  generator_ne_zero : generator ≠ 0
  spans : Submodule.span Real ({generator} : Set
    (curve.crossingSubmodule spectralParameter)) = ⊤
  crossing_ne_zero : curve.crossingQuadratic spectralParameter generator ≠ 0

/-- Orientation of a simple crossing. -/
def CanonicalScalarBoundarySimpleCrossingData.orientation
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    {spectralParameter : Real}
    (crossing : CanonicalScalarBoundarySimpleCrossingData
      curve spectralParameter) : Int :=
  if 0 < curve.crossingQuadratic spectralParameter crossing.generator then 1 else -1

/-- A simple crossing orientation is always `+1` or `-1`. -/
theorem CanonicalScalarBoundarySimpleCrossingData.orientation_eq_one_or_neg_one
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    {spectralParameter : Real}
    (crossing : CanonicalScalarBoundarySimpleCrossingData
      curve spectralParameter) :
    crossing.orientation = 1 ∨ crossing.orientation = -1 := by
  unfold CanonicalScalarBoundarySimpleCrossingData.orientation
  split_ifs <;> simp

/-- Schur-curve data for one symmetric Robin boundary family. -/
structure CanonicalScalarGraphRobinSchurCurve
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace) where
  robin_symmetric : robin.toLinearMap.IsSymmetric
  poissonData : ∀ spectralParameter : Real,
    CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter
  derivative : Real → Trace →L[Real] Trace
  hasDerivAt_apply : ∀ spectralParameter boundary,
    HasDerivAt
      (fun parameter => canonicalScalarGraphBoundarySchurOperator
        data traceBound parameter (poissonData parameter) robin boundary)
      (derivative spectralParameter boundary) spectralParameter
  derivative_symmetric : ∀ spectralParameter,
    (derivative spectralParameter).toLinearMap.IsSymmetric

/-- Boundary-operator curve underlying a Robin Schur curve. -/
noncomputable def CanonicalScalarGraphRobinSchurCurve.toBoundaryOperatorCurve
    (curve : CanonicalScalarGraphRobinSchurCurve data traceBound robin) :
    CanonicalScalarBoundaryOperatorCurve (Trace := Trace) where
  operator spectralParameter := canonicalScalarGraphBoundarySchurOperator
    data traceBound spectralParameter (curve.poissonData spectralParameter) robin
  derivative := curve.derivative
  hasDerivAt_apply := curve.hasDerivAt_apply
  symmetric spectralParameter :=
    canonicalScalarGraphBoundarySchurOperator_isSymmetric
      data traceBound spectralParameter (curve.poissonData spectralParameter)
        robin curve.robin_symmetric
  derivative_symmetric := curve.derivative_symmetric

/-- Bulk mode associated with a boundary crossing vector. -/
def canonicalScalarGraphBoundaryCrossingToBulkMode
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap →ₗ[Real]
      canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin :=
  canonicalScalarGraphSchurKernelToRobinSolution
    data traceBound spectralParameter poissonData robin

/-- Boundary crossing vectors are nonzero exactly when their Poisson bulk modes
are nonzero. -/
theorem canonicalScalarGraphBoundaryCrossingToBulkMode_ne_zero_iff
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (boundary : LinearMap.ker
      (canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin).toLinearMap) :
    canonicalScalarGraphBoundaryCrossingToBulkMode
        data traceBound spectralParameter poissonData robin boundary ≠ 0 ↔
      boundary ≠ 0 := by
  exact (canonicalScalarGraphRobinSolutionSchurKernelEquiv
    data traceBound spectralParameter poissonData robin).symm.map_ne_zero_iff

/-- Crossing-form certificate. -/
theorem canonicalScalarBoundaryCrossingForm_certificate
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace))
    (spectralParameter : Real) :
    (∀ first second : curve.crossingSubmodule spectralParameter,
      curve.crossingPairing spectralParameter first second =
        curve.crossingPairing spectralParameter second first) ∧
      (curve.PositiveCrossing spectralParameter →
        curve.RegularCrossing spectralParameter) ∧
      (curve.NegativeCrossing spectralParameter →
        curve.RegularCrossing spectralParameter) :=
  ⟨curve.crossingPairing_comm spectralParameter,
    curve.regularCrossing_of_positive spectralParameter,
    curve.regularCrossing_of_negative spectralParameter⟩

end
end P0EFTJanusMappingTorusScalarGraphBoundaryCrossingForm4D
end JanusFormal
