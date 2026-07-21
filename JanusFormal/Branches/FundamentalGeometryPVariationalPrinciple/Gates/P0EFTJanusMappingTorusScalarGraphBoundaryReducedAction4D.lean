import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D

/-!
# Reduced boundary action from the scalar Dirichlet-to-Neumann operator

For a bounded symmetric Robin operator `B`, the reduced quadratic action at a
fixed spectral parameter is

`S_B(g) = 1/2 <g, (DtN - B) g>`.

Its actual first variation is the Schur pairing with `DtN - B`; hence boundary
stationarity is equivalent to the boundary Schur equation.  Through the Poisson
operator this is exactly the homogeneous Robin bulk equation.

This is the infinite-dimensional parent-bulk reduction promised by Program P-A,
conditional only on the explicit Poisson/Green inputs.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphBoundaryReducedAction4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Reduced Robin boundary action. -/
def canonicalScalarGraphRobinReducedAction
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (boundary : Trace) : Real :=
  (1 / 2 : Real) * inner Real boundary
    (canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin boundary)

/-- The boundary Schur operator is symmetric when the Robin operator is
symmetric. -/
theorem canonicalScalarGraphBoundarySchurOperator_isSymmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    (canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin).toLinearMap.IsSymmetric := by
  intro first second
  change inner Real
      (canonicalScalarGraphDirichletToNeumann
          data traceBound spectralParameter poissonData first - robin first) second =
    inner Real first
      (canonicalScalarGraphDirichletToNeumann
          data traceBound spectralParameter poissonData second - robin second)
  calc
    _ = inner Real
          (canonicalScalarGraphDirichletToNeumann
            data traceBound spectralParameter poissonData first) second -
        inner Real (robin first) second := inner_sub_left _ _ _
    _ = inner Real first
          (canonicalScalarGraphDirichletToNeumann
            data traceBound spectralParameter poissonData second) -
        inner Real first (robin second) := congrArg₂ (· - ·)
          (canonicalScalarGraphDirichletToNeumann_isSymmetric
            data traceBound spectralParameter poissonData first second)
          (hRobin first second)
    _ = _ := (inner_sub_right first
      (canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData second)
      (robin second)).symm

/-- Exact affine Taylor formula for the reduced Robin action. -/
theorem canonicalScalarGraphRobinReducedAction_affine
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (boundary variation : Trace) (parameter : Real) :
    canonicalScalarGraphRobinReducedAction
        data traceBound spectralParameter poissonData robin
        (boundary + parameter • variation) =
      canonicalScalarGraphRobinReducedAction
          data traceBound spectralParameter poissonData robin boundary +
        parameter * inner Real variation
          (canonicalScalarGraphBoundarySchurOperator
            data traceBound spectralParameter poissonData robin boundary) +
        parameter ^ 2 *
          canonicalScalarGraphRobinReducedAction
            data traceBound spectralParameter poissonData robin variation := by
  unfold canonicalScalarGraphRobinReducedAction
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  have hCross : inner Real boundary
      (canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin variation) =
      inner Real variation
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin boundary) := by
    rw [real_inner_comm]
    exact canonicalScalarGraphBoundarySchurOperator_isSymmetric
      data traceBound spectralParameter poissonData robin hRobin
        variation boundary
  rw [hCross]
  ring

/-- First derivative of the reduced Robin action. -/
theorem canonicalScalarGraphRobinReducedAction_hasDerivAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (boundary variation : Trace) :
    @HasDerivAt Real _ Real
      Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun parameter : Real =>
        canonicalScalarGraphRobinReducedAction
          data traceBound spectralParameter poissonData robin
          (boundary + parameter • variation))
      (inner Real variation
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin boundary)) 0 := by
  have hPolynomial := (((hasDerivAt_const (x := (0 : Real))
      (canonicalScalarGraphRobinReducedAction
        data traceBound spectralParameter poissonData robin boundary)).add
      ((hasDerivAt_id (0 : Real)).mul_const
        (inner Real variation
          (canonicalScalarGraphBoundarySchurOperator
            data traceBound spectralParameter poissonData robin boundary)))).add
      (((hasDerivAt_id (0 : Real)).pow 2).mul_const
        (canonicalScalarGraphRobinReducedAction
          data traceBound spectralParameter poissonData robin variation)))
  norm_num at hPolynomial
  apply hPolynomial.congr_of_eventuallyEq
  filter_upwards [] with parameter
  exact canonicalScalarGraphRobinReducedAction_affine
    data traceBound spectralParameter poissonData robin hRobin
      boundary variation parameter

/-- Boundary stationarity predicate. -/
def CanonicalScalarGraphRobinBoundaryStationary
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (boundary : Trace) : Prop :=
  ∀ variation : Trace,
    inner Real variation
      (canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin boundary) = 0

/-- Stationarity is equivalent to the Schur equation. -/
theorem canonicalScalarGraphRobinBoundaryStationary_iff_schur_zero
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (boundary : Trace) :
    CanonicalScalarGraphRobinBoundaryStationary
        data traceBound spectralParameter poissonData robin boundary ↔
      canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin boundary = 0 := by
  constructor
  · intro hStationary
    let residual := canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin boundary
    have hSelf : inner Real residual residual = 0 := hStationary residual
    have hNormSq : ‖residual‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq residual]
      exact hSelf
    have hNorm : ‖residual‖ = 0 := by
      nlinarith [sq_nonneg ‖residual‖]
    exact norm_eq_zero.mp hNorm
  · intro hZero variation
    rw [hZero]
    simp

/-- Stationarity is exactly membership in the boundary Schur kernel. -/
theorem canonicalScalarGraphRobinBoundaryStationary_iff_mem_kernel
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (boundary : Trace) :
    CanonicalScalarGraphRobinBoundaryStationary
        data traceBound spectralParameter poissonData robin boundary ↔
      boundary ∈ LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap := by
  rw [canonicalScalarGraphRobinBoundaryStationary_iff_schur_zero,
    LinearMap.mem_ker]
  rfl

/-- Boundary stationarity is equivalent to the Poisson solution satisfying the
homogeneous Robin bulk problem. -/
theorem canonicalScalarGraphRobinBoundaryStationary_iff_bulk_solution
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (boundary : Trace) :
    CanonicalScalarGraphRobinBoundaryStationary
        data traceBound spectralParameter poissonData robin boundary ↔
      poissonData.poisson boundary ∈
        canonicalScalarGraphRobinHomogeneousSolutionSubmodule
          data traceBound spectralParameter robin := by
  rw [canonicalScalarGraphRobinBoundaryStationary_iff_schur_zero]
  constructor
  · intro hSchur
    refine ⟨poissonData.homogeneous boundary, ?_⟩
    have hEq := sub_eq_zero.mp hSchur
    rw [poissonData.value_trace]
    exact hEq
  · intro hBulk
    have hBoundary := hBulk.2
    rw [poissonData.value_trace] at hBoundary
    exact sub_eq_zero.mpr hBoundary

/-- A nonzero stationary boundary value gives a nonzero Robin bulk mode. -/
theorem canonicalScalarGraphRobinBoundaryStationary_nonzero_bulk
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (boundary : Trace)
    (hBoundary : boundary ≠ 0)
    (hStationary : CanonicalScalarGraphRobinBoundaryStationary
      data traceBound spectralParameter poissonData robin boundary) :
    ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0 := by
  refine ⟨⟨poissonData.poisson boundary,
    (canonicalScalarGraphRobinBoundaryStationary_iff_bulk_solution
      data traceBound spectralParameter poissonData robin boundary).1 hStationary⟩, ?_⟩
  intro hZero
  apply hBoundary
  have hValue := congrArg
    (canonicalScalarCompletedValueTrace data traceBound) (congrArg Subtype.val hZero)
  simpa [poissonData.value_trace boundary] using hValue

/-- Reduced-action/Schur/bulk certificate. -/
theorem canonicalScalarGraphBoundaryReducedAction_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (boundary : Trace) :
    (CanonicalScalarGraphRobinBoundaryStationary
        data traceBound spectralParameter poissonData robin boundary ↔
      canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin boundary = 0) ∧
      (CanonicalScalarGraphRobinBoundaryStationary
        data traceBound spectralParameter poissonData robin boundary ↔
      poissonData.poisson boundary ∈
        canonicalScalarGraphRobinHomogeneousSolutionSubmodule
          data traceBound spectralParameter robin) ∧
      (∀ variation : Trace,
        HasDerivAt
          (fun parameter : Real =>
            canonicalScalarGraphRobinReducedAction
              data traceBound spectralParameter poissonData robin
              (boundary + parameter • variation))
          (inner Real variation
            (canonicalScalarGraphBoundarySchurOperator
              data traceBound spectralParameter poissonData robin boundary)) 0) :=
  ⟨canonicalScalarGraphRobinBoundaryStationary_iff_schur_zero
      data traceBound spectralParameter poissonData robin boundary,
    canonicalScalarGraphRobinBoundaryStationary_iff_bulk_solution
      data traceBound spectralParameter poissonData robin boundary,
    canonicalScalarGraphRobinReducedAction_hasDerivAt
      data traceBound spectralParameter poissonData robin hRobin boundary⟩

end
end P0EFTJanusMappingTorusScalarGraphBoundaryReducedAction4D
end JanusFormal
