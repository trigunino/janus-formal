import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryReducedAction4D

/-!
# Coercive reduced scalar boundary action

For a symmetric boundary Schur operator `S = DtN - B`, the sourced reduced
boundary action is

`A_q(g) = 1/2 <g,Sg> - <q,g>`.

This file proves its exact first variation, stationarity equation `Sg=q`, and
unique global minimization under a positive Schur lower bound.  A bounded
Schur inverse gives the explicit minimizer.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphBoundaryCoerciveAction4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphBoundaryReducedAction4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Positive lower bound for one boundary Schur operator. -/
structure CanonicalScalarGraphBoundarySchurCoerciveData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) where
  robin_symmetric : robin.toLinearMap.IsSymmetric
  constant : Real
  constant_pos : 0 < constant
  lower_bound : ∀ boundary : Trace,
    constant * ‖boundary‖ ^ 2 ≤
      inner Real boundary
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin boundary)

/-- Sourced reduced boundary action. -/
def canonicalScalarGraphBoundarySourceAction
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (source boundary : Trace) : Real :=
  canonicalScalarGraphRobinReducedAction
      data traceBound spectralParameter poissonData robin boundary -
    inner Real source boundary

/-- Exact affine Taylor formula for the sourced boundary action. -/
theorem canonicalScalarGraphBoundarySourceAction_affine
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (source boundary variation : Trace) (parameter : Real) :
    canonicalScalarGraphBoundarySourceAction
        data traceBound spectralParameter poissonData robin source
        (boundary + parameter • variation) =
      canonicalScalarGraphBoundarySourceAction
          data traceBound spectralParameter poissonData robin source boundary +
        parameter * inner Real variation
          (canonicalScalarGraphBoundarySchurOperator
              data traceBound spectralParameter poissonData robin boundary - source) +
        parameter ^ 2 *
          canonicalScalarGraphRobinReducedAction
            data traceBound spectralParameter poissonData robin variation := by
  unfold canonicalScalarGraphBoundarySourceAction
  rw [canonicalScalarGraphRobinReducedAction_affine
    data traceBound spectralParameter poissonData robin hRobin]
  simp only [inner_add_right, real_inner_smul_right, inner_sub_right]
  rw [real_inner_comm source variation]
  ring

/-- First variation of the sourced boundary action. -/
theorem canonicalScalarGraphBoundarySourceAction_hasDerivAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (source boundary variation : Trace) :
    HasDerivAt
      (fun parameter : Real =>
        canonicalScalarGraphBoundarySourceAction
          data traceBound spectralParameter poissonData robin source
          (boundary + parameter • variation))
      (inner Real variation
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin boundary - source)) 0 := by
  rw [show (fun parameter : Real =>
      canonicalScalarGraphBoundarySourceAction
        data traceBound spectralParameter poissonData robin source
        (boundary + parameter • variation)) =
    (fun parameter : Real =>
      canonicalScalarGraphBoundarySourceAction
          data traceBound spectralParameter poissonData robin source boundary +
        parameter * inner Real variation
          (canonicalScalarGraphBoundarySchurOperator
              data traceBound spectralParameter poissonData robin boundary - source) +
        parameter ^ 2 *
          canonicalScalarGraphRobinReducedAction
            data traceBound spectralParameter poissonData robin variation) from by
      funext parameter
      exact canonicalScalarGraphBoundarySourceAction_affine
        data traceBound spectralParameter poissonData robin hRobin
          source boundary variation parameter]
  convert (((hasDerivAt_const (x := (0 : Real))
      (canonicalScalarGraphBoundarySourceAction
        data traceBound spectralParameter poissonData robin source boundary)).add
      ((hasDerivAt_id (0 : Real)).mul_const
        (inner Real variation
          (canonicalScalarGraphBoundarySchurOperator
            data traceBound spectralParameter poissonData robin boundary - source)))).add
      (((hasDerivAt_id (0 : Real)).pow 2).mul_const
        (canonicalScalarGraphRobinReducedAction
          data traceBound spectralParameter poissonData robin variation))) using 1 <;> norm_num

/-- Weak stationarity of the sourced boundary action. -/
def CanonicalScalarGraphBoundarySourceStationary
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (source boundary : Trace) : Prop :=
  ∀ variation : Trace,
    inner Real variation
      (canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin boundary - source) = 0

/-- Boundary stationarity is exactly the sourced Schur equation. -/
theorem canonicalScalarGraphBoundarySourceStationary_iff_equation
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (source boundary : Trace) :
    CanonicalScalarGraphBoundarySourceStationary
        data traceBound spectralParameter poissonData robin source boundary ↔
      canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin boundary = source := by
  constructor
  · intro hStationary
    let residual := canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin boundary - source
    have hSelf : inner Real residual residual = 0 := hStationary residual
    have hNorm : ‖residual‖ = 0 := by
      rw [← sq_eq_zero_iff]
      simpa [real_inner_self_eq_norm_sq] using hSelf
    exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)
  · intro hEquation variation
    rw [hEquation, sub_self]
    simp

/-- Energy difference from a sourced Schur solution. -/
theorem canonicalScalarGraphBoundarySourceAction_sub_solution
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (source solution boundary : Trace)
    (hSolution : canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin solution = source) :
    canonicalScalarGraphBoundarySourceAction
          data traceBound spectralParameter poissonData robin source boundary -
        canonicalScalarGraphBoundarySourceAction
          data traceBound spectralParameter poissonData robin source solution =
      canonicalScalarGraphRobinReducedAction
        data traceBound spectralParameter poissonData robin (boundary - solution) := by
  let displacement := boundary - solution
  have hBoundary : boundary = solution + displacement := by
    dsimp [displacement]
    module
  rw [hBoundary,
    canonicalScalarGraphBoundarySourceAction_affine
      data traceBound spectralParameter poissonData robin hRobin
        source solution displacement 1,
    hSolution, sub_self]
  ring

/-- Coercivity makes a sourced Schur solution the unique global minimizer. -/
theorem canonicalScalarGraphBoundarySourceAction_unique_minimizer
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveData
      data traceBound spectralParameter poissonData robin)
    (source solution : Trace)
    (hSolution : canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin solution = source) :
    (∀ boundary : Trace,
      canonicalScalarGraphBoundarySourceAction
          data traceBound spectralParameter poissonData robin source solution ≤
        canonicalScalarGraphBoundarySourceAction
          data traceBound spectralParameter poissonData robin source boundary) ∧
      (∀ boundary : Trace,
        canonicalScalarGraphBoundarySourceAction
            data traceBound spectralParameter poissonData robin source boundary =
          canonicalScalarGraphBoundarySourceAction
            data traceBound spectralParameter poissonData robin source solution →
        boundary = solution) := by
  constructor
  · intro boundary
    have hDifference := canonicalScalarGraphBoundarySourceAction_sub_solution
      data traceBound spectralParameter poissonData robin
        coercive.robin_symmetric source solution boundary hSolution
    have hBound := coercive.lower_bound (boundary - solution)
    unfold canonicalScalarGraphRobinReducedAction at hDifference
    linarith [sq_nonneg ‖boundary - solution‖]
  · intro boundary hEqual
    have hDifference := canonicalScalarGraphBoundarySourceAction_sub_solution
      data traceBound spectralParameter poissonData robin
        coercive.robin_symmetric source solution boundary hSolution
    rw [hEqual, sub_self] at hDifference
    have hBound := coercive.lower_bound (boundary - solution)
    unfold canonicalScalarGraphRobinReducedAction at hDifference
    have hNorm : ‖boundary - solution‖ = 0 := by
      nlinarith [sq_nonneg ‖boundary - solution‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Explicit bounded inverse for a sourced boundary Schur equation. -/
structure CanonicalScalarGraphBoundarySchurBoundedInverseData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) where
  inverse : Trace →L[Real] Trace
  left_inverse : ∀ source,
    canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin (inverse source) = source
  right_inverse : ∀ boundary,
    inverse (canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin boundary) = boundary

/-- Bounded inverse gives the explicit sourced stationary boundary. -/
theorem CanonicalScalarGraphBoundarySchurBoundedInverseData.solution
    (inverseData : CanonicalScalarGraphBoundarySchurBoundedInverseData
      data traceBound spectralParameter poissonData robin)
    (source : Trace) :
    canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin
        (inverseData.inverse source) = source :=
  inverseData.left_inverse source

/-- Coercive boundary action certificate. -/
theorem canonicalScalarGraphBoundaryCoerciveAction_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (coercive : CanonicalScalarGraphBoundarySchurCoerciveData
      data traceBound spectralParameter poissonData robin)
    (inverseData : CanonicalScalarGraphBoundarySchurBoundedInverseData
      data traceBound spectralParameter poissonData robin)
    (source : Trace) :
    let solution := inverseData.inverse source
    CanonicalScalarGraphBoundarySourceStationary
        data traceBound spectralParameter poissonData robin source solution ∧
      (∀ boundary : Trace,
        canonicalScalarGraphBoundarySourceAction
            data traceBound spectralParameter poissonData robin source solution ≤
          canonicalScalarGraphBoundarySourceAction
            data traceBound spectralParameter poissonData robin source boundary) ∧
      (∀ boundary : Trace,
        canonicalScalarGraphBoundarySourceAction
            data traceBound spectralParameter poissonData robin source boundary =
          canonicalScalarGraphBoundarySourceAction
            data traceBound spectralParameter poissonData robin source solution →
        boundary = solution) := by
  dsimp
  have hSolution := inverseData.left_inverse source
  exact ⟨(canonicalScalarGraphBoundarySourceStationary_iff_equation
      data traceBound spectralParameter poissonData robin source
        (inverseData.inverse source)).2 hSolution,
    (canonicalScalarGraphBoundarySourceAction_unique_minimizer
      data traceBound spectralParameter poissonData robin coercive
        source (inverseData.inverse source) hSolution).1,
    (canonicalScalarGraphBoundarySourceAction_unique_minimizer
      data traceBound spectralParameter poissonData robin coercive
        source (inverseData.inverse source) hSolution).2⟩

end
end P0EFTJanusMappingTorusScalarGraphBoundaryCoerciveAction4D
end JanusFormal
