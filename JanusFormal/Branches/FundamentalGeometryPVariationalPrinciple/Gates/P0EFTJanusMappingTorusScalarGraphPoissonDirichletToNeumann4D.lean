import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarHilbertGreenSystem4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertRobinGraph4D

/-!
# Poisson and Dirichlet-to-Neumann operators on the completed scalar graph

The completed scalar graph carries continuous value and normal traces and the
exact Green identity.  This file adds the standard boundary-value input at one
real spectral parameter: a continuous Poisson operator solving the homogeneous
shifted equation with prescribed value trace.

From that input it constructs the continuous Dirichlet-to-Neumann operator,
proves its symmetry, identifies its Cauchy-data graph as a closed Lagrangian
subspace, and derives the exact reduced quadratic boundary action.  A symmetric
Robin operator enters through the boundary Schur complement `DtN - B`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarHilbertRobinGraph4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Shifted relation on the completed graph. -/
def canonicalScalarGraphShiftedOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (spectralParameter : Real) :
    CanonicalScalarOperatorGraphSpace data →L[Real] Ambient :=
  canonicalScalarOperatorGraphOperator data -
    spectralParameter • canonicalScalarOperatorGraphInclusion data

@[simp] theorem canonicalScalarGraphShiftedOperator_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (spectralParameter : Real)
    (field : CanonicalScalarOperatorGraphSpace data) :
    canonicalScalarGraphShiftedOperator data spectralParameter field =
      canonicalScalarOperatorGraphOperator data field -
        spectralParameter • canonicalScalarOperatorGraphInclusion data field :=
  rfl

/-- Continuous Poisson solution operator at one spectral parameter. -/
structure CanonicalScalarGraphDirichletPoissonData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real) where
  poisson : Trace →L[Real] CanonicalScalarOperatorGraphSpace data
  value_trace : ∀ boundary : Trace,
    canonicalScalarCompletedValueTrace data traceBound (poisson boundary) = boundary
  homogeneous : ∀ boundary : Trace,
    canonicalScalarGraphShiftedOperator data spectralParameter
      (poisson boundary) = 0
  unique : ∀ (field : CanonicalScalarOperatorGraphSpace data) (boundary : Trace),
    canonicalScalarCompletedValueTrace data traceBound field = boundary →
    canonicalScalarGraphShiftedOperator data spectralParameter field = 0 →
    field = poisson boundary

/-- Dirichlet-to-Neumann operator at the chosen spectral parameter. -/
def canonicalScalarGraphDirichletToNeumann
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) : Trace →L[Real] Trace :=
  (canonicalScalarCompletedNormalTrace data traceBound).comp poissonData.poisson

@[simp] theorem canonicalScalarGraphDirichletToNeumann_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (boundary : Trace) :
    canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData boundary =
      canonicalScalarCompletedNormalTrace data traceBound
        (poissonData.poisson boundary) :=
  rfl

/-- Every homogeneous graph solution is reconstructed by the Poisson operator
from its value trace. -/
theorem CanonicalScalarGraphDirichletPoissonData.reconstruct
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (field : CanonicalScalarOperatorGraphSpace data)
    (hField : canonicalScalarGraphShiftedOperator
      data spectralParameter field = 0) :
    field = poissonData.poisson
      (canonicalScalarCompletedValueTrace data traceBound field) :=
  poissonData.unique field _ rfl hField

/-- The Dirichlet-to-Neumann operator is symmetric by the completed Green
identity. -/
theorem canonicalScalarGraphDirichletToNeumann_isSymmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    (canonicalScalarGraphDirichletToNeumann
      data traceBound spectralParameter poissonData).toLinearMap.IsSymmetric := by
  intro first second
  have hGreen := canonicalScalarCompletedGreenIdentity data traceBound
    (poissonData.poisson first) (poissonData.poisson second)
  have hFirstEquation := poissonData.homogeneous first
  have hSecondEquation := poissonData.homogeneous second
  have hFirstOperator :
      canonicalScalarOperatorGraphOperator data (poissonData.poisson first) =
        spectralParameter • canonicalScalarOperatorGraphInclusion data
          (poissonData.poisson first) := by
    exact sub_eq_zero.mp (by
      simpa [canonicalScalarGraphShiftedOperator_apply] using hFirstEquation)
  have hSecondOperator :
      canonicalScalarOperatorGraphOperator data (poissonData.poisson second) =
        spectralParameter • canonicalScalarOperatorGraphInclusion data
          (poissonData.poisson second) := by
    exact sub_eq_zero.mp (by
      simpa [canonicalScalarGraphShiftedOperator_apply] using hSecondEquation)
  rw [hFirstOperator, hSecondOperator,
    real_inner_smul_left, real_inner_smul_right] at hGreen
  unfold canonicalScalarCompletedBoundaryGreenPairing at hGreen
  rw [poissonData.value_trace first, poissonData.value_trace second] at hGreen
  change spectralParameter * inner Real
          (canonicalScalarOperatorGraphInclusion data (poissonData.poisson first))
          (canonicalScalarOperatorGraphInclusion data (poissonData.poisson second)) -
      spectralParameter * inner Real
          (canonicalScalarOperatorGraphInclusion data (poissonData.poisson first))
          (canonicalScalarOperatorGraphInclusion data (poissonData.poisson second)) =
    2 * (inner Real first
        (canonicalScalarGraphDirichletToNeumann
          data traceBound spectralParameter poissonData second) -
      inner Real
        (canonicalScalarGraphDirichletToNeumann
          data traceBound spectralParameter poissonData first) second) at hGreen
  have hZero :
      inner Real first
          (canonicalScalarGraphDirichletToNeumann
            data traceBound spectralParameter poissonData second) -
        inner Real
          (canonicalScalarGraphDirichletToNeumann
            data traceBound spectralParameter poissonData first) second = 0 := by
    linarith
  have hComm := real_inner_comm
    (canonicalScalarGraphDirichletToNeumann
      data traceBound spectralParameter poissonData first) second
  linarith

/-- Cauchy-data graph of homogeneous solutions. -/
def canonicalScalarGraphCauchyDataSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    Submodule Real (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :=
  canonicalScalarHilbertRobinGraphSubmodule
    (canonicalScalarGraphDirichletToNeumann
      data traceBound spectralParameter poissonData)

/-- The Cauchy-data space is a closed Lagrangian boundary subspace. -/
theorem canonicalScalarGraphCauchyDataSubmodule_closed_lagrangian
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    IsClosed
        (canonicalScalarGraphCauchyDataSubmodule
          data traceBound spectralParameter poissonData :
            Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))) ∧
      canonicalScalarHilbertBoundarySymplecticOrthogonal
          (canonicalScalarGraphCauchyDataSubmodule
            data traceBound spectralParameter poissonData) =
        canonicalScalarGraphCauchyDataSubmodule
          data traceBound spectralParameter poissonData :=
  canonicalScalarHilbertRobinGraph_certificate
    (canonicalScalarGraphDirichletToNeumann
      data traceBound spectralParameter poissonData)
    (canonicalScalarGraphDirichletToNeumann_isSymmetric
      data traceBound spectralParameter poissonData)

/-- Boundary Schur complement for a bounded Robin operator. -/
def canonicalScalarGraphBoundarySchurOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) : Trace →L[Real] Trace :=
  canonicalScalarGraphDirichletToNeumann
      data traceBound spectralParameter poissonData - robin

@[simp] theorem canonicalScalarGraphBoundarySchurOperator_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) (boundary : Trace) :
    canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin boundary =
      canonicalScalarGraphDirichletToNeumann
          data traceBound spectralParameter poissonData boundary -
        robin boundary :=
  rfl

/-- A Poisson solution satisfies the Robin boundary law exactly when its
boundary value lies in the kernel of the Schur operator. -/
theorem canonicalScalarGraph_poisson_satisfies_robin_iff
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) (boundary : Trace) :
    canonicalScalarCompletedNormalTrace data traceBound
          (poissonData.poisson boundary) = robin boundary ↔
      boundary ∈ LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap := by
  rw [LinearMap.mem_ker]
  change canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData boundary = robin boundary ↔
    canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData boundary - robin boundary = 0
  exact eq_comm.trans sub_eq_zero.symm

/-- Reduced on-shell Dirichlet action. -/
def canonicalScalarGraphDirichletOnShellAction
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (boundary : Trace) : Real :=
  (1 / 2 : Real) * inner Real boundary
    (canonicalScalarGraphDirichletToNeumann
      data traceBound spectralParameter poissonData boundary)

/-- Exact affine Taylor formula for the reduced on-shell action. -/
theorem canonicalScalarGraphDirichletOnShellAction_affine
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (boundary variation : Trace) (parameter : Real) :
    canonicalScalarGraphDirichletOnShellAction
        data traceBound spectralParameter poissonData
        (boundary + parameter • variation) =
      canonicalScalarGraphDirichletOnShellAction
          data traceBound spectralParameter poissonData boundary +
        parameter * inner Real variation
          (canonicalScalarGraphDirichletToNeumann
            data traceBound spectralParameter poissonData boundary) +
        parameter ^ 2 *
          canonicalScalarGraphDirichletOnShellAction
            data traceBound spectralParameter poissonData variation := by
  unfold canonicalScalarGraphDirichletOnShellAction
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [canonicalScalarGraphDirichletToNeumann_isSymmetric
    data traceBound spectralParameter poissonData boundary variation]
  ring

/-- First variation of the reduced on-shell action is the Dirichlet-to-Neumann
pairing. -/
theorem canonicalScalarGraphDirichletOnShellAction_hasDerivAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (boundary variation : Trace) :
    HasDerivAt
      (fun parameter : Real =>
        canonicalScalarGraphDirichletOnShellAction
          data traceBound spectralParameter poissonData
          (boundary + parameter • variation))
      (inner Real variation
        (canonicalScalarGraphDirichletToNeumann
          data traceBound spectralParameter poissonData boundary)) 0 := by
  rw [show (fun parameter : Real =>
      canonicalScalarGraphDirichletOnShellAction
        data traceBound spectralParameter poissonData
        (boundary + parameter • variation)) =
    (fun parameter : Real =>
      canonicalScalarGraphDirichletOnShellAction
          data traceBound spectralParameter poissonData boundary +
        parameter * inner Real variation
          (canonicalScalarGraphDirichletToNeumann
            data traceBound spectralParameter poissonData boundary) +
        parameter ^ 2 *
          canonicalScalarGraphDirichletOnShellAction
            data traceBound spectralParameter poissonData variation) from by
      funext parameter
      exact canonicalScalarGraphDirichletOnShellAction_affine
        data traceBound spectralParameter poissonData
          boundary variation parameter]
  convert (((hasDerivAt_const (x := (0 : Real))
      (canonicalScalarGraphDirichletOnShellAction
        data traceBound spectralParameter poissonData boundary)).add
      ((hasDerivAt_id (0 : Real)).mul_const
        (inner Real variation
          (canonicalScalarGraphDirichletToNeumann
            data traceBound spectralParameter poissonData boundary)))).add
      (((hasDerivAt_id (0 : Real)).pow 2).mul_const
        (canonicalScalarGraphDirichletOnShellAction
          data traceBound spectralParameter poissonData variation))) using 1 <;> norm_num

/-- Poisson/DtN closure certificate. -/
theorem canonicalScalarGraphPoissonDirichletToNeumann_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    (canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData).toLinearMap.IsSymmetric ∧
      IsClosed
        (canonicalScalarGraphCauchyDataSubmodule
          data traceBound spectralParameter poissonData :
            Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))) ∧
      canonicalScalarHilbertBoundarySymplecticOrthogonal
          (canonicalScalarGraphCauchyDataSubmodule
            data traceBound spectralParameter poissonData) =
        canonicalScalarGraphCauchyDataSubmodule
          data traceBound spectralParameter poissonData :=
  ⟨canonicalScalarGraphDirichletToNeumann_isSymmetric
      data traceBound spectralParameter poissonData,
    (canonicalScalarGraphCauchyDataSubmodule_closed_lagrangian
      data traceBound spectralParameter poissonData).1,
    (canonicalScalarGraphCauchyDataSubmodule_closed_lagrangian
      data traceBound spectralParameter poissonData).2⟩

end
end P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
end JanusFormal
