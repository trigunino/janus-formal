import Mathlib.LinearAlgebra.Determinant
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphInterfaceCoerciveGluing4D

/-!
# Finite Galerkin reduction of scalar boundary Schur operators

For an infinite-dimensional Hilbert trace space, choose a finite-dimensional
coefficient space with an isometric embedding and an adjoint projection.  The
Galerkin reduction of a boundary operator `S` is

`S_N = project ∘ S ∘ embed`.

Symmetry is preserved.  For a Robin Schur operator, a coefficient kernel vector
lifts by the Poisson map to a homogeneous bulk field whose boundary residual is
orthogonal to the Galerkin test space.  The finite determinant detects exactly
such nonzero projected modes.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphBoundaryGalerkin4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D

universe u v w z

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  {Coefficient : Type z}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  [NormedAddCommGroup Coefficient] [InnerProductSpace Real Coefficient]
  [CompleteSpace Coefficient]
  [FiniteDimensional Real Coefficient]

/-- Finite boundary Galerkin trial/test space. -/
structure CanonicalScalarBoundaryGalerkinData where
  embed : Coefficient →L[Real] Trace
  project : Trace →L[Real] Coefficient
  project_embed : ∀ coefficient,
    project (embed coefficient) = coefficient
  adjoint : ∀ coefficient boundary,
    inner Real (embed coefficient) boundary =
      inner Real coefficient (project boundary)

namespace CanonicalScalarBoundaryGalerkinData

/-- Galerkin reduction of a bounded trace operator. -/
def reduce
    (galerkin : CanonicalScalarBoundaryGalerkinData
      (Trace := Trace) (Coefficient := Coefficient))
    (operator : Trace →L[Real] Trace) :
    Coefficient →L[Real] Coefficient :=
  galerkin.project.comp (operator.comp galerkin.embed)

@[simp] theorem reduce_apply
    (galerkin : CanonicalScalarBoundaryGalerkinData
      (Trace := Trace) (Coefficient := Coefficient))
    (operator : Trace →L[Real] Trace)
    (coefficient : Coefficient) :
    galerkin.reduce operator coefficient =
      galerkin.project (operator (galerkin.embed coefficient)) :=
  rfl

/-- The embedding is injective. -/
theorem embed_injective
    (galerkin : CanonicalScalarBoundaryGalerkinData
      (Trace := Trace) (Coefficient := Coefficient)) :
    Function.Injective galerkin.embed := by
  intro first second hEqual
  rw [← galerkin.project_embed first,
    ← galerkin.project_embed second, hEqual]

/-- The projection is surjective. -/
theorem project_surjective
    (galerkin : CanonicalScalarBoundaryGalerkinData
      (Trace := Trace) (Coefficient := Coefficient)) :
    Function.Surjective galerkin.project := by
  intro coefficient
  exact ⟨galerkin.embed coefficient, galerkin.project_embed coefficient⟩

/-- Galerkin reduction preserves symmetry. -/
theorem reduce_isSymmetric
    (galerkin : CanonicalScalarBoundaryGalerkinData
      (Trace := Trace) (Coefficient := Coefficient))
    (operator : Trace →L[Real] Trace)
    (hOperator : operator.toLinearMap.IsSymmetric) :
    (galerkin.reduce operator).toLinearMap.IsSymmetric := by
  intro first second
  rw [← galerkin.adjoint first (operator (galerkin.embed second)),
    ← galerkin.adjoint second (operator (galerkin.embed first)),
    hOperator (galerkin.embed first) (galerkin.embed second)]

/-- Projected Robin boundary Schur operator. -/
def schur
    (galerkin : CanonicalScalarBoundaryGalerkinData
      (Trace := Trace) (Coefficient := Coefficient))
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    Coefficient →L[Real] Coefficient :=
  galerkin.reduce
    (canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin)

/-- Symmetry of the projected Schur operator. -/
theorem schur_isSymmetric
    (galerkin : CanonicalScalarBoundaryGalerkinData
      (Trace := Trace) (Coefficient := Coefficient))
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    (galerkin.schur data traceBound spectralParameter poissonData robin).toLinearMap.IsSymmetric :=
  galerkin.reduce_isSymmetric _
    (canonicalScalarGraphBoundarySchurOperator_isSymmetric
      data traceBound spectralParameter poissonData robin hRobin)

/-- Finite Galerkin Schur determinant. -/
noncomputable def schurDeterminant
    (galerkin : CanonicalScalarBoundaryGalerkinData
      (Trace := Trace) (Coefficient := Coefficient))
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) : Real :=
  LinearMap.det
    (galerkin.schur data traceBound spectralParameter poissonData robin).toLinearMap

/-- Galerkin determinant zero iff projected Schur kernel is nontrivial. -/
theorem schurDeterminant_eq_zero_iff
    (galerkin : CanonicalScalarBoundaryGalerkinData
      (Trace := Trace) (Coefficient := Coefficient))
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    galerkin.schurDeterminant data traceBound spectralParameter
        poissonData robin = 0 ↔
      LinearMap.ker
        (galerkin.schur data traceBound spectralParameter
          poissonData robin).toLinearMap ≠ ⊥ :=
  LinearMap.det_eq_zero_iff_ker_ne_bot

/-- Galerkin homogeneous Robin trial mode.  The bulk equation is exact and the
Robin residual is orthogonal to the finite test space. -/
structure CanonicalScalarGraphGalerkinRobinMode
    (galerkin : CanonicalScalarBoundaryGalerkinData
      (Trace := Trace) (Coefficient := Coefficient))
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) where
  coefficient : Coefficient
  coefficient_ne_zero : coefficient ≠ 0
  projectedEquation :
    galerkin.schur data traceBound spectralParameter poissonData robin
      coefficient = 0

namespace CanonicalScalarGraphGalerkinRobinMode

/-- Embedded boundary trial value. -/
def boundary
    (mode : CanonicalScalarGraphGalerkinRobinMode galerkin data traceBound
      spectralParameter poissonData robin) : Trace :=
  galerkin.embed mode.coefficient

/-- Poisson bulk trial field. -/
def field
    (mode : CanonicalScalarGraphGalerkinRobinMode galerkin data traceBound
      spectralParameter poissonData robin) :
    CanonicalScalarOperatorGraphSpace data :=
  poissonData.poisson mode.boundary

/-- Galerkin trial field solves the bulk homogeneous equation exactly. -/
theorem homogeneous
    (mode : CanonicalScalarGraphGalerkinRobinMode galerkin data traceBound
      spectralParameter poissonData robin) :
    canonicalScalarGraphShiftedOperator data spectralParameter mode.field = 0 :=
  poissonData.homogeneous mode.boundary

/-- Galerkin trial field has the embedded boundary value. -/
theorem value_trace
    (mode : CanonicalScalarGraphGalerkinRobinMode galerkin data traceBound
      spectralParameter poissonData robin) :
    canonicalScalarCompletedValueTrace data traceBound mode.field =
      mode.boundary :=
  poissonData.value_trace mode.boundary

/-- Robin residual is orthogonal to every embedded Galerkin test vector. -/
theorem residual_orthogonal
    (mode : CanonicalScalarGraphGalerkinRobinMode galerkin data traceBound
      spectralParameter poissonData robin)
    (test : Coefficient) :
    inner Real (galerkin.embed test)
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin mode.boundary) = 0 := by
  rw [galerkin.adjoint]
  change inner Real test
    (galerkin.schur data traceBound spectralParameter poissonData robin
      mode.coefficient) = 0
  rw [mode.projectedEquation]
  simp

/-- A nonzero Galerkin coefficient gives a nonzero embedded boundary. -/
theorem boundary_ne_zero
    (mode : CanonicalScalarGraphGalerkinRobinMode galerkin data traceBound
      spectralParameter poissonData robin) :
    mode.boundary ≠ 0 := by
  intro hZero
  apply mode.coefficient_ne_zero
  exact galerkin.embed_injective (by simpa using hZero)

/-- A nonzero Galerkin boundary gives a nonzero Poisson field. -/
theorem field_ne_zero
    (mode : CanonicalScalarGraphGalerkinRobinMode galerkin data traceBound
      spectralParameter poissonData robin) :
    mode.field ≠ 0 := by
  intro hZero
  apply mode.boundary_ne_zero
  have hValue := congrArg
    (canonicalScalarCompletedValueTrace data traceBound) hZero
  simpa [mode.value_trace] using hValue

end CanonicalScalarGraphGalerkinRobinMode

/-- Determinant zero produces a nonzero Galerkin Robin trial mode. -/
theorem exists_galerkinRobinMode_of_det_eq_zero
    (galerkin : CanonicalScalarBoundaryGalerkinData
      (Trace := Trace) (Coefficient := Coefficient))
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hDet : galerkin.schurDeterminant data traceBound spectralParameter
      poissonData robin = 0) :
    Nonempty (CanonicalScalarGraphGalerkinRobinMode
      galerkin data traceBound spectralParameter poissonData robin) := by
  have hKernel := (galerkin.schurDeterminant_eq_zero_iff
    data traceBound spectralParameter poissonData robin).1 hDet
  rw [Submodule.ne_bot_iff] at hKernel
  rcases hKernel with ⟨coefficient, hCoefficient⟩
  exact ⟨{
    coefficient := coefficient.1
    coefficient_ne_zero := by
      intro hZero
      exact hCoefficient (Subtype.ext hZero)
    projectedEquation := LinearMap.mem_ker.mp coefficient.2 }⟩

/-- Galerkin boundary-reduction certificate. -/
theorem canonicalScalarGraphBoundaryGalerkin_certificate
    (galerkin : CanonicalScalarBoundaryGalerkinData
      (Trace := Trace) (Coefficient := Coefficient))
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    (galerkin.schur data traceBound spectralParameter
        poissonData robin).toLinearMap.IsSymmetric ∧
      (galerkin.schurDeterminant data traceBound spectralParameter
          poissonData robin = 0 ↔
        LinearMap.ker
          (galerkin.schur data traceBound spectralParameter
            poissonData robin).toLinearMap ≠ ⊥) :=
  ⟨galerkin.schur_isSymmetric data traceBound spectralParameter
      poissonData robin hRobin,
    galerkin.schurDeterminant_eq_zero_iff
      data traceBound spectralParameter poissonData robin⟩

end CanonicalScalarBoundaryGalerkinData

end
end P0EFTJanusMappingTorusScalarGraphBoundaryGalerkin4D
end JanusFormal
