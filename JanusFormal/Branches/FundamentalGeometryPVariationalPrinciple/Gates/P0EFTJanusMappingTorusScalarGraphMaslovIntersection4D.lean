import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundarySpectralFlow4D

/-!
# Lagrangian intersections and scalar Robin modes

At a fixed spectral parameter, the homogeneous Cauchy data form the graph of
the Dirichlet-to-Neumann operator.  A Robin boundary condition is another
Lagrangian graph.  Their intersection is therefore the geometric carrier of
Robin eigenmodes.

This file constructs exact linear equivalences among:

* the boundary Schur kernel;
* the intersection of the Cauchy-data and Robin Lagrangians;
* the homogeneous Robin bulk-solution space.

It also transfers nontriviality and finite-dimensional multiplicity to the
Lagrangian-intersection description used by the Maslov index.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphMaslovIntersection4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarHilbertRobinGraph4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Intersection of homogeneous Cauchy data with a Robin graph. -/
def canonicalScalarGraphCauchyRobinIntersection
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    Submodule Real (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :=
  canonicalScalarGraphCauchyDataSubmodule
      data traceBound spectralParameter poissonData ⊓
    canonicalScalarHilbertRobinGraphSubmodule robin

@[simp] theorem mem_canonicalScalarGraphCauchyRobinIntersection
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (boundary : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    boundary ∈ canonicalScalarGraphCauchyRobinIntersection
        data traceBound spectralParameter poissonData robin ↔
      boundary.2 = canonicalScalarGraphDirichletToNeumann
          data traceBound spectralParameter poissonData boundary.1 ∧
        boundary.2 = robin boundary.1 := by
  rw [canonicalScalarGraphCauchyRobinIntersection, Submodule.mem_inf]
  exact and_congr
    (mem_canonicalScalarHilbertRobinGraphSubmodule
      (canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData) boundary)
    (mem_canonicalScalarHilbertRobinGraphSubmodule robin boundary)

/-- Schur-kernel boundary value mapped to its full Cauchy pair. -/
def canonicalScalarGraphSchurKernelToLagrangianIntersection
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
      canonicalScalarGraphCauchyRobinIntersection
        data traceBound spectralParameter poissonData robin where
  toFun boundary :=
    ⟨(boundary.1,
      canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData boundary.1), by
      rw [mem_canonicalScalarGraphCauchyRobinIntersection]
      constructor
      · rfl
      · have hKernel := LinearMap.mem_ker.mp boundary.2
        change canonicalScalarGraphDirichletToNeumann
              data traceBound spectralParameter poissonData boundary.1 -
            robin boundary.1 = 0 at hKernel
        exact sub_eq_zero.mp hKernel⟩
  map_add' first second := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  map_smul' scalar boundary := by
    apply Subtype.ext
    apply Prod.ext <;> simp

/-- Lagrangian-intersection pair mapped to its value component in the Schur
kernel. -/
def canonicalScalarGraphLagrangianIntersectionToSchurKernel
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarGraphCauchyRobinIntersection
        data traceBound spectralParameter poissonData robin →ₗ[Real]
      LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap where
  toFun boundary :=
    ⟨boundary.1.1, by
      rw [LinearMap.mem_ker]
      have hMembership :=
        (mem_canonicalScalarGraphCauchyRobinIntersection
          data traceBound spectralParameter poissonData robin boundary.1).1
          boundary.2
      change canonicalScalarGraphDirichletToNeumann
          data traceBound spectralParameter poissonData boundary.1.1 -
        robin boundary.1.1 = 0
      rw [← hMembership.1, ← hMembership.2, sub_self]⟩
  map_add' first second := by
    apply Subtype.ext
    rfl
  map_smul' scalar boundary := by
    apply Subtype.ext
    rfl

/-- Exact Schur-kernel/Lagrangian-intersection equivalence. -/
noncomputable def canonicalScalarGraphSchurKernelLagrangianIntersectionEquiv
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap ≃ₗ[Real]
      canonicalScalarGraphCauchyRobinIntersection
        data traceBound spectralParameter poissonData robin where
  toFun := canonicalScalarGraphSchurKernelToLagrangianIntersection
    data traceBound spectralParameter poissonData robin
  invFun := canonicalScalarGraphLagrangianIntersectionToSchurKernel
    data traceBound spectralParameter poissonData robin
  left_inv := by
    intro boundary
    apply Subtype.ext
    rfl
  right_inv := by
    intro boundary
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hMembership :=
        (mem_canonicalScalarGraphCauchyRobinIntersection
          data traceBound spectralParameter poissonData robin boundary.1).1
          boundary.2
      exact hMembership.1.symm
  map_add' := by
    intro first second
    exact (canonicalScalarGraphSchurKernelToLagrangianIntersection
      data traceBound spectralParameter poissonData robin).map_add first second
  map_smul' := by
    intro scalar boundary
    exact (canonicalScalarGraphSchurKernelToLagrangianIntersection
      data traceBound spectralParameter poissonData robin).map_smul scalar boundary

/-- Exact bulk-mode/Lagrangian-intersection equivalence. -/
noncomputable def canonicalScalarGraphRobinSolutionLagrangianIntersectionEquiv
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin ≃ₗ[Real]
      canonicalScalarGraphCauchyRobinIntersection
        data traceBound spectralParameter poissonData robin :=
  (canonicalScalarGraphRobinSolutionSchurKernelEquiv
    data traceBound spectralParameter poissonData robin).trans
      (canonicalScalarGraphSchurKernelLagrangianIntersectionEquiv
        data traceBound spectralParameter poissonData robin)

/-- Nontrivial Lagrangian intersection exactly means a nonzero Robin bulk mode. -/
theorem canonicalScalarGraphCauchyRobinIntersection_ne_bot_iff_bulkMode
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarGraphCauchyRobinIntersection
        data traceBound spectralParameter poissonData robin ≠ ⊥ ↔
      ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0 := by
  rw [Submodule.ne_bot_iff]
  let equivalence := canonicalScalarGraphRobinSolutionLagrangianIntersectionEquiv
    data traceBound spectralParameter poissonData robin
  constructor
  · rintro ⟨boundary, hBoundary, hBoundaryNonzero⟩
    let boundarySubtype : canonicalScalarGraphCauchyRobinIntersection
        data traceBound spectralParameter poissonData robin :=
      ⟨boundary, hBoundary⟩
    refine ⟨equivalence.symm boundarySubtype, ?_⟩
    intro hZero
    apply hBoundaryNonzero
    have hSubtypeZero : boundarySubtype = 0 := by
      apply equivalence.symm.injective
      simpa using hZero
    simpa [boundarySubtype] using congrArg Subtype.val hSubtypeZero
  · rintro ⟨field, hField⟩
    refine ⟨(equivalence field : CanonicalScalarHilbertBoundaryDatum),
      (equivalence field).property, ?_⟩
    intro hBoundaryZero
    apply hField
    apply equivalence.injective
    apply Subtype.ext
    simpa using hBoundaryZero

/-- Finite-dimensional multiplicity transfers from the intersection to the bulk
and conversely by linear equivalence. -/
theorem canonicalScalarGraphRobinSolution_finiteDimensional_of_intersection
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    [FiniteDimensional Real
      (canonicalScalarGraphCauchyRobinIntersection
        data traceBound spectralParameter poissonData robin)] :
    FiniteDimensional Real
      (canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin) := by
  exact FiniteDimensional.of_injective
    (canonicalScalarGraphRobinSolutionLagrangianIntersectionEquiv
      data traceBound spectralParameter poissonData robin).toLinearMap
    (canonicalScalarGraphRobinSolutionLagrangianIntersectionEquiv
      data traceBound spectralParameter poissonData robin).injective

/-- Lagrangian-intersection certificate. -/
theorem canonicalScalarGraphMaslovIntersection_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    Nonempty
      (canonicalScalarGraphRobinHomogeneousSolutionSubmodule
          data traceBound spectralParameter robin ≃ₗ[Real]
        canonicalScalarGraphCauchyRobinIntersection
          data traceBound spectralParameter poissonData robin) ∧
      (canonicalScalarGraphCauchyRobinIntersection
          data traceBound spectralParameter poissonData robin ≠ ⊥ ↔
        ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
          data traceBound spectralParameter robin, field ≠ 0) :=
  ⟨⟨canonicalScalarGraphRobinSolutionLagrangianIntersectionEquiv
      data traceBound spectralParameter poissonData robin⟩,
    canonicalScalarGraphCauchyRobinIntersection_ne_bot_iff_bulkMode
      data traceBound spectralParameter poissonData robin⟩

end
end P0EFTJanusMappingTorusScalarGraphMaslovIntersection4D
end JanusFormal
