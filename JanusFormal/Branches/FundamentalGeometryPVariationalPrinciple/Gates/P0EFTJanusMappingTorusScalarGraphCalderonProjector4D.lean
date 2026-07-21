import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D

/-!
# Calderon projector for the completed scalar graph

A Dirichlet Poisson operator identifies the Cauchy-data space with the graph of
the Dirichlet-to-Neumann operator.  The canonical Calderon projector sends an
arbitrary boundary pair `(value, normal)` to `(value, DtN value)`.

This file proves idempotence, identifies its range with the closed Lagrangian
Cauchy-data graph, identifies its kernel with the Dirichlet vertical subspace,
and constructs the complementary projector and exact boundary splitting.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphCalderonProjector4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Calderon projector onto the homogeneous Cauchy-data graph. -/
def canonicalScalarGraphCalderonProjector
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    CanonicalScalarHilbertBoundaryDatum (Trace := Trace) →L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace) where
  toFun boundary :=
    (boundary.1,
      canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData boundary.1)
  map_add' first second := by ext <;> simp
  map_smul' scalar boundary := by ext <;> simp
  cont := by fun_prop

@[simp] theorem canonicalScalarGraphCalderonProjector_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (boundary : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarGraphCalderonProjector
        data traceBound spectralParameter poissonData boundary =
      (boundary.1,
        canonicalScalarGraphDirichletToNeumann
          data traceBound spectralParameter poissonData boundary.1) :=
  rfl

/-- The Calderon projector is idempotent. -/
theorem canonicalScalarGraphCalderonProjector_idempotent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    (canonicalScalarGraphCalderonProjector
        data traceBound spectralParameter poissonData).comp
      (canonicalScalarGraphCalderonProjector
        data traceBound spectralParameter poissonData) =
      canonicalScalarGraphCalderonProjector
        data traceBound spectralParameter poissonData := by
  ext boundary <;> rfl

/-- Range of the Calderon projector is exactly the Cauchy-data graph. -/
theorem canonicalScalarGraphCalderonProjector_range_eq_cauchyData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    LinearMap.range
        (canonicalScalarGraphCalderonProjector
          data traceBound spectralParameter poissonData).toLinearMap =
      canonicalScalarGraphCauchyDataSubmodule
        data traceBound spectralParameter poissonData := by
  ext boundary
  constructor
  · rintro ⟨source, rfl⟩
    exact (mem_canonicalScalarHilbertRobinGraphSubmodule
      (canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData) _).2 rfl
  · intro hBoundary
    have hGraph := (mem_canonicalScalarHilbertRobinGraphSubmodule
      (canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData) boundary).1 hBoundary
    refine ⟨boundary, ?_⟩
    apply Prod.ext
    · rfl
    · exact hGraph.symm

/-- Kernel of the Calderon projector is the Dirichlet vertical boundary
subspace. -/
theorem canonicalScalarGraphCalderonProjector_ker_eq_dirichlet
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    LinearMap.ker
        (canonicalScalarGraphCalderonProjector
          data traceBound spectralParameter poissonData).toLinearMap =
      canonicalScalarHilbertDirichletBoundarySubmodule (Trace := Trace) := by
  ext boundary
  rw [LinearMap.mem_ker,
    mem_canonicalScalarHilbertDirichletBoundarySubmodule]
  constructor
  · intro hZero
    exact congrArg Prod.fst hZero
  · intro hValue
    apply Prod.ext
    · simpa using hValue
    · simp [hValue]

/-- Complementary projector onto the vertical Dirichlet data. -/
def canonicalScalarGraphCalderonComplement
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    CanonicalScalarHilbertBoundaryDatum (Trace := Trace) →L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace) :=
  ContinuousLinearMap.id Real _ -
    canonicalScalarGraphCalderonProjector
      data traceBound spectralParameter poissonData

@[simp] theorem canonicalScalarGraphCalderonComplement_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (boundary : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarGraphCalderonComplement
        data traceBound spectralParameter poissonData boundary =
      (0, boundary.2 -
        canonicalScalarGraphDirichletToNeumann
          data traceBound spectralParameter poissonData boundary.1) := by
  apply Prod.ext <;> simp [canonicalScalarGraphCalderonComplement]

/-- The complementary projector is idempotent. -/
theorem canonicalScalarGraphCalderonComplement_idempotent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    (canonicalScalarGraphCalderonComplement
        data traceBound spectralParameter poissonData).comp
      (canonicalScalarGraphCalderonComplement
        data traceBound spectralParameter poissonData) =
      canonicalScalarGraphCalderonComplement
        data traceBound spectralParameter poissonData := by
  ext boundary
  apply Prod.ext <;> simp [canonicalScalarGraphCalderonComplement]

/-- Range of the complementary projector is the Dirichlet vertical subspace. -/
theorem canonicalScalarGraphCalderonComplement_range_eq_dirichlet
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    LinearMap.range
        (canonicalScalarGraphCalderonComplement
          data traceBound spectralParameter poissonData).toLinearMap =
      canonicalScalarHilbertDirichletBoundarySubmodule (Trace := Trace) := by
  ext boundary
  constructor
  · rintro ⟨source, rfl⟩
    rw [mem_canonicalScalarHilbertDirichletBoundarySubmodule]
    simp
  · intro hBoundary
    have hValue := (mem_canonicalScalarHilbertDirichletBoundarySubmodule
      (Trace := Trace) boundary).1 hBoundary
    refine ⟨boundary, ?_⟩
    apply Prod.ext
    · simp [canonicalScalarGraphCalderonComplement, hValue]
    · simp [canonicalScalarGraphCalderonComplement, hValue]

/-- Cauchy and vertical components add to the original boundary datum. -/
theorem canonicalScalarGraphCalderon_add_complement
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (boundary : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarGraphCalderonProjector
          data traceBound spectralParameter poissonData boundary +
        canonicalScalarGraphCalderonComplement
          data traceBound spectralParameter poissonData boundary =
      boundary := by
  apply Prod.ext <;> simp [canonicalScalarGraphCalderonComplement]

/-- Exact linear equivalence between arbitrary boundary data and the product of
Cauchy data with vertical Dirichlet data. -/
noncomputable def canonicalScalarGraphCalderonSplittingEquiv
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    CanonicalScalarHilbertBoundaryDatum (Trace := Trace) ≃ₗ[Real]
      canonicalScalarGraphCauchyDataSubmodule
          data traceBound spectralParameter poissonData ×
        canonicalScalarHilbertDirichletBoundarySubmodule (Trace := Trace) where
  toFun boundary :=
    (⟨canonicalScalarGraphCalderonProjector
        data traceBound spectralParameter poissonData boundary,
      by
        rw [← canonicalScalarGraphCalderonProjector_range_eq_cauchyData]
        exact LinearMap.mem_range_self _ boundary⟩,
     ⟨canonicalScalarGraphCalderonComplement
        data traceBound spectralParameter poissonData boundary,
      by
        rw [← canonicalScalarGraphCalderonComplement_range_eq_dirichlet]
        exact LinearMap.mem_range_self _ boundary⟩)
  invFun components := components.1.1 + components.2.1
  left_inv boundary := canonicalScalarGraphCalderon_add_complement
    data traceBound spectralParameter poissonData boundary
  right_inv components := by
    apply Prod.ext
    · apply Subtype.ext
      have hCauchy := components.1.2
      have hRange : components.1.1 ∈ LinearMap.range
          (canonicalScalarGraphCalderonProjector
            data traceBound spectralParameter poissonData).toLinearMap := by
        rw [canonicalScalarGraphCalderonProjector_range_eq_cauchyData]
        exact hCauchy
      rcases hRange with ⟨source, hSource⟩
      rw [map_add, hSource,
        ← ContinuousLinearMap.comp_apply,
        canonicalScalarGraphCalderonProjector_idempotent]
      have hVertical := components.2.2
      have hKernel : components.2.1 ∈ LinearMap.ker
          (canonicalScalarGraphCalderonProjector
            data traceBound spectralParameter poissonData).toLinearMap := by
        rw [canonicalScalarGraphCalderonProjector_ker_eq_dirichlet]
        exact hVertical
      rw [LinearMap.mem_ker.mp hKernel, add_zero]
    · apply Subtype.ext
      have hCauchy := components.1.2
      have hCauchyKernel : components.1.1 ∈ LinearMap.ker
          (canonicalScalarGraphCalderonComplement
            data traceBound spectralParameter poissonData).toLinearMap := by
        rw [LinearMap.mem_ker]
        have hRange : components.1.1 ∈ LinearMap.range
            (canonicalScalarGraphCalderonProjector
              data traceBound spectralParameter poissonData).toLinearMap := by
          rw [canonicalScalarGraphCalderonProjector_range_eq_cauchyData]
          exact hCauchy
        rcases hRange with ⟨source, hSource⟩
        rw [hSource]
        apply Prod.ext <;> simp [canonicalScalarGraphCalderonComplement]
      rw [map_add, LinearMap.mem_ker.mp hCauchyKernel]
      have hVertical := components.2.2
      have hRange : components.2.1 ∈ LinearMap.range
          (canonicalScalarGraphCalderonComplement
            data traceBound spectralParameter poissonData).toLinearMap := by
        rw [canonicalScalarGraphCalderonComplement_range_eq_dirichlet]
        exact hVertical
      rcases hRange with ⟨source, hSource⟩
      rw [hSource,
        ← ContinuousLinearMap.comp_apply,
        canonicalScalarGraphCalderonComplement_idempotent,
        zero_add]
  map_add' first second := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_smul' scalar boundary := by
    apply Prod.ext <;> apply Subtype.ext <;> simp

/-- Calderon closure certificate. -/
theorem canonicalScalarGraphCalderonProjector_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter) :
    (canonicalScalarGraphCalderonProjector
        data traceBound spectralParameter poissonData).comp
        (canonicalScalarGraphCalderonProjector
          data traceBound spectralParameter poissonData) =
      canonicalScalarGraphCalderonProjector
        data traceBound spectralParameter poissonData ∧
    LinearMap.range
        (canonicalScalarGraphCalderonProjector
          data traceBound spectralParameter poissonData).toLinearMap =
      canonicalScalarGraphCauchyDataSubmodule
        data traceBound spectralParameter poissonData ∧
    LinearMap.ker
        (canonicalScalarGraphCalderonProjector
          data traceBound spectralParameter poissonData).toLinearMap =
      canonicalScalarHilbertDirichletBoundarySubmodule (Trace := Trace) :=
  ⟨canonicalScalarGraphCalderonProjector_idempotent
      data traceBound spectralParameter poissonData,
    canonicalScalarGraphCalderonProjector_range_eq_cauchyData
      data traceBound spectralParameter poissonData,
    canonicalScalarGraphCalderonProjector_ker_eq_dirichlet
      data traceBound spectralParameter poissonData⟩

end
end P0EFTJanusMappingTorusScalarGraphCalderonProjector4D
end JanusFormal
