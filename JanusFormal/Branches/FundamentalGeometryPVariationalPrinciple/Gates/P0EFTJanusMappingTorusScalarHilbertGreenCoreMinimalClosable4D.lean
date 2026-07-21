import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

/-!
# Minimal zero-trace core closes a dense Hilbert Green core

For the corrected dense-core architecture, the minimal smooth domain is the
kernel of the paired Cauchy trace.  Testing the full Green identity against this
minimal core removes the boundary form.  Density of the minimal ambient image
then forces every vertical vector in the completed graph to vanish.

Thus the completed maximal graph is single-valued without ever requiring the
smooth trace map to be surjective onto the whole boundary Hilbert space.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarHilbertGreenCore

/-- Minimal smooth domain with zero paired trace. -/
def minimalDomainSubmodule
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    Submodule Real Domain :=
  LinearMap.ker core.boundaryTrace

/-- Minimal smooth inclusion. -/
def minimalInclusion
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    core.minimalDomainSubmodule →ₗ[Real] Ambient :=
  core.inclusion.comp core.minimalDomainSubmodule.subtype

/-- Minimal smooth operator. -/
def minimalOperator
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    core.minimalDomainSubmodule →ₗ[Real] Ambient :=
  core.operator.comp core.minimalDomainSubmodule.subtype

/-- Formal-adjoint pairing against zero-trace tests. -/
theorem maximal_minimal_pairing
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (field : Domain) (test : core.minimalDomainSubmodule) :
    inner Real (core.operator field) (core.minimalInclusion test) =
      inner Real (core.inclusion field) (core.minimalOperator test) := by
  have hGreen := core.green_identity field test.1
  have hTraceZero : core.boundaryTrace test.1 = 0 :=
    LinearMap.mem_ker.mp test.2
  rw [hTraceZero,
    canonicalScalarHilbertBoundarySymplecticForm_zero_right] at hGreen
  linarith

/-- Density of the minimal smooth core. -/
def MinimalCoreDense
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) : Prop :=
  DenseRange core.minimalInclusion

/-- The formal-adjoint pairing extends to one completed graph vector. -/
theorem completedGraph_pairing_minimal
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (graphField : CanonicalScalarGreenCoreGraphSpace core)
    (test : core.minimalDomainSubmodule) :
    inner Real (canonicalScalarGreenCoreGraphOperator core graphField)
        (core.minimalInclusion test) =
      inner Real (canonicalScalarGreenCoreGraphInclusion core graphField)
        (core.minimalOperator test) := by
  let good : Set (CanonicalScalarGreenCoreGraphSpace core) :=
    {field |
      inner Real (canonicalScalarGreenCoreGraphOperator core field)
          (core.minimalInclusion test) =
        inner Real (canonicalScalarGreenCoreGraphInclusion core field)
          (core.minimalOperator test)}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range (canonicalScalarGreenCoreToGraph core) ⊆ good := by
    rintro field ⟨smoothField, rfl⟩
    exact core.maximal_minimal_pairing smoothField test
  have hClosure : closure (Set.range
      (canonicalScalarGreenCoreToGraph core)) = Set.univ :=
    (canonicalScalarGreenCoreToGraph_denseRange core).closure_range
  have hGraphMem : graphField ∈ closure (Set.range
      (canonicalScalarGreenCoreToGraph core)) := by
    rw [hClosure]
    trivial
  exact (closure_minimal hRange hGoodClosed) hGraphMem

/-- A vertical completed graph vector has zero operator coordinate. -/
theorem graphOperator_eq_zero_of_graphInclusion_eq_zero
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hDense : core.MinimalCoreDense)
    (graphField : CanonicalScalarGreenCoreGraphSpace core)
    (hVertical : canonicalScalarGreenCoreGraphInclusion core graphField = 0) :
    canonicalScalarGreenCoreGraphOperator core graphField = 0 := by
  let residual : Ambient := canonicalScalarGreenCoreGraphOperator core graphField
  have hTestOrthogonal (test : core.minimalDomainSubmodule) :
      inner Real residual (core.minimalInclusion test) = 0 := by
    have hPairing := core.completedGraph_pairing_minimal graphField test
    rw [hVertical] at hPairing
    simpa [residual] using hPairing
  let good : Set Ambient := {test | inner Real residual test = 0}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range core.minimalInclusion ⊆ good := by
    rintro test ⟨smoothTest, rfl⟩
    exact hTestOrthogonal smoothTest
  have hClosure : closure (Set.range core.minimalInclusion) = Set.univ :=
    hDense.closure_range
  have hResidualMem : residual ∈ closure (Set.range core.minimalInclusion) := by
    rw [hClosure]
    trivial
  have hResidualOrthogonal : inner Real residual residual = 0 :=
    (closure_minimal hRange hGoodClosed) hResidualMem
  have hNormSq : ‖residual‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hResidualOrthogonal
  exact norm_eq_zero.mp (by nlinarith [sq_nonneg ‖residual‖])

/-- Density of the minimal core makes the completed maximal inclusion
injective. -/
theorem graphInclusion_injective_of_minimal_dense
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hDense : core.MinimalCoreDense) :
    Function.Injective (canonicalScalarGreenCoreGraphInclusion core) := by
  intro first second hInclusion
  have hDifferenceInclusion :
      canonicalScalarGreenCoreGraphInclusion core (first - second) = 0 := by
    rw [map_sub, hInclusion, sub_self]
  have hDifferenceOperator :
      canonicalScalarGreenCoreGraphOperator core (first - second) = 0 :=
    core.graphOperator_eq_zero_of_graphInclusion_eq_zero
      hDense (first - second) hDifferenceInclusion
  apply Subtype.ext
  apply Prod.ext
  · exact hInclusion
  · rw [map_sub, sub_eq_zero] at hDifferenceOperator
    exact hDifferenceOperator

/-- Minimal-core closability certificate. -/
theorem minimalCoreClosable_certificate
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hDense : core.MinimalCoreDense) :
    Function.Injective (canonicalScalarGreenCoreGraphInclusion core) ∧
      (∀ graphField : CanonicalScalarGreenCoreGraphSpace core,
        canonicalScalarGreenCoreGraphInclusion core graphField = 0 →
          canonicalScalarGreenCoreGraphOperator core graphField = 0) :=
  ⟨core.graphInclusion_injective_of_minimal_dense hDense,
    core.graphOperator_eq_zero_of_graphInclusion_eq_zero hDense⟩

end CanonicalScalarHilbertGreenCore

end
end P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
end JanusFormal
