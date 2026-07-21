import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarClosedGraphRealization4D

/-!
# Closability from a dense adjoint test core

A maximal differential operator with boundary terms need not be symmetric on its
whole smooth domain.  It is nevertheless closable whenever there is a dense
smooth test core on which the boundary terms vanish and an operator representing
the formal adjoint.

This file proves the corresponding theorem directly in the Program-P graph
model.  The symmetric-core theorem is the special case where the test core is
the original domain itself.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarAdjointCoreClosable4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D

universe u v w z

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  {TestDomain : Type z}
  [AddCommGroup Domain] [Module Real Domain]
  [AddCommGroup TestDomain] [Module Real TestDomain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Dense formal-adjoint test data for one scalar Green core. -/
structure CanonicalScalarAdjointTestCore
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) where
  inclusion : TestDomain →ₗ[Real] Ambient
  operator : TestDomain →ₗ[Real] Ambient
  dense : DenseRange inclusion
  pairing : ∀ field : Domain, ∀ test : TestDomain,
    inner Real (data.operator field) (inclusion test) =
      inner Real (data.inclusion field) (operator test)

namespace CanonicalScalarAdjointTestCore

/-- The formal-adjoint pairing extends from the algebraic graph core to every
completed graph vector. -/
theorem completedGraph_pairing
    (testCore : CanonicalScalarAdjointTestCore
      (TestDomain := TestDomain) data)
    (graphField : CanonicalScalarOperatorGraphSpace data)
    (test : TestDomain) :
    inner Real (canonicalScalarOperatorGraphOperator data graphField)
        (testCore.inclusion test) =
      inner Real (canonicalScalarOperatorGraphInclusion data graphField)
        (testCore.operator test) := by
  let good : Set (CanonicalScalarOperatorGraphSpace data) :=
    {field |
      inner Real (canonicalScalarOperatorGraphOperator data field)
          (testCore.inclusion test) =
        inner Real (canonicalScalarOperatorGraphInclusion data field)
          (testCore.operator test)}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hCore : Set.range
      (canonicalScalarSmoothToOperatorGraphLinearMap data) ⊆ good := by
    rintro field ⟨smoothField, rfl⟩
    exact testCore.pairing smoothField test
  have hClosure : closure (Set.range
      (canonicalScalarSmoothToOperatorGraphLinearMap data)) = Set.univ :=
    (canonicalScalarSmoothToOperatorGraph_denseRange data).closure_range
  have hGraphMem : graphField ∈ closure (Set.range
      (canonicalScalarSmoothToOperatorGraphLinearMap data)) := by
    rw [hClosure]
    trivial
  exact (closure_minimal hCore hGoodClosed) hGraphMem

/-- A vertical completed graph vector has zero operator coordinate. -/
theorem operator_eq_zero_of_inclusion_eq_zero
    (testCore : CanonicalScalarAdjointTestCore
      (TestDomain := TestDomain) data)
    (graphField : CanonicalScalarOperatorGraphSpace data)
    (hVertical : canonicalScalarOperatorGraphInclusion data graphField = 0) :
    canonicalScalarOperatorGraphOperator data graphField = 0 := by
  let residual : Ambient := canonicalScalarOperatorGraphOperator data graphField
  have hTestOrthogonal (test : TestDomain) :
      inner Real residual (testCore.inclusion test) = 0 := by
    have hPairing := testCore.completedGraph_pairing graphField test
    rw [hVertical] at hPairing
    simpa [residual] using hPairing
  let good : Set Ambient := {test | inner Real residual test = 0}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range testCore.inclusion ⊆ good := by
    rintro test ⟨smoothTest, rfl⟩
    exact hTestOrthogonal smoothTest
  have hClosure : closure (Set.range testCore.inclusion) = Set.univ :=
    testCore.dense.closure_range
  have hResidualMem : residual ∈ closure (Set.range testCore.inclusion) := by
    rw [hClosure]
    trivial
  have hResidualOrthogonal : inner Real residual residual = 0 :=
    (closure_minimal hRange hGoodClosed) hResidualMem
  have hNormSq : ‖residual‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hResidualOrthogonal
  have hNorm : ‖residual‖ = 0 := by
    nlinarith [sq_nonneg ‖residual‖]
  exact norm_eq_zero.mp hNorm

/-- A dense formal-adjoint test core makes the original maximal graph
single-valued. -/
theorem graphClosable
    (testCore : CanonicalScalarAdjointTestCore
      (TestDomain := TestDomain) data) :
    CanonicalScalarGraphClosable data := by
  intro first second hInclusion
  have hDifferenceInclusion :
      canonicalScalarOperatorGraphInclusion data (first - second) = 0 := by
    rw [map_sub, hInclusion, sub_self]
  have hDifferenceOperator :
      canonicalScalarOperatorGraphOperator data (first - second) = 0 :=
    testCore.operator_eq_zero_of_inclusion_eq_zero
      (first - second) hDifferenceInclusion
  have hOperator :
      canonicalScalarOperatorGraphOperator data first =
        canonicalScalarOperatorGraphOperator data second := by
    rw [map_sub, sub_eq_zero] at hDifferenceOperator
    exact hDifferenceOperator
  apply Subtype.ext
  apply Prod.ext
  · exact hInclusion
  · exact hOperator

/-- The vertical graph subspace vanishes. -/
theorem verticalSubmodule_eq_bot
    (testCore : CanonicalScalarAdjointTestCore
      (TestDomain := TestDomain) data) :
    canonicalScalarOperatorGraphVerticalSubmodule data = ⊥ :=
  canonicalScalarOperatorGraphVerticalSubmodule_eq_bot data
    testCore.graphClosable

/-- Adjoint-test-core closability certificate. -/
theorem certificate
    (testCore : CanonicalScalarAdjointTestCore
      (TestDomain := TestDomain) data) :
    CanonicalScalarGraphClosable data ∧
      canonicalScalarOperatorGraphVerticalSubmodule data = ⊥ :=
  ⟨testCore.graphClosable, testCore.verticalSubmodule_eq_bot⟩

end CanonicalScalarAdjointTestCore

end
end P0EFTJanusMappingTorusScalarAdjointCoreClosable4D
end JanusFormal
