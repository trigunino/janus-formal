import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarClosedGraphRealization4D

/-!
# Dense symmetric scalar cores are closable

The graph architecture previously kept single-valuedness of the closed relation
as an explicit assumption.  For the physical scalar operator this assumption is
not independent: a densely defined symmetric operator is closable.

This file proves that fact directly in the graph-completion model used by
Program P.  The argument first extends the smooth symmetry identity to one
completed graph vector by density of the algebraic graph core.  A vertical graph
vector is then orthogonal to the dense ambient inclusion range, hence its
operator coordinate vanishes.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarSymmetricCoreClosable4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Symmetry against a smooth test vector extends to every vector of the closed
graph. -/
theorem canonicalScalarCompletedGraph_pairing_symmetric_against_core
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hSymmetric : ∀ first second : Domain,
      inner Real (data.operator first) (data.inclusion second) =
        inner Real (data.inclusion first) (data.operator second))
    (graphField : CanonicalScalarOperatorGraphSpace data)
    (test : Domain) :
    inner Real (canonicalScalarOperatorGraphOperator data graphField)
        (data.inclusion test) =
      inner Real (canonicalScalarOperatorGraphInclusion data graphField)
        (data.operator test) := by
  let good : Set (CanonicalScalarOperatorGraphSpace data) :=
    {field |
      inner Real (canonicalScalarOperatorGraphOperator data field)
          (data.inclusion test) =
        inner Real (canonicalScalarOperatorGraphInclusion data field)
          (data.operator test)}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hCore : Set.range
      (canonicalScalarSmoothToOperatorGraphLinearMap data) ⊆ good := by
    rintro field ⟨smoothField, rfl⟩
    exact hSymmetric smoothField test
  have hClosure : closure (Set.range
      (canonicalScalarSmoothToOperatorGraphLinearMap data)) = Set.univ :=
    (canonicalScalarSmoothToOperatorGraph_denseRange data).closure_range
  have hGraphMem : graphField ∈ closure (Set.range
      (canonicalScalarSmoothToOperatorGraphLinearMap data)) := by
    rw [hClosure]
    trivial
  exact (closure_minimal hCore hGoodClosed) hGraphMem

/-- A vertical completed graph vector has zero operator coordinate when the
ambient smooth inclusion is dense and the core operator is symmetric. -/
theorem canonicalScalarCompletedGraph_operator_eq_zero_of_inclusion_eq_zero
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hDense : DenseRange data.inclusion)
    (hSymmetric : ∀ first second : Domain,
      inner Real (data.operator first) (data.inclusion second) =
        inner Real (data.inclusion first) (data.operator second))
    (graphField : CanonicalScalarOperatorGraphSpace data)
    (hVertical : canonicalScalarOperatorGraphInclusion data graphField = 0) :
    canonicalScalarOperatorGraphOperator data graphField = 0 := by
  let residual : Ambient := canonicalScalarOperatorGraphOperator data graphField
  have hCoreOrthogonal (test : Domain) :
      inner Real residual (data.inclusion test) = 0 := by
    have hPairing := canonicalScalarCompletedGraph_pairing_symmetric_against_core
      data hSymmetric graphField test
    rw [hVertical] at hPairing
    simpa [residual] using hPairing
  let good : Set Ambient := {test | inner Real residual test = 0}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range data.inclusion ⊆ good := by
    rintro test ⟨smoothTest, rfl⟩
    exact hCoreOrthogonal smoothTest
  have hClosure : closure (Set.range data.inclusion) = Set.univ :=
    hDense.closure_range
  have hResidualMem : residual ∈ closure (Set.range data.inclusion) := by
    rw [hClosure]
    trivial
  have hResidualOrthogonal : inner Real residual residual = 0 :=
    (closure_minimal hRange hGoodClosed) hResidualMem
  have hNormSq : ‖residual‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hResidualOrthogonal
  have hNorm : ‖residual‖ = 0 := by
    nlinarith [sq_nonneg ‖residual‖]
  exact norm_eq_zero.mp hNorm

/-- A densely defined symmetric scalar Green core has a single-valued closed
graph. -/
theorem canonicalScalarGraphClosable_of_dense_symmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hDense : DenseRange data.inclusion)
    (hSymmetric : ∀ first second : Domain,
      inner Real (data.operator first) (data.inclusion second) =
        inner Real (data.inclusion first) (data.operator second)) :
    CanonicalScalarGraphClosable data := by
  intro first second hInclusion
  have hDifferenceInclusion :
      canonicalScalarOperatorGraphInclusion data (first - second) = 0 := by
    rw [map_sub, hInclusion, sub_self]
  have hDifferenceOperator :
      canonicalScalarOperatorGraphOperator data (first - second) = 0 :=
    canonicalScalarCompletedGraph_operator_eq_zero_of_inclusion_eq_zero
      data hDense hSymmetric (first - second) hDifferenceInclusion
  have hOperator :
      canonicalScalarOperatorGraphOperator data first =
        canonicalScalarOperatorGraphOperator data second := by
    rw [map_sub, sub_eq_zero] at hDifferenceOperator
    exact hDifferenceOperator
  apply Subtype.ext
  apply Prod.ext
  · exact hInclusion
  · exact hOperator

/-- The closability conclusion also identifies the vertical graph subspace as
zero. -/
theorem canonicalScalarOperatorGraphVerticalSubmodule_eq_bot_of_dense_symmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hDense : DenseRange data.inclusion)
    (hSymmetric : ∀ first second : Domain,
      inner Real (data.operator first) (data.inclusion second) =
        inner Real (data.inclusion first) (data.operator second)) :
    canonicalScalarOperatorGraphVerticalSubmodule data = ⊥ :=
  canonicalScalarOperatorGraphVerticalSubmodule_eq_bot data
    (canonicalScalarGraphClosable_of_dense_symmetric data hDense hSymmetric)

/-- Dense-symmetric closability certificate. -/
theorem canonicalScalarSymmetricCoreClosable_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hDense : DenseRange data.inclusion)
    (hSymmetric : ∀ first second : Domain,
      inner Real (data.operator first) (data.inclusion second) =
        inner Real (data.inclusion first) (data.operator second)) :
    CanonicalScalarGraphClosable data ∧
      canonicalScalarOperatorGraphVerticalSubmodule data = ⊥ :=
  ⟨canonicalScalarGraphClosable_of_dense_symmetric data hDense hSymmetric,
    canonicalScalarOperatorGraphVerticalSubmodule_eq_bot_of_dense_symmetric
      data hDense hSymmetric⟩

end
end P0EFTJanusMappingTorusScalarSymmetricCoreClosable4D
end JanusFormal
