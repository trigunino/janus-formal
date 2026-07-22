import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

/-!
# Regularity factorization of a completed scalar Green core

A graph estimate on the smooth core extends a regularity map continuously to the
completed maximal graph.  If the regularity-space inclusion agrees with the
original smooth ambient inclusion, the completed graph inclusion factors through
that regularity space.

Consequently a compact Sobolev/Rellich inclusion makes the maximal graph
inclusion compact, and therefore makes every completed Lagrangian domain
inclusion compact as well.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGreenCoreRegularityFactorization4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe u v w z

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  {Regularity : Type z}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- A regularity realization of one smooth scalar Green core. -/
structure CanonicalScalarGreenCoreRegularityData
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) where
  regularityCore : Domain →ₗ[Real] Regularity
  regularityInclusion : Regularity →L[Real] Ambient
  inclusion_agrees : ∀ field : Domain,
    regularityInclusion (regularityCore field) = core.inclusion field
  constant : Real
  nonnegative : 0 ≤ constant
  bound : ∀ field : Domain,
    ‖regularityCore field‖ ≤
      constant * ‖canonicalScalarGreenCoreToGraph core field‖

namespace CanonicalScalarGreenCoreRegularityData

/-- Continuous extension of the regularity map to the maximal completed graph. -/
def completedRegularity
    (regularity : CanonicalScalarGreenCoreRegularityData
      (Regularity := Regularity) core) :
    CanonicalScalarGreenCoreGraphSpace core →L[Real] Regularity :=
  regularity.regularityCore.extendOfNorm
    (canonicalScalarGreenCoreToGraph core)

/-- Agreement of the completed regularity map on smooth core vectors. -/
theorem completedRegularity_smooth
    (regularity : CanonicalScalarGreenCoreRegularityData
      (Regularity := Regularity) core)
    (field : Domain) :
    regularity.completedRegularity
        (canonicalScalarGreenCoreToGraph core field) =
      regularity.regularityCore field :=
  LinearMap.extendOfNorm_eq
    (canonicalScalarGreenCoreToGraph_denseRange core)
    ⟨regularity.constant, regularity.bound⟩ field

/-- Norm control of the completed regularity map. -/
theorem completedRegularity_norm_le
    (regularity : CanonicalScalarGreenCoreRegularityData
      (Regularity := Regularity) core)
    (field : CanonicalScalarGreenCoreGraphSpace core) :
    ‖regularity.completedRegularity field‖ ≤
      regularity.constant * ‖field‖ :=
  LinearMap.norm_extendOfNorm_apply_le
    (canonicalScalarGreenCoreToGraph_denseRange core)
    regularity.constant regularity.bound field

/-- Exact factorization of the completed graph inclusion through the regularity
space. -/
theorem regularityInclusion_completedRegularity
    (regularity : CanonicalScalarGreenCoreRegularityData
      (Regularity := Regularity) core)
    (field : CanonicalScalarGreenCoreGraphSpace core) :
    regularity.regularityInclusion
        (regularity.completedRegularity field) =
      canonicalScalarGreenCoreGraphInclusion core field := by
  let good : Set (CanonicalScalarGreenCoreGraphSpace core) :=
    {candidate |
      regularity.regularityInclusion
          (regularity.completedRegularity candidate) =
        canonicalScalarGreenCoreGraphInclusion core candidate}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range (canonicalScalarGreenCoreToGraph core) ⊆ good := by
    rintro candidate ⟨smoothField, rfl⟩
    rw [regularity.completedRegularity_smooth,
      regularity.inclusion_agrees]
    rfl
  have hClosure : closure
      (Set.range (canonicalScalarGreenCoreToGraph core)) = Set.univ :=
    (canonicalScalarGreenCoreToGraph_denseRange core).closure_range
  have hField : field ∈ closure
      (Set.range (canonicalScalarGreenCoreToGraph core)) := by
    rw [hClosure]
    trivial
  exact (closure_minimal hRange hGoodClosed) hField

/-- Equality of continuous maps in the regularity factorization. -/
theorem regularity_factorization
    (regularity : CanonicalScalarGreenCoreRegularityData
      (Regularity := Regularity) core) :
    regularity.regularityInclusion.comp regularity.completedRegularity =
      canonicalScalarGreenCoreGraphInclusion core := by
  ext field
  exact regularity.regularityInclusion_completedRegularity field

/-- Compact regularity embedding gives compact maximal graph inclusion. -/
theorem graphInclusion_compact
    (regularity : CanonicalScalarGreenCoreRegularityData
      (Regularity := Regularity) core)
    (hCompact : IsCompactOperator regularity.regularityInclusion) :
    IsCompactOperator (canonicalScalarGreenCoreGraphInclusion core) := by
  rw [← regularity.regularity_factorization]
  exact hCompact.comp_clm regularity.completedRegularity

/-- Compact regularity embedding gives compact inclusion for every completed
Lagrangian boundary domain. -/
theorem lagrangianInclusion_compact
    (regularity : CanonicalScalarGreenCoreRegularityData
      (Regularity := Regularity) core)
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (hCompact : IsCompactOperator regularity.regularityInclusion) :
    IsCompactOperator (triple.lagrangianInclusion condition) := by
  change IsCompactOperator
    ((canonicalScalarGreenCoreGraphInclusion core).comp
      (triple.lagrangianDomainSubmodule condition).subtypeL)
  exact (regularity.graphInclusion_compact hCompact).comp_clm
    (triple.lagrangianDomainSubmodule condition).subtypeL

/-- Regularity factorization certificate. -/
theorem certificate
    (regularity : CanonicalScalarGreenCoreRegularityData
      (Regularity := Regularity) core) :
    (∀ field : CanonicalScalarGreenCoreGraphSpace core,
      regularity.regularityInclusion
          (regularity.completedRegularity field) =
        canonicalScalarGreenCoreGraphInclusion core field) ∧
      (∀ field : CanonicalScalarGreenCoreGraphSpace core,
        ‖regularity.completedRegularity field‖ ≤
          regularity.constant * ‖field‖) :=
  ⟨regularity.regularityInclusion_completedRegularity,
    regularity.completedRegularity_norm_le⟩

end CanonicalScalarGreenCoreRegularityData

end
end P0EFTJanusMappingTorusScalarGreenCoreRegularityFactorization4D
end JanusFormal
