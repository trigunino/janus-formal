import Mathlib.Topology.Sequences
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D

/-!
# Minimal scalar core density from smooth cutoff approximation

Assume smooth scalar fields are dense in the ambient Hilbert space.  If every
smooth field admits a sequence of smooth zero-Cauchy cutoff fields converging to
it in the ambient norm, then the minimal zero-Cauchy domain is dense.

This is the standard proof used when the cutting hypersurface has measure zero:
choose cutoffs vanishing in shrinking collars of the hypersurface.  The theorem
below isolates the functional-analytic closure argument from the later geometric
construction of those cutoffs.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffDensity4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D.CanonicalScalarHilbertGreenCore

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Smooth cutoff approximation into the zero-Cauchy core. -/
structure CanonicalScalarGreenCoreMinimalCutoffData
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) where
  smoothDense : DenseRange core.inclusion
  cutoff : Nat → Domain →ₗ[Real] Domain
  boundary_zero : ∀ (index : Nat) (field : Domain),
    core.boundaryTrace (cutoff index field) = 0
  tendsto_inclusion : ∀ field : Domain,
    Tendsto
      (fun index => core.inclusion (cutoff index field))
      atTop (𝓝 (core.inclusion field))

namespace CanonicalScalarGreenCoreMinimalCutoffData

variable {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}

/-- One cutoff field as a vector of the minimal domain. -/
def cutoffMinimal
    (cutoffData : CanonicalScalarGreenCoreMinimalCutoffData core)
    (index : Nat) : Domain →ₗ[Real] minimalDomainSubmodule core where
  toFun field :=
    ⟨cutoffData.cutoff index field, by
      change core.boundaryTrace (cutoffData.cutoff index field) = 0
      exact cutoffData.boundary_zero index field⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar field := by
    apply Subtype.ext
    simp

/-- The minimal inclusion of a cutoff is its original ambient inclusion. -/
theorem minimalInclusion_cutoffMinimal
    (cutoffData : CanonicalScalarGreenCoreMinimalCutoffData core)
    (index : Nat) (field : Domain) :
    minimalInclusion core (cutoffData.cutoffMinimal index field) =
      core.inclusion (cutoffData.cutoff index field) :=
  rfl

/-- Every smooth ambient field belongs to the closure of the minimal-domain
ambient range. -/
theorem smooth_mem_closure_minimalRange
    (cutoffData : CanonicalScalarGreenCoreMinimalCutoffData core)
    (field : Domain) :
    core.inclusion field ∈ closure (Set.range (minimalInclusion core)) := by
  apply mem_closure_of_tendsto (cutoffData.tendsto_inclusion field)
  exact Filter.Eventually.of_forall fun index =>
    ⟨cutoffData.cutoffMinimal index field,
      cutoffData.minimalInclusion_cutoffMinimal index field⟩

/-- The smooth ambient range lies in the closure of the minimal range. -/
theorem smoothRange_subset_closure_minimalRange
    (cutoffData : CanonicalScalarGreenCoreMinimalCutoffData core) :
    Set.range core.inclusion ⊆ closure (Set.range (minimalInclusion core)) := by
  rintro value ⟨field, rfl⟩
  exact cutoffData.smooth_mem_closure_minimalRange field

/-- Smooth density plus shrinking zero-trace cutoffs proves minimal-core
density. -/
theorem minimalCoreDense
    (cutoffData : CanonicalScalarGreenCoreMinimalCutoffData core) :
    MinimalCoreDense core := by
  intro value
  have hSmoothClosure : value ∈ closure (Set.range core.inclusion) :=
    cutoffData.smoothDense value
  exact (closure_minimal
    cutoffData.smoothRange_subset_closure_minimalRange isClosed_closure)
      hSmoothClosure

/-- The completed maximal graph is single-valued. -/
theorem graphInclusion_injective
    (cutoffData : CanonicalScalarGreenCoreMinimalCutoffData core) :
    Function.Injective (canonicalScalarGreenCoreGraphInclusion core) :=
  graphInclusion_injective_of_minimal_dense core cutoffData.minimalCoreDense

/-- Cutoff-density certificate. -/
theorem certificate
    (cutoffData : CanonicalScalarGreenCoreMinimalCutoffData core) :
    MinimalCoreDense core ∧
      Function.Injective (canonicalScalarGreenCoreGraphInclusion core) ∧
      Set.range core.inclusion ⊆ closure
        (Set.range (minimalInclusion core)) :=
  ⟨cutoffData.minimalCoreDense,
    cutoffData.graphInclusion_injective,
    cutoffData.smoothRange_subset_closure_minimalRange⟩

end CanonicalScalarGreenCoreMinimalCutoffData

end
end P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffDensity4D
end JanusFormal
