import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D

/-!
# Minimal-core density from a dense interior scalar core

Smooth fields supported away from the cutting hypersurface have zero value and
normal traces.  Therefore any dense interior test core embeds in the zero-Cauchy
minimal domain.  Density of its ambient image immediately proves minimal-core
density, which in turn gives closability and density of every Lagrangian
realization.

This file isolates that reduction independently of a particular construction of
compactly supported smooth functions.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGreenCoreInteriorDensity4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D.CanonicalScalarHilbertGreenCore

universe u v w z

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  {InteriorCore : Type z}
  [AddCommGroup Domain] [Module Real Domain]
  [AddCommGroup InteriorCore] [Module Real InteriorCore]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Dense smooth interior core whose fields have zero Cauchy trace. -/
structure CanonicalScalarGreenCoreInteriorDensityData
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) where
  toDomain : InteriorCore →ₗ[Real] Domain
  boundary_zero : ∀ test : InteriorCore,
    core.boundaryTrace (toDomain test) = 0
  dense : DenseRange (core.inclusion.comp toDomain)

namespace CanonicalScalarGreenCoreInteriorDensityData

variable {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}

/-- Interior test fields as vectors of the minimal zero-Cauchy domain. -/
def toMinimalDomain
    (interior : CanonicalScalarGreenCoreInteriorDensityData
      (InteriorCore := InteriorCore) core) :
    InteriorCore →ₗ[Real] minimalDomainSubmodule core where
  toFun test :=
    ⟨interior.toDomain test, by
      change core.boundaryTrace (interior.toDomain test) = 0
      exact interior.boundary_zero test⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar test := by
    apply Subtype.ext
    simp

/-- Minimal inclusion agrees with the original interior ambient inclusion. -/
theorem minimalInclusion_toMinimalDomain
    (interior : CanonicalScalarGreenCoreInteriorDensityData
      (InteriorCore := InteriorCore) core)
    (test : InteriorCore) :
    minimalInclusion core (interior.toMinimalDomain test) =
      core.inclusion (interior.toDomain test) :=
  rfl

/-- The dense interior range is contained in the minimal-domain ambient range. -/
theorem range_interior_subset_minimal
    (interior : CanonicalScalarGreenCoreInteriorDensityData
      (InteriorCore := InteriorCore) core) :
    Set.range (core.inclusion.comp interior.toDomain) ⊆
      Set.range (minimalInclusion core) := by
  rintro value ⟨test, rfl⟩
  exact ⟨interior.toMinimalDomain test,
    interior.minimalInclusion_toMinimalDomain test⟩

/-- A dense zero-trace interior core proves minimal-core density. -/
theorem minimalCoreDense
    (interior : CanonicalScalarGreenCoreInteriorDensityData
      (InteriorCore := InteriorCore) core) :
    MinimalCoreDense core := by
  intro value
  exact closure_mono interior.range_interior_subset_minimal
    (interior.dense value)

/-- The maximal completed graph inclusion is injective. -/
theorem graphInclusion_injective
    (interior : CanonicalScalarGreenCoreInteriorDensityData
      (InteriorCore := InteriorCore) core) :
    Function.Injective (canonicalScalarGreenCoreGraphInclusion core) :=
  graphInclusion_injective_of_minimal_dense core interior.minimalCoreDense

/-- Interior-density certificate. -/
theorem certificate
    (interior : CanonicalScalarGreenCoreInteriorDensityData
      (InteriorCore := InteriorCore) core) :
    MinimalCoreDense core ∧
      Function.Injective (canonicalScalarGreenCoreGraphInclusion core) ∧
      Set.range (core.inclusion.comp interior.toDomain) ⊆
        Set.range (minimalInclusion core) :=
  ⟨interior.minimalCoreDense,
    interior.graphInclusion_injective,
    interior.range_interior_subset_minimal⟩

end CanonicalScalarGreenCoreInteriorDensityData

end
end P0EFTJanusMappingTorusScalarGreenCoreInteriorDensity4D
end JanusFormal
