import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGreenCoreInteriorDensity4D

/-!
# From smooth cutoff density to a dense interior core

Once shrinking zero-Cauchy cutoffs prove density of the minimal domain, that
minimal domain itself can be used as the abstract dense interior core.  This
small bridge allows all constructions parameterized by
`CanonicalScalarGreenCoreInteriorDensityData` to consume the more geometric
cutoff approximation package directly.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffInteriorBridge4D
end P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffInteriorBridge4D

namespace P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffDensity4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D.CanonicalScalarHilbertGreenCore
open P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffDensity4D
open P0EFTJanusMappingTorusScalarGreenCoreInteriorDensity4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarGreenCoreMinimalCutoffData

variable {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}

/-- The minimal zero-Cauchy domain as a dense interior core. -/
def toInteriorDensityData
    (cutoffData : CanonicalScalarGreenCoreMinimalCutoffData core) :
    CanonicalScalarGreenCoreInteriorDensityData
      (InteriorCore := minimalDomainSubmodule core) core where
  toDomain := (minimalDomainSubmodule core).subtype
  boundary_zero := by
    intro test
    exact LinearMap.mem_ker.mp test.2
  dense := cutoffData.minimalCoreDense

/-- The resulting interior density conclusion is the original minimal-core
density theorem. -/
theorem toInteriorDensityData_minimalCoreDense
    (cutoffData : CanonicalScalarGreenCoreMinimalCutoffData core) :
    cutoffData.toInteriorDensityData.minimalCoreDense =
      cutoffData.minimalCoreDense :=
  rfl

/-- Cutoff/interior bridge certificate. -/
theorem interiorBridgeCertificate
    (cutoffData : CanonicalScalarGreenCoreMinimalCutoffData core) :
    DenseRange
        (core.inclusion.comp (minimalDomainSubmodule core).subtype) ∧
      MinimalCoreDense core :=
  ⟨cutoffData.minimalCoreDense,
    cutoffData.minimalCoreDense⟩

end CanonicalScalarGreenCoreMinimalCutoffData

end
end P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffDensity4D
end JanusFormal
