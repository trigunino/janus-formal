import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssembly4D

/-!
# Differentiable ProductThroat reference atlas

The base and local regularized zeta derivatives form differentiable parameter
families; their derivative fields are generated rather than supplied.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAtlas4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssembly4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Differentiable base and local reference assemblies. -/
structure ProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAtlasData
    (CountertermIndex Chart : Type*) (fold : Fold) where
  baseProductData : ProductThroatSpectralData
  baseTwist : CircleTwist
  baseNuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)
  base : ProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssemblyData
    CountertermIndex baseProductData fold baseTwist baseNuclear
  localProductData : Chart → ProductThroatSpectralData
  localTwist : Chart → CircleTwist
  localNuclear : Chart → NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)
  localAssembly : ∀ chart,
    ProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAssemblyData
      CountertermIndex (localProductData chart) fold (localTwist chart)
        (localNuclear chart)

namespace ProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAtlasData

/-- Public atlas checkpoint for differentiability and Schwarz reality. -/
theorem product_throat_reference_heat_duhamel_differentiable_canonical_schwarz_atlas_gate
    {CountertermIndex Chart : Type*} {fold : Fold}
    (data : ProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAtlasData
      (E := E) CountertermIndex Chart fold) :
    Differentiable Real
      (fun parameter => (data.base.continuation parameter).derivativeAtZero) ∧
    (∀ chart, Differentiable Real
      (fun parameter =>
        ((data.localAssembly chart).continuation parameter).derivativeAtZero)) ∧
    (∀ parameter,
      (data.base.continuation parameter).derivativeAtZero.im = 0) ∧
    (∀ chart parameter,
      ((data.localAssembly chart).continuation parameter).derivativeAtZero.im =
        0) := by
  exact ⟨data.base.zetaPrime_differentiable,
    fun chart => (data.localAssembly chart).zetaPrime_differentiable,
    data.base.product_throat_reference_heat_duhamel_differentiable_canonical_schwarz_gate.2.1,
    fun chart =>
      (data.localAssembly chart).product_throat_reference_heat_duhamel_differentiable_canonical_schwarz_gate.2.1⟩

end ProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAtlasData

end
end P0EFTJanusProgramPProductThroatReferenceHeatDuhamelDifferentiableCanonicalSchwarzAtlas4D
end JanusFormal
