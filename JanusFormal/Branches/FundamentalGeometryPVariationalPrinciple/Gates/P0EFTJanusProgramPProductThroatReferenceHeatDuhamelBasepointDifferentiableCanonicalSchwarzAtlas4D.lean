import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssembly4D

/-!
# Basepoint-generated differentiable ProductThroat atlas
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAtlas4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssembly4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Base and local references generated from one short-time basepoint per
chart. -/
structure ProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAtlasData
    (CountertermIndex Chart : Type*) (fold : Fold) where
  baseProductData : ProductThroatSpectralData
  baseTwist : CircleTwist
  baseNuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)
  base :
    ProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssemblyData
      CountertermIndex baseProductData fold baseTwist baseNuclear
  localProductData : Chart → ProductThroatSpectralData
  localTwist : Chart → CircleTwist
  localNuclear : Chart → NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)
  localAssembly : ∀ chart,
    ProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAssemblyData
      CountertermIndex (localProductData chart) fold (localTwist chart)
        (localNuclear chart)

namespace ProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAtlasData

/-- Public strongest generated atlas checkpoint. -/
theorem product_throat_reference_heat_duhamel_basepoint_differentiable_canonical_schwarz_atlas_gate
    {CountertermIndex Chart : Type*} {fold : Fold}
    (data :
      ProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAtlasData
        (E := E) CountertermIndex Chart fold) :
    (∀ parameter,
      Integrable (data.base.finitePart.shortTimeBasepoint.weightedRemainder
        parameter) (volume.restrict (Set.Ioo (0 : Real) 1))) ∧
    (∀ chart parameter,
      Integrable
        ((data.localAssembly chart).finitePart.shortTimeBasepoint.weightedRemainder
          parameter) (volume.restrict (Set.Ioo (0 : Real) 1))) ∧
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
  exact
    ⟨data.base.product_throat_reference_heat_duhamel_basepoint_differentiable_canonical_schwarz_gate.1,
      fun chart =>
        (data.localAssembly chart).product_throat_reference_heat_duhamel_basepoint_differentiable_canonical_schwarz_gate.1,
      data.base.zetaPrime_differentiable,
      fun chart => (data.localAssembly chart).zetaPrime_differentiable,
      data.base.product_throat_reference_heat_duhamel_basepoint_differentiable_canonical_schwarz_gate.2.2,
      fun chart =>
        (data.localAssembly chart).product_throat_reference_heat_duhamel_basepoint_differentiable_canonical_schwarz_gate.2.2⟩

end ProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAtlasData

end
end P0EFTJanusProgramPProductThroatReferenceHeatDuhamelBasepointDifferentiableCanonicalSchwarzAtlas4D
end JanusFormal
