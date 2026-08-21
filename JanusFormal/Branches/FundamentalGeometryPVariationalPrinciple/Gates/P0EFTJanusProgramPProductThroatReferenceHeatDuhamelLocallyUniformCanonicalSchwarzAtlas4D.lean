import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssembly4D

/-!
# Locally uniform ProductThroat reference atlas

The base chart and all local charts use uniformly dominated countable
rank-one series, so their long operator continuity is generated chartwise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatReferenceHeatDuhamelLocallyUniformCanonicalSchwarzAtlas4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssembly4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Locally uniform base and local reference assemblies. -/
structure ProductThroatReferenceHeatDuhamelLocallyUniformCanonicalSchwarzAtlasData
    (CountertermIndex Chart : Type*) (fold : Fold) where
  baseProductData : ProductThroatSpectralData
  baseTwist : CircleTwist
  baseNuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)
  base :
    ProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssemblyData
      CountertermIndex baseProductData fold baseTwist baseNuclear
  localProductData : Chart → ProductThroatSpectralData
  localTwist : Chart → CircleTwist
  localNuclear : Chart → NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)
  localAssembly : ∀ chart,
    ProductThroatReferenceHeatDuhamelLocallyUniformOperatorGeneratedCanonicalSchwarzAssemblyData
      CountertermIndex (localProductData chart) fold (localTwist chart)
        (localNuclear chart)

namespace ProductThroatReferenceHeatDuhamelLocallyUniformCanonicalSchwarzAtlasData

/-- Public chartwise continuity, Schwarz reality and connection checkpoint. -/
theorem product_throat_reference_heat_duhamel_locally_uniform_canonical_schwarz_atlas_gate
    {CountertermIndex Chart : Type*} {fold : Fold}
    (data : ProductThroatReferenceHeatDuhamelLocallyUniformCanonicalSchwarzAtlasData
      (E := E) CountertermIndex Chart fold) :
    (∀ parameter,
      ContinuousOn (data.base.operatorBoundary.longTime.operatorIntegrand parameter)
        (Set.Ici (1 : Real))) ∧
    (∀ chart parameter,
      ContinuousOn
        ((data.localAssembly chart).operatorBoundary.longTime.operatorIntegrand
          parameter) (Set.Ici (1 : Real))) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient
          data.base.toOperatorGeneratedCanonicalSchwarzAssembly.toRelativeHeatMellinZetaFamilyData.toZetaFamily
          parameter =
        -(data.base.toOperatorGeneratedCanonicalSchwarzAssembly.logarithmicTrace
          parameter : Complex)) ∧
    (∀ chart parameter,
      relativeZetaConnectionCoefficient
          (data.localAssembly chart).toOperatorGeneratedCanonicalSchwarzAssembly.toRelativeHeatMellinZetaFamilyData.toZetaFamily
          parameter =
        -((data.localAssembly chart).toOperatorGeneratedCanonicalSchwarzAssembly.logarithmicTrace
          parameter : Complex)) := by
  exact
    ⟨data.base.product_throat_reference_heat_duhamel_locally_uniform_operator_generated_canonical_schwarz_gate.1,
      fun chart =>
        (data.localAssembly chart).product_throat_reference_heat_duhamel_locally_uniform_operator_generated_canonical_schwarz_gate.1,
      data.base.product_throat_reference_heat_duhamel_locally_uniform_operator_generated_canonical_schwarz_gate.2.2,
      fun chart =>
        (data.localAssembly chart).product_throat_reference_heat_duhamel_locally_uniform_operator_generated_canonical_schwarz_gate.2.2⟩

end ProductThroatReferenceHeatDuhamelLocallyUniformCanonicalSchwarzAtlasData

end
end P0EFTJanusProgramPProductThroatReferenceHeatDuhamelLocallyUniformCanonicalSchwarzAtlas4D
end JanusFormal
