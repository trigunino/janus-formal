import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssembly4D

/-!
# Continuous-basepoint differentiable ProductThroat atlas
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAtlas4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssembly4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Base and local continuous-basepoint assemblies. -/
structure ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAtlasData
    (CountertermIndex Chart : Type*) (fold : Fold) where
  baseProductData : ProductThroatSpectralData
  baseTwist : CircleTwist
  baseNuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)
  base :
    ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssemblyData
      CountertermIndex baseProductData fold baseTwist baseNuclear
  localProductData : Chart → ProductThroatSpectralData
  localTwist : Chart → CircleTwist
  localNuclear : Chart → NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)
  localAssembly : ∀ chart,
    ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAssemblyData
      CountertermIndex (localProductData chart) fold (localTwist chart)
        (localNuclear chart)

namespace ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAtlasData

/-- Public continuous-basepoint atlas checkpoint. -/
theorem product_throat_reference_heat_duhamel_continuous_basepoint_differentiable_canonical_schwarz_atlas_gate
    {CountertermIndex Chart : Type*} {fold : Fold}
    (data :
      ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAtlasData
        (E := E) CountertermIndex Chart fold) :
    (∀ parameter,
      ContinuousOn
        (fun time => time⁻¹ *
          (extendedHeatTrace data.baseNuclear parameter time -
            counterterm data.base.finitePart.finiteCounterterm.variation
              parameter time))
        (Set.Ioo (0 : Real) 1)) ∧
    (∀ chart parameter,
      ContinuousOn
        (fun time => time⁻¹ *
          (extendedHeatTrace (data.localNuclear chart) parameter time -
            counterterm
              (data.localAssembly chart).finitePart.finiteCounterterm.variation
              parameter time))
        (Set.Ioo (0 : Real) 1)) ∧
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
    ⟨data.base.finitePart.toCanonicalWeightContinuousBasepointFinitePartFamilyFrontend
        |>.toContinuousBasepointFinitePartFamilyFrontend.shortTime
        |>.toContinuousBasepoint.weightedRemainder_continuousOn,
      fun chart =>
        (data.localAssembly chart).finitePart.toCanonicalWeightContinuousBasepointFinitePartFamilyFrontend
          |>.toContinuousBasepointFinitePartFamilyFrontend.shortTime
          |>.toContinuousBasepoint.weightedRemainder_continuousOn,
      data.base.zetaPrime_differentiable,
      fun chart => (data.localAssembly chart).zetaPrime_differentiable,
      data.base.product_throat_reference_heat_duhamel_continuous_basepoint_differentiable_canonical_schwarz_gate.2.2,
      fun chart =>
        (data.localAssembly chart).product_throat_reference_heat_duhamel_continuous_basepoint_differentiable_canonical_schwarz_gate.2.2⟩

end ProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAtlasData

end
end P0EFTJanusProgramPProductThroatReferenceHeatDuhamelContinuousBasepointDifferentiableCanonicalSchwarzAtlas4D
end JanusFormal
