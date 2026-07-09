import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4ActionVariationGate
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4LinearizedActionVariation
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4DeterminantMeasureVariation
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4BoundaryVariationClosure

namespace JanusFormal
namespace P0EFTJanusZ4FullActionAssemblyTarget

set_option autoImplicit false

structure FullActionAssemblyTarget where
  bulkPalatiniVariationDeclared : Prop
  sourceVariationInserted : Prop
  determinantMeasureVariationInserted : Prop
  boundaryVariationInserted : Prop
  gaugeFixingVariationInserted : Prop
  z4RankOneSourceRecovered : Prop
  nonlinearEulerLagrangeResidualVanishing : Prop

def fullActionAssemblyScaffoldReady (a : FullActionAssemblyTarget) : Prop :=
  a.bulkPalatiniVariationDeclared /\
  a.sourceVariationInserted /\
  a.determinantMeasureVariationInserted /\
  a.boundaryVariationInserted /\
  a.gaugeFixingVariationInserted /\
  a.z4RankOneSourceRecovered

def fullActionVariationClosedByAssembly (a : FullActionAssemblyTarget) : Prop :=
  fullActionAssemblyScaffoldReady a /\
  a.nonlinearEulerLagrangeResidualVanishing

theorem assembly_scaffold_requires_rank_one_source
    (a : FullActionAssemblyTarget)
    (h : fullActionAssemblyScaffoldReady a) :
    a.z4RankOneSourceRecovered := by
  exact h.right.right.right.right.right

theorem assembly_scaffold_does_not_close_full_variation
    (a : FullActionAssemblyTarget)
    (_h : fullActionAssemblyScaffoldReady a)
    (hMissing : Not a.nonlinearEulerLagrangeResidualVanishing) :
    Not (fullActionVariationClosedByAssembly a) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4FullActionAssemblyTarget
end JanusFormal
