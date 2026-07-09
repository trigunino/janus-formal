import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4FullActionAssemblyTarget

namespace JanusFormal
namespace P0EFTJanusZ4GaugeFixingVariationUniquenessGate

set_option autoImplicit false

structure GaugeFixingVariationUniquenessGate where
  gaugeFixingVariationInserted : Prop
  gaugeConditionDeclared : Prop
  residualGaugeFreedomClassified : Prop
  residualGaugeFreedomRemovedByJanusGeometry : Prop
  gaugeChoiceIndependentOfObservation : Prop
  gaugeFixedBoundaryVariationUnique : Prop

def gaugeFixingScaffoldReady (g : GaugeFixingVariationUniquenessGate) : Prop :=
  g.gaugeFixingVariationInserted /\
  g.gaugeConditionDeclared /\
  g.residualGaugeFreedomClassified /\
  g.gaugeChoiceIndependentOfObservation

def gaugeFixingVariationUnique (g : GaugeFixingVariationUniquenessGate) : Prop :=
  gaugeFixingScaffoldReady g /\
  g.residualGaugeFreedomRemovedByJanusGeometry /\
  g.gaugeFixedBoundaryVariationUnique

theorem missing_janus_geometry_gauge_removal_blocks_uniqueness
    (g : GaugeFixingVariationUniquenessGate)
    (hMissing : Not g.residualGaugeFreedomRemovedByJanusGeometry) :
    Not (gaugeFixingVariationUnique g) := by
  intro h
  exact hMissing h.right.left

theorem gauge_uniqueness_supplies_boundary_variation_uniqueness
    (g : GaugeFixingVariationUniquenessGate)
    (h : gaugeFixingVariationUnique g) :
    g.gaugeFixedBoundaryVariationUnique := by
  exact h.right.right

end P0EFTJanusZ4GaugeFixingVariationUniquenessGate
end JanusFormal
