namespace JanusFormal
namespace P0EFTJanusZ2CoverMasterLagrangianSkeletonGate

set_option autoImplicit false

structure Z2CoverMasterLagrangianSkeletonGate where
  activeCoreJanusZ2Cover : Prop
  masterActionOnCoverDeclared : Prop
  coverEinsteinHilbertBlockDeclared : Prop
  coverMatterBlockDeclared : Prop
  tauZ2PullbackMatterBlockDeclared : Prop
  sigmaBoundaryBlockDeclaredAsPartOfMasterAction : Prop
  plusSectorNotIndependentAction : Prop
  minusSectorNotIndependentAction : Prop
  projectedMeasureFactorsDeclared : Prop
  orientationSignChannelDeclared : Prop
  negativeMassAsProjectionSignTarget : Prop
  negativeThermodynamicDensityNotPostulated : Prop
  rhoEffCollapseForbidden : Prop
  z4MonodromyForbidden : Prop
  observationalFitForbidden : Prop
  lagrangianDensityExplicit : Prop
  variationDerived : Prop

def masterLagrangianSkeletonDeclared
    (g : Z2CoverMasterLagrangianSkeletonGate) : Prop :=
  g.activeCoreJanusZ2Cover /\
  g.masterActionOnCoverDeclared /\
  g.coverEinsteinHilbertBlockDeclared /\
  g.coverMatterBlockDeclared /\
  g.tauZ2PullbackMatterBlockDeclared /\
  g.sigmaBoundaryBlockDeclaredAsPartOfMasterAction /\
  g.plusSectorNotIndependentAction /\
  g.minusSectorNotIndependentAction /\
  g.projectedMeasureFactorsDeclared /\
  g.orientationSignChannelDeclared /\
  g.negativeMassAsProjectionSignTarget /\
  g.negativeThermodynamicDensityNotPostulated /\
  g.rhoEffCollapseForbidden /\
  g.z4MonodromyForbidden /\
  g.observationalFitForbidden

theorem skeleton_forbids_effective_shortcuts
    (g : Z2CoverMasterLagrangianSkeletonGate)
    (h : masterLagrangianSkeletonDeclared g) :
    g.plusSectorNotIndependentAction /\
      g.minusSectorNotIndependentAction /\
      g.negativeThermodynamicDensityNotPostulated /\
      g.rhoEffCollapseForbidden := by
  exact And.intro h.right.right.right.right.right.right.left
    (And.intro h.right.right.right.right.right.right.right.left
      (And.intro h.right.right.right.right.right.right.right.right.right.right.right.left
        h.right.right.right.right.right.right.right.right.right.right.right.right.left))

theorem explicit_variation_is_still_required_for_closure
    (g : Z2CoverMasterLagrangianSkeletonGate)
    (hExplicit : g.lagrangianDensityExplicit)
    (hVariation : g.variationDerived) :
    g.lagrangianDensityExplicit /\ g.variationDerived := by
  exact And.intro hExplicit hVariation

end P0EFTJanusZ2CoverMasterLagrangianSkeletonGate
end JanusFormal
