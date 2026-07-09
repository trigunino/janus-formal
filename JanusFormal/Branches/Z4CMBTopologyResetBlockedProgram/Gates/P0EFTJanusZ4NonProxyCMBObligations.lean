namespace JanusFormal
namespace P0EFTJanusZ4NonProxyCMBObligations

set_option autoImplicit false

structure NonProxyCMBObligations where
  z4BackgroundEquationDerived : Prop
  z4ScalarPerturbationsDerived : Prop
  photonBaryonHierarchyDerived : Prop
  neutrinoHierarchyDerived : Prop
  recombinationVisibilityDerived : Prop
  lineOfSightSourcesDerived : Prop
  lensingSourcesDerived : Prop
  planckLikelihoodAdapterReady : Prop

def nonProxyCMBReady (o : NonProxyCMBObligations) : Prop :=
  o.z4BackgroundEquationDerived /\
  o.z4ScalarPerturbationsDerived /\
  o.photonBaryonHierarchyDerived /\
  o.neutrinoHierarchyDerived /\
  o.recombinationVisibilityDerived /\
  o.lineOfSightSourcesDerived /\
  o.lensingSourcesDerived /\
  o.planckLikelihoodAdapterReady

theorem missing_planck_adapter_blocks_nonproxy_cmb
    (o : NonProxyCMBObligations)
    (hMissing : Not o.planckLikelihoodAdapterReady) :
    Not (nonProxyCMBReady o) := by
  intro h
  exact hMissing h.right.right.right.right.right.right.right

end P0EFTJanusZ4NonProxyCMBObligations
end JanusFormal
