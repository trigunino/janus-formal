namespace JanusFormal
namespace P0EFTJanusZ2CoverMasterProjectedEquationsGate

set_option autoImplicit false

structure Z2CoverMasterProjectedEquationsGate where
  activeCoreJanusZ2Cover : Prop
  singleMasterActionInput : Prop
  plusEquationProjected : Prop
  minusEquationProjected : Prop
  selfSectorSignPositive : Prop
  crossSectorSignNegative : Prop
  negativeSignFromProjectionOrientation : Prop
  negativeThermodynamicDensityNotPostulated : Prop
  rhoEffShortcutForbidden : Prop
  z4MonodromyForbidden : Prop
  sigmaBoundarySourceCarried : Prop
  sigmaJunctionNotYetDerived : Prop
  pairedBianchiNotYetDerived : Prop

def projectedEquationsReady (g : Z2CoverMasterProjectedEquationsGate) : Prop :=
  g.activeCoreJanusZ2Cover /\
  g.singleMasterActionInput /\
  g.plusEquationProjected /\
  g.minusEquationProjected /\
  g.selfSectorSignPositive /\
  g.crossSectorSignNegative /\
  g.negativeSignFromProjectionOrientation /\
  g.negativeThermodynamicDensityNotPostulated /\
  g.rhoEffShortcutForbidden /\
  g.z4MonodromyForbidden /\
  g.sigmaBoundarySourceCarried

theorem cross_sign_is_projection_not_negative_density
    (g : Z2CoverMasterProjectedEquationsGate)
    (h : projectedEquationsReady g) :
    g.crossSectorSignNegative /\
      g.negativeSignFromProjectionOrientation /\
      g.negativeThermodynamicDensityNotPostulated /\
      g.rhoEffShortcutForbidden := by
  exact And.intro h.right.right.right.right.right.left
    (And.intro h.right.right.right.right.right.right.left
      (And.intro h.right.right.right.right.right.right.right.left
        h.right.right.right.right.right.right.right.right.left))

theorem projected_equations_do_not_close_junction_or_bianchi
    (g : Z2CoverMasterProjectedEquationsGate)
    (hSigma : g.sigmaJunctionNotYetDerived)
    (hBianchi : g.pairedBianchiNotYetDerived) :
    g.sigmaJunctionNotYetDerived /\ g.pairedBianchiNotYetDerived := by
  exact And.intro hSigma hBianchi

end P0EFTJanusZ2CoverMasterProjectedEquationsGate
end JanusFormal
