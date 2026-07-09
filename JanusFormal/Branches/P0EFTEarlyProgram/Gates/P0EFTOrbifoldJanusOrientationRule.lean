import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldFluxOrientationRule
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldIntegerFluxLaw

namespace JanusFormal
namespace P0EFTOrbifoldJanusOrientationRule

set_option autoImplicit false

structure JanusOrientationRule where
  janusNormalFixed : Prop
  mirrorNormalFixed : Prop
  positiveSectorDouble : Prop
  negativeSectorSingle : Prop

def janusOrientationRuleDerived (r : JanusOrientationRule) : Prop :=
  r.janusNormalFixed /\
  r.mirrorNormalFixed /\
  r.positiveSectorDouble /\
  r.negativeSectorSingle

theorem janus_orientation_rule_supplies_flux_orientation_rule
    (r : JanusOrientationRule)
    (o : P0EFTOrbifoldFluxOrientationRule.OrbifoldFluxOrientationRule)
    (_hRule : janusOrientationRuleDerived r)
    (hJanus : o.janusNormalOrientationFixed)
    (hMirror : o.mirrorNormalOrientationFixed)
    (hPositive : o.positiveFluxSectorHasMultiplicityTwo)
    (hNegative : o.negativeFluxSectorHasMultiplicityOne) :
    P0EFTOrbifoldFluxOrientationRule.orientationRuleClosed o := by
  unfold P0EFTOrbifoldFluxOrientationRule.orientationRuleClosed
  exact And.intro hJanus
    (And.intro hMirror (And.intro hPositive hNegative))

theorem missing_positive_sector_blocks_janus_orientation_rule
    (r : JanusOrientationRule)
    (hMissing : Not r.positiveSectorDouble) :
    Not (janusOrientationRuleDerived r) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTOrbifoldJanusOrientationRule
end JanusFormal
