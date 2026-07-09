namespace JanusFormal
namespace P0EFTPrimordialRoutesDecision

set_option autoImplicit false

structure PrimordialRoutesDecision where
  twoModeRejected : Prop
  nonlocalVisibilityRejectedAsSufficient : Prop
  visibilityImprovesTotal : Prop
  lowEStillUnfixed : Prop
  polarizationSourceShapeDerived : Prop

def testedRoutesExcludedAsSufficient (d : PrimordialRoutesDecision) : Prop :=
  d.twoModeRejected /\
  d.nonlocalVisibilityRejectedAsSufficient /\
  d.lowEStillUnfixed

def nextViableRouteReady (d : PrimordialRoutesDecision) : Prop :=
  testedRoutesExcludedAsSufficient d /\
  d.polarizationSourceShapeDerived

theorem routes_excluded_require_polarization_shape
    (d : PrimordialRoutesDecision)
    (hTwo : d.twoModeRejected)
    (hVis : d.nonlocalVisibilityRejectedAsSufficient)
    (hLowE : d.lowEStillUnfixed) :
    testedRoutesExcludedAsSufficient d := by
  exact And.intro hTwo (And.intro hVis hLowE)

theorem missing_polarization_shape_blocks_next_route
    (d : PrimordialRoutesDecision)
    (_hExcluded : testedRoutesExcludedAsSufficient d)
    (hMissing : Not d.polarizationSourceShapeDerived) :
    Not (nextViableRouteReady d) := by
  intro h
  exact hMissing h.right

end P0EFTPrimordialRoutesDecision
end JanusFormal
