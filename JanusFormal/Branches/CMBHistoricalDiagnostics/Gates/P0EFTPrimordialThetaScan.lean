namespace JanusFormal
namespace P0EFTPrimordialThetaScan

set_option autoImplicit false

structure PrimordialThetaScan where
  wardConstrained : Prop
  thetaGridRun : Prop
  acceptedThetaFound : Prop
  thetaTopologicallyDerived : Prop

def thetaWindowPhenomenologicallyOpen (s : PrimordialThetaScan) : Prop :=
  s.wardConstrained /\
  s.thetaGridRun /\
  s.acceptedThetaFound

def thetaNoFitReady (s : PrimordialThetaScan) : Prop :=
  thetaWindowPhenomenologicallyOpen s /\
  s.thetaTopologicallyDerived

theorem accepted_theta_requires_topological_derivation
    (s : PrimordialThetaScan)
    (_hOpen : thetaWindowPhenomenologicallyOpen s)
    (hMissing : Not s.thetaTopologicallyDerived) :
    Not (thetaNoFitReady s) := by
  intro h
  exact hMissing h.right

end P0EFTPrimordialThetaScan
end JanusFormal
