import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4PolarizationSourceScan
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4PhotonBaryonSourceClosure

namespace JanusFormal
namespace P0EFTJanusZ4PolarizationHierarchyClosure

set_option autoImplicit false

structure PolarizationHierarchyClosure where
  thomsonQuadrupoleSourceDeclared : Prop
  photonQuadrupoleCoupled : Prop
  eModeSpin2ProjectionUsed : Prop
  z4PolarizationSourceResidualDeclared : Prop
  uniqueAlgebraicSolution : Prop
  substitutedResidualsVanish : Prop
  actionCoefficientsDerived : Prop

def polarizationHierarchyScaffoldReady (p : PolarizationHierarchyClosure) : Prop :=
  p.thomsonQuadrupoleSourceDeclared /\
  p.photonQuadrupoleCoupled /\
  p.eModeSpin2ProjectionUsed /\
  p.z4PolarizationSourceResidualDeclared

def polarizationHierarchyAlgebraicallyClosed (p : PolarizationHierarchyClosure) : Prop :=
  polarizationHierarchyScaffoldReady p /\
  p.uniqueAlgebraicSolution /\
  p.substitutedResidualsVanish

def polarizationHierarchyPhysicalReady (p : PolarizationHierarchyClosure) : Prop :=
  polarizationHierarchyAlgebraicallyClosed p /\ p.actionCoefficientsDerived

theorem polarization_scaffold_does_not_close_physics
    (p : PolarizationHierarchyClosure)
    (_h : polarizationHierarchyScaffoldReady p)
    (hMissing : Not p.actionCoefficientsDerived) :
    Not (polarizationHierarchyPhysicalReady p) := by
  intro h
  exact hMissing h.right

theorem polarization_algebraic_closure_does_not_close_physics
    (p : PolarizationHierarchyClosure)
    (_h : polarizationHierarchyAlgebraicallyClosed p)
    (hMissing : Not p.actionCoefficientsDerived) :
    Not (polarizationHierarchyPhysicalReady p) := by
  intro h
  exact hMissing h.right

theorem photon_baryon_action_coefficients_feed_polarization_lock
    (p : PolarizationHierarchyClosure)
    (b : P0EFTJanusZ4PhotonBaryonSourceClosure.PhotonBaryonSourceClosure)
    (hAlg : polarizationHierarchyAlgebraicallyClosed p)
    (hAction : b.coefficientsFromFullZ4Action)
    (hTransport : b.coefficientsFromFullZ4Action -> p.actionCoefficientsDerived) :
    polarizationHierarchyPhysicalReady p := by
  exact And.intro hAlg (hTransport hAction)

end P0EFTJanusZ4PolarizationHierarchyClosure
end JanusFormal
