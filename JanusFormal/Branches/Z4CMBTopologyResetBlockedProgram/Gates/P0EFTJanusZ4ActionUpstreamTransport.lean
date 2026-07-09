import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4PhotonBaryonSourceClosure
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4ScalarActionDerivation
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4WeylLensingSourceTarget
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4PhysicalClosureTriad

namespace JanusFormal
namespace P0EFTJanusZ4ActionUpstreamTransport

set_option autoImplicit false

structure ActionUpstreamTransport where
  coefficientsFromFullZ4Action : Prop
  scalarActionDerivedReady : Prop
  sourceCoefficientsDerived : Prop
  polarizationCoefficientsTransported : Prop
  scalarCoefficientsTransported : Prop
  weylLensingCoefficientsTransported : Prop
  planckValidationClaimed : Prop

def upstreamActionTransportReady (u : ActionUpstreamTransport) : Prop :=
  u.coefficientsFromFullZ4Action /\
  u.scalarActionDerivedReady /\
  u.sourceCoefficientsDerived /\
  u.polarizationCoefficientsTransported /\
  u.scalarCoefficientsTransported /\
  u.weylLensingCoefficientsTransported

theorem upstream_transport_gives_physical_triad
    (u : ActionUpstreamTransport)
    (h : upstreamActionTransportReady u) :
    P0EFTJanusZ4PhysicalClosureTriad.cmbZ4PhysicalTriadReady
      { polarizationHierarchyPhysicalReady := u.coefficientsFromFullZ4Action /\ u.polarizationCoefficientsTransported
        scalarSWISWPhysicalReady := u.scalarActionDerivedReady /\ u.scalarCoefficientsTransported
        lensingProjectionPhysicalReady := u.sourceCoefficientsDerived /\ u.weylLensingCoefficientsTransported } := by
  exact And.intro (And.intro h.left h.right.right.right.left)
    (And.intro
      (And.intro h.right.left h.right.right.right.right.left)
      (And.intro h.right.right.left h.right.right.right.right.right))

theorem upstream_transport_does_not_claim_planck
    (u : ActionUpstreamTransport)
    (_h : upstreamActionTransportReady u)
    (hNoClaim : Not u.planckValidationClaimed) :
    Not u.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4ActionUpstreamTransport
end JanusFormal
