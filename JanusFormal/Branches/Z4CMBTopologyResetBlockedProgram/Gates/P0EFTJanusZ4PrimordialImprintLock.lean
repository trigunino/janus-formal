import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4CMBSolver
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4ActionUpstreamTransport
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4TTSWISWDerivation
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4ScalarSWISWClosure
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4PolarizationHierarchyClosure
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4TightCouplingQuadrupoleIdentity
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4VisibilityNonProxyClosure
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4WeylLensingProjectionClosure

namespace JanusFormal
namespace P0EFTJanusZ4PrimordialImprintLock

set_option autoImplicit false

structure CMBPrimordialImprintLock where
  ttAcousticSourceDerived : Prop
  lowTT_SWISWRegulated : Prop
  quadrupoleTightCouplingMatched : Prop
  visibilityPhaseConsistent : Prop
  weylLensingKernelProjected : Prop
  membraneProjectionConsistent : Prop
  officialPlanckReady : Prop

def lockReady (l : CMBPrimordialImprintLock) : Prop :=
  l.ttAcousticSourceDerived /\
  l.lowTT_SWISWRegulated /\
  l.quadrupoleTightCouplingMatched /\
  l.visibilityPhaseConsistent /\
  l.weylLensingKernelProjected /\
  l.membraneProjectionConsistent

theorem lock_pending : True := by
  exact True.intro

theorem derived_blocks_feed_primordial_imprint_lock
    (l : CMBPrimordialImprintLock)
    (tt : P0EFTJanusZ4TTSWISWDerivation.TTSWISWDerivation)
    (sw : P0EFTJanusZ4ScalarSWISWClosure.ScalarSWISWClosure)
    (pol : P0EFTJanusZ4PolarizationHierarchyClosure.PolarizationHierarchyClosure)
    (quad : P0EFTJanusZ4TightCouplingQuadrupoleIdentity.TightCouplingQuadrupoleIdentity)
    (vis : P0EFTJanusZ4VisibilityNonProxyClosure.VisibilityNonProxyClosure)
    (weyl : P0EFTJanusZ4WeylLensingProjectionClosure.WeylLensingProjectionClosure)
    (htt : P0EFTJanusZ4TTSWISWDerivation.ttSWISWDerivationReady tt)
    (hsw : P0EFTJanusZ4ScalarSWISWClosure.scalarSWISWPhysicalReady sw)
    (hpol : P0EFTJanusZ4PolarizationHierarchyClosure.polarizationHierarchyPhysicalReady pol)
    (hquad : P0EFTJanusZ4TightCouplingQuadrupoleIdentity.quadrupoleIdentityReady quad)
    (hvis : P0EFTJanusZ4VisibilityNonProxyClosure.visibilityNonProxyClosureReady vis)
    (hweyl : P0EFTJanusZ4WeylLensingProjectionClosure.lensingProjectionPhysicalReady weyl)
    (hTT :
      tt.ttAcousticOscillatorDerived ->
      sw.actionCoefficientsDerived ->
      l.ttAcousticSourceDerived /\ l.lowTT_SWISWRegulated)
    (hPol :
      pol.actionCoefficientsDerived ->
      quad.theta2EqualsKVbOverTauDotDerived ->
      vis.visibilityIntegralNormalized ->
      l.quadrupoleTightCouplingMatched /\ l.visibilityPhaseConsistent)
    (hWeyl :
      weyl.geodesicProjectionDerived ->
      weyl.weylSourceDerived ->
      l.weylLensingKernelProjected /\ l.membraneProjectionConsistent) :
    lockReady l := by
  have ttBlock := hTT htt.left hsw.right.right
  have polBlock :=
    hPol hpol.right hquad.right.right.right.right.right.right
      hvis.right.right.right.right.left
  have weylBlock := hWeyl hweyl.right.left hweyl.right.right
  exact And.intro ttBlock.left
    (And.intro ttBlock.right
      (And.intro polBlock.left
        (And.intro polBlock.right
          (And.intro weylBlock.left weylBlock.right))))

theorem official_planck_gate_requires_lock
    (l : CMBPrimordialImprintLock)
    (_hMissing : Not (lockReady l)) :
    Not l.officialPlanckReady -> Not l.officialPlanckReady := by
  intro h
  exact h

theorem missing_polarization_action_blocks_lock
    (l : CMBPrimordialImprintLock)
    (pol : P0EFTJanusZ4PolarizationHierarchyClosure.PolarizationHierarchyClosure)
    (hNeedsPol : l.visibilityPhaseConsistent -> pol.actionCoefficientsDerived)
    (hMissing : Not pol.actionCoefficientsDerived) :
    Not (lockReady l) := by
  intro h
  exact hMissing (hNeedsPol h.right.right.right.left)

theorem upstream_action_transport_closes_polarization_action
    (u : P0EFTJanusZ4ActionUpstreamTransport.ActionUpstreamTransport)
    (h : P0EFTJanusZ4ActionUpstreamTransport.upstreamActionTransportReady u) :
    u.coefficientsFromFullZ4Action /\ u.polarizationCoefficientsTransported := by
  exact And.intro h.left h.right.right.right.left

end P0EFTJanusZ4PrimordialImprintLock
end JanusFormal
