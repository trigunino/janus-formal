import JanusFormal.Branches.P0EarlyProgram.Gates.P0DynamicSourceObligations

namespace JanusFormal
namespace P0BridgeUniquenessObligations

open P0DynamicSourceObligations

set_option autoImplicit false

structure BridgeProblem (Bridge : Type) where
  admissible : Bridge -> Prop
  eulerLagrangeSolution : Bridge -> Prop
  transportCompatible : Bridge -> Prop

def bridgeClosed {Bridge : Type} (p : BridgeProblem Bridge) (b : Bridge) : Prop :=
  p.admissible b /\ p.eulerLagrangeSolution b /\ p.transportCompatible b

def bridgeUnique {Bridge : Type} (p : BridgeProblem Bridge) : Prop :=
  ExistsUnique (bridgeClosed p)

structure BridgeClosureCertificate {Bridge : Type} (p : BridgeProblem Bridge) where
  candidate : Bridge
  candidateClosed : bridgeClosed p candidate
  allClosedEqualCandidate : forall b, bridgeClosed p b -> b = candidate

def bridgeUniquenessFromCertificate
    {Bridge : Type}
    (p : BridgeProblem Bridge)
    (_c : BridgeClosureCertificate p) : BridgeUniqueness :=
  { bridgeEquationWritten := True
    uniqueBridgeSolution := bridgeUnique p
    sameBridgeTransportLaw := True }

theorem certificate_implies_unique_bridge
    {Bridge : Type}
    (p : BridgeProblem Bridge)
    (c : BridgeClosureCertificate p) :
    bridgeUnique p := by
  exact ⟨c.candidate, c.candidateClosed, c.allClosedEqualCandidate⟩

theorem certificate_gives_bridge_uniqueness_obligation
    {Bridge : Type}
    (p : BridgeProblem Bridge)
    (c : BridgeClosureCertificate p) :
    (bridgeUniquenessFromCertificate p c).uniqueBridgeSolution := by
  exact certificate_implies_unique_bridge p c

theorem missing_certificate_blocks_this_route
    {Bridge : Type}
    (p : BridgeProblem Bridge)
    (hMissing : Not (bridgeUnique p)) :
    Not (Nonempty (BridgeClosureCertificate p)) := by
  intro hCert
  rcases hCert with ⟨c⟩
  exact hMissing (certificate_implies_unique_bridge p c)

structure TwoBridgeCounterexample {Bridge : Type} (p : BridgeProblem Bridge) where
  left : Bridge
  right : Bridge
  leftClosed : bridgeClosed p left
  rightClosed : bridgeClosed p right
  distinct : left ≠ right

theorem two_closed_bridges_block_uniqueness
    {Bridge : Type}
    (p : BridgeProblem Bridge)
    (c : TwoBridgeCounterexample p) :
    Not (bridgeUnique p) := by
  intro hUnique
  rcases hUnique with ⟨b0, _hb0, huniq⟩
  have hLeft : c.left = b0 := huniq c.left c.leftClosed
  have hRight : c.right = b0 := huniq c.right c.rightClosed
  exact c.distinct (hLeft.trans hRight.symm)

theorem admissibility_alone_does_not_define_closure
    {Bridge : Type}
    (p : BridgeProblem Bridge)
    (b : Bridge)
    (_h : p.admissible b)
    (hNoEL : Not (p.eulerLagrangeSolution b)) :
    Not (bridgeClosed p b) := by
  intro hClosed
  exact hNoEL hClosed.right.left

end P0BridgeUniquenessObligations
end JanusFormal
