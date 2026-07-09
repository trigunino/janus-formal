import JanusFormal.Branches.JanusEarlyUniverseNativePlasma.Gates.P0EFTJanusM31SymmetricPowerBoundarySectorCandidateGate

namespace JanusFormal
namespace P0EFTJanusM31Sym4BoundaryStateLawDerivationAttemptGate

set_option autoImplicit false

structure M31Sym4BoundaryStateLawDerivationAttemptGate where
  M31SuppliesJanusLieDimension11 : Prop
  bosonicSymmetricPowerConstructionStandard : Prop
  dimSym4C11Equals1001 : Prop
  degree4SelectedByJanusBoundaryLaw : Prop
  dimSym4SetsAmin : Prop
  aminEntersPhotonRulerDynamics : Prop

def sym4NumberClosed
    (g : M31Sym4BoundaryStateLawDerivationAttemptGate) : Prop :=
  g.M31SuppliesJanusLieDimension11 /\
  g.bosonicSymmetricPowerConstructionStandard /\
  g.dimSym4C11Equals1001

def sym4NoFitStateLawClosed
    (g : M31Sym4BoundaryStateLawDerivationAttemptGate) : Prop :=
  sym4NumberClosed g /\
  g.degree4SelectedByJanusBoundaryLaw /\
  g.dimSym4SetsAmin /\
  g.aminEntersPhotonRulerDynamics

theorem sym4_number_without_boundary_law_not_no_fit_state_law
    (g : M31Sym4BoundaryStateLawDerivationAttemptGate)
    (hNoDegree : Not g.degree4SelectedByJanusBoundaryLaw) :
    Not (sym4NoFitStateLawClosed g) := by
  intro h
  exact hNoDegree h.right.left

end P0EFTJanusM31Sym4BoundaryStateLawDerivationAttemptGate
end JanusFormal
