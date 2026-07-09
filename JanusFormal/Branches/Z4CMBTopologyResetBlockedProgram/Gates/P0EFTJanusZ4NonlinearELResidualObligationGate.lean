import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4FullActionAssemblyTarget
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4NonlinearResidualFactorization

namespace JanusFormal
namespace P0EFTJanusZ4NonlinearELResidualObligationGate

set_option autoImplicit false

abbrev NonlinearResidualFactorization :=
  P0EFTJanusZ4NonlinearResidualFactorization.NonlinearResidualFactorization

structure NonlinearELResidualObligationGate where
  fullActionAssemblyScaffoldReady : Prop
  rankOneSourceRecovered : Prop
  residualPairFactorized : Prop
  determinantReciprocalWeightUsed : Prop
  commonObstructionExtracted : Prop
  commonObstructionVanishes : Prop
  nonlinearEulerLagrangeResidualVanishing : Prop

def nonlinearELResidualReducedToCommonObstruction
    (g : NonlinearELResidualObligationGate) : Prop :=
  g.fullActionAssemblyScaffoldReady /\
  g.rankOneSourceRecovered /\
  g.residualPairFactorized /\
  g.determinantReciprocalWeightUsed /\
  g.commonObstructionExtracted

def nonlinearELResidualClosed
    (g : NonlinearELResidualObligationGate) : Prop :=
  nonlinearELResidualReducedToCommonObstruction g /\
  g.commonObstructionVanishes /\
  g.nonlinearEulerLagrangeResidualVanishing

theorem common_obstruction_is_required_for_nonlinear_el_closure
    (g : NonlinearELResidualObligationGate)
    (hMissing : Not g.commonObstructionVanishes) :
    Not (nonlinearELResidualClosed g) := by
  intro h
  exact hMissing h.right.left

theorem factorization_transports_to_reduced_el_obligation
    (r : NonlinearResidualFactorization)
    (g : NonlinearELResidualObligationGate)
    (_hr :
      P0EFTJanusZ4NonlinearResidualFactorization.residualFactorizationReady r)
    (hgScaffold : g.fullActionAssemblyScaffoldReady)
    (hgRank : g.rankOneSourceRecovered)
    (hgFactorized : g.residualPairFactorized)
    (hgWeight : g.determinantReciprocalWeightUsed)
    (hgObstruction : g.commonObstructionExtracted) :
    nonlinearELResidualReducedToCommonObstruction g := by
  exact And.intro hgScaffold
    (And.intro hgRank
      (And.intro hgFactorized
        (And.intro hgWeight hgObstruction)))

end P0EFTJanusZ4NonlinearELResidualObligationGate
end JanusFormal
