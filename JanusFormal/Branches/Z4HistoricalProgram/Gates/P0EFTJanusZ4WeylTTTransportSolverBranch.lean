import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4WeylTTTransportDerivation

namespace JanusFormal
namespace P0EFTJanusZ4WeylTTTransportSolverBranch

set_option autoImplicit false

structure WeylTTTransportSolverBranch where
  mirrorEvenWeylSourceIntegrated : Prop
  ttClockWardRegularizerIntegrated : Prop
  spectraExported : Prop
  solverNumericsModified : Prop
  planckValidationClaimed : Prop

def branchReady (b : WeylTTTransportSolverBranch) : Prop :=
  b.mirrorEvenWeylSourceIntegrated /\
  b.ttClockWardRegularizerIntegrated /\
  b.spectraExported

theorem branch_integrates_weyl_and_clock_terms
    (b : WeylTTTransportSolverBranch)
    (h : branchReady b) :
    b.mirrorEvenWeylSourceIntegrated /\ b.ttClockWardRegularizerIntegrated := by
  exact And.intro h.left h.right.left

theorem branch_does_not_claim_planck
    (b : WeylTTTransportSolverBranch)
    (_h : branchReady b)
    (hNoClaim : Not b.planckValidationClaimed) :
    Not b.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4WeylTTTransportSolverBranch
end JanusFormal
