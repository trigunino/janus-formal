namespace JanusFormal
namespace P0EFTCMBBackendSmoke

set_option autoImplicit false

structure CMBBackendSmoke where
  cambAvailable : Prop
  backendSolverRun : Prop
  janusBackgroundParametersInjected : Prop
  janusModifiedGravityTablesInjected : Prop
  uncompressedPlanckLikelihoodUsed : Prop

def backendSmokeReady (s : CMBBackendSmoke) : Prop :=
  s.cambAvailable /\
  s.backendSolverRun /\
  s.janusBackgroundParametersInjected

def directCMBLikelihoodReady (s : CMBBackendSmoke) : Prop :=
  backendSmokeReady s /\
  s.janusModifiedGravityTablesInjected /\
  s.uncompressedPlanckLikelihoodUsed

theorem camb_smoke_alone_does_not_close_direct_cmb
    (s : CMBBackendSmoke)
    (_hSmoke : backendSmokeReady s)
    (hMissingMG : Not s.janusModifiedGravityTablesInjected) :
    Not (directCMBLikelihoodReady s) := by
  intro h
  exact hMissingMG h.right.left

theorem camb_smoke_ready_from_backend_run
    (s : CMBBackendSmoke)
    (hCamb : s.cambAvailable)
    (hRun : s.backendSolverRun)
    (hJanusBg : s.janusBackgroundParametersInjected) :
    backendSmokeReady s := by
  exact And.intro hCamb (And.intro hRun hJanusBg)

end P0EFTCMBBackendSmoke
end JanusFormal
