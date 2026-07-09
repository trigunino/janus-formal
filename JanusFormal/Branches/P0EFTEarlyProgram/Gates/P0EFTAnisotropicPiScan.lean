import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTCosmologicalMiniScan

namespace JanusFormal
namespace P0EFTAnisotropicPiScan

set_option autoImplicit false

structure AnisotropicPiScan where
  piFriedmannChannelDefined : Prop
  piMuChannelDefined : Prop
  anisotropicBranchesScored : Prop
  physicalAnisotropicBranchFound : Prop
  unitAmplitudeCriterionPassed : Prop
  piDerivedFromVlasovMomentTwo : Prop

def anisotropicScanReady (s : AnisotropicPiScan) : Prop :=
  s.piFriedmannChannelDefined /\
  s.piMuChannelDefined /\
  s.anisotropicBranchesScored

def anisotropicNoFitCandidateReady (s : AnisotropicPiScan) : Prop :=
  anisotropicScanReady s /\
  s.physicalAnisotropicBranchFound /\
  s.unitAmplitudeCriterionPassed /\
  s.piDerivedFromVlasovMomentTwo

theorem anisotropic_pi_scan_is_structured
    (s : AnisotropicPiScan)
    (hF : s.piFriedmannChannelDefined)
    (hMu : s.piMuChannelDefined)
    (hScan : s.anisotropicBranchesScored) :
    anisotropicScanReady s := by
  exact And.intro hF (And.intro hMu hScan)

theorem underived_pi_blocks_no_fit_candidate
    (s : AnisotropicPiScan)
    (hMissing : Not s.piDerivedFromVlasovMomentTwo) :
    Not (anisotropicNoFitCandidateReady s) := by
  intro h
  exact hMissing h.right.right.right

end P0EFTAnisotropicPiScan
end JanusFormal
