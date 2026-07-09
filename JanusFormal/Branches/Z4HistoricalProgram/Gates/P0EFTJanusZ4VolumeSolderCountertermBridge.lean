import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTBoundaryIdentityObstruction
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTBoundaryVolumeSolderClosure

namespace JanusFormal
namespace P0EFTJanusZ4VolumeSolderCountertermBridge

set_option autoImplicit false

abbrev EFTIdentityCounterterm :=
  P0EFTBoundaryIdentityObstruction.EFTIdentityCounterterm

abbrev VolumeSolderSource :=
  P0EFTBoundaryVolumeSolderClosure.VolumeSolderSource

def volumeSolderDerivesIdentityCounterterm
    (v : VolumeSolderSource)
    (e : EFTIdentityCounterterm) : Prop :=
  P0EFTBoundaryVolumeSolderClosure.volumeSourceClosesIdentity v /\
  e.scalarBoundaryCountertermAdded /\
  e.exactCountertermCancelsIdentityResidue /\
  e.countertermDerivedFromJanusInvariant /\
  e.algebraicClosureRestored

theorem volume_solder_counterterm_closes_eft_identity_branch
    (v : VolumeSolderSource)
    (e : EFTIdentityCounterterm)
    (h : volumeSolderDerivesIdentityCounterterm v e) :
    e.countertermDerivedFromJanusInvariant /\
      P0EFTBoundaryIdentityObstruction.eftBranchClosesOnlyIfAccepted e := by
  exact And.intro h.right.right.right.left
    (And.intro h.right.left
      (And.intro h.right.right.left h.right.right.right.right))

theorem missing_volume_lambda_geometry_blocks_counterterm_bridge
    (v : VolumeSolderSource)
    (e : EFTIdentityCounterterm)
    (hMissing : Not v.lambdaFixedByJanusGeometry) :
    Not (volumeSolderDerivesIdentityCounterterm v e) := by
  intro h
  exact hMissing h.left.right.right.left

end P0EFTJanusZ4VolumeSolderCountertermBridge
end JanusFormal
