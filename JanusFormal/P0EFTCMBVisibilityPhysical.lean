namespace JanusFormal
namespace P0EFTCMBVisibilityPhysical

set_option autoImplicit false

structure CMBVisibilityPhysical where
  deltaNeffHolstIncluded : Prop
  visibilityNormalized : Prop
  visibilityFunctionReady : Prop
  fullRecombinationODESolverDerived : Prop

def visibilityPhysicalReady (v : CMBVisibilityPhysical) : Prop :=
  v.deltaNeffHolstIncluded /\
  v.visibilityNormalized /\
  v.visibilityFunctionReady

def recombinationReady (v : CMBVisibilityPhysical) : Prop :=
  visibilityPhysicalReady v /\
  v.fullRecombinationODESolverDerived

theorem physical_visibility_replaces_fixed_gaussian_target
    (v : CMBVisibilityPhysical)
    (hDelta : v.deltaNeffHolstIncluded)
    (hNorm : v.visibilityNormalized)
    (hReady : v.visibilityFunctionReady) :
    visibilityPhysicalReady v := by
  exact And.intro hDelta (And.intro hNorm hReady)

theorem missing_recombination_ode_blocks_final_visibility
    (v : CMBVisibilityPhysical)
    (hMissing : Not v.fullRecombinationODESolverDerived) :
    Not (recombinationReady v) := by
  intro h
  exact hMissing h.right

end P0EFTCMBVisibilityPhysical
end JanusFormal
