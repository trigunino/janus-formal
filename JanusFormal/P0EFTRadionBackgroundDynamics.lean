import JanusFormal.P0EFTGrowthNumericSolverFamily

namespace JanusFormal
namespace P0EFTRadionBackgroundDynamics

set_option autoImplicit false

structure RadionBackgroundDynamics where
  radionKGStructureEncoded : Prop
  omegaTExtractionEncoded : Prop
  potentialVFixedFromJanusAction : Prop
  spinorBoundarySourceFixed : Prop
  radionBackgroundSolutionReady : Prop
  omegaTNoFitReady : Prop

def radionBackgroundStarted (r : RadionBackgroundDynamics) : Prop :=
  r.radionKGStructureEncoded /\
  r.omegaTExtractionEncoded

def radionBackgroundClosed (r : RadionBackgroundDynamics) : Prop :=
  radionBackgroundStarted r /\
  r.potentialVFixedFromJanusAction /\
  r.spinorBoundarySourceFixed /\
  r.radionBackgroundSolutionReady /\
  r.omegaTNoFitReady

theorem kg_structure_starts_radion_background
    (r : RadionBackgroundDynamics)
    (hKG : r.radionKGStructureEncoded)
    (hOmega : r.omegaTExtractionEncoded) :
    radionBackgroundStarted r := by
  exact And.intro hKG hOmega

theorem missing_potential_blocks_omegaT_no_fit
    (r : RadionBackgroundDynamics)
    (hMissing : Not r.potentialVFixedFromJanusAction) :
    Not (radionBackgroundClosed r) := by
  intro h
  exact hMissing h.right.left

theorem missing_spinor_source_blocks_omegaT_no_fit
    (r : RadionBackgroundDynamics)
    (hMissing : Not r.spinorBoundarySourceFixed) :
    Not (radionBackgroundClosed r) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTRadionBackgroundDynamics
end JanusFormal
