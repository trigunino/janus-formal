import JanusFormal.P0EFTSameLPhaseSpaceBridge

namespace JanusFormal
namespace P0EFTMassShellB4volMeasure

set_option autoImplicit false

structure MassShellB4volMeasure where
  massShellMeasureDefined : Prop
  lapseEnergyFactorIdentified : Prop
  b4volCandidateDefined : Prop
  b4volDerivedFromSoldering : Prop
  activeSourceMeasureClosed : Prop
  stressTensorMomentsClosed : Prop

def massShellMeasureStarted (m : MassShellB4volMeasure) : Prop :=
  m.massShellMeasureDefined /\
  m.lapseEnergyFactorIdentified /\
  m.b4volCandidateDefined

def activeSourceMeasureClosed (m : MassShellB4volMeasure) : Prop :=
  massShellMeasureStarted m /\
  m.b4volDerivedFromSoldering /\
  m.activeSourceMeasureClosed

def matterMomentsClosed (m : MassShellB4volMeasure) : Prop :=
  activeSourceMeasureClosed m /\ m.stressTensorMomentsClosed

theorem mass_shell_and_b4vol_candidate_start_measure
    (m : MassShellB4volMeasure)
    (hShell : m.massShellMeasureDefined)
    (hLapse : m.lapseEnergyFactorIdentified)
    (hB4 : m.b4volCandidateDefined) :
    massShellMeasureStarted m := by
  exact And.intro hShell (And.intro hLapse hB4)

theorem missing_b4vol_derivation_blocks_active_source
    (m : MassShellB4volMeasure)
    (hMissing : Not m.b4volDerivedFromSoldering) :
    Not (activeSourceMeasureClosed m) := by
  intro h
  exact hMissing h.right.left

theorem b4vol_and_active_source_close_measure
    (m : MassShellB4volMeasure)
    (hStarted : massShellMeasureStarted m)
    (hB4 : m.b4volDerivedFromSoldering)
    (hActive : m.activeSourceMeasureClosed) :
    activeSourceMeasureClosed m := by
  exact And.intro hStarted (And.intro hB4 hActive)

end P0EFTMassShellB4volMeasure
end JanusFormal
