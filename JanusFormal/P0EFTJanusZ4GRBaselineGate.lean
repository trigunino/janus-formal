import JanusFormal.P0EFTJanusZ4CMBSolver

namespace JanusFormal
namespace P0EFTJanusZ4GRBaselineGate

set_option autoImplicit false

structure GRBaselineGate where
  z4SectorEnabled : Prop
  negativeSectorEnabled : Prop
  torsionEnabled : Prop
  visibilityNormalized : Prop
  finiteSources : Prop
  finiteSpectra : Prop
  positiveAutoSpectra : Prop
  planckValidationClaimed : Prop

def grBaselineReady (g : GRBaselineGate) : Prop :=
  Not g.z4SectorEnabled /\
  Not g.negativeSectorEnabled /\
  Not g.torsionEnabled /\
  g.visibilityNormalized /\
  g.finiteSources /\
  g.finiteSpectra /\
  g.positiveAutoSpectra

theorem gr_baseline_is_not_planck_validation
    (g : GRBaselineGate)
    (_h : grBaselineReady g)
    (hNoClaim : Not g.planckValidationClaimed) :
    Not g.planckValidationClaimed := by
  exact hNoClaim

theorem gr_baseline_has_finite_spectra
    (g : GRBaselineGate)
    (h : grBaselineReady g) :
    g.finiteSpectra /\ g.positiveAutoSpectra := by
  exact And.intro h.right.right.right.right.right.left h.right.right.right.right.right.right

end P0EFTJanusZ4GRBaselineGate
end JanusFormal
