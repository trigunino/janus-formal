import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4CAMBGRBaselineExport

namespace JanusFormal
namespace P0EFTJanusZ4GRBaselineReductionGate

set_option autoImplicit false

structure GRBaselineReductionGate where
  cambGRBaselineAvailable : Prop
  dominantTTTEMismatchReduced : Prop
  safeGRBaselineAvailable : Prop
  nativeToySourceEngineRepaired : Prop
  z4CorrectionsAllowed : Prop

theorem safe_baseline_from_reduced_tt_te
    (g : GRBaselineReductionGate)
    (hPolicy : g.cambGRBaselineAvailable -> g.dominantTTTEMismatchReduced -> g.safeGRBaselineAvailable)
    (hCamb : g.cambGRBaselineAvailable)
    (hReduced : g.dominantTTTEMismatchReduced) :
    g.safeGRBaselineAvailable := by
  exact hPolicy hCamb hReduced

theorem unrepaired_toy_engine_does_not_allow_z4_by_itself
    (g : GRBaselineReductionGate)
    (hPolicy : g.z4CorrectionsAllowed -> g.nativeToySourceEngineRepaired)
    (hNotRepaired : Not g.nativeToySourceEngineRepaired) :
    Not g.z4CorrectionsAllowed := by
  intro h
  exact hNotRepaired (hPolicy h)

end P0EFTJanusZ4GRBaselineReductionGate
end JanusFormal
