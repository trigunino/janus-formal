import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4NativeGRAcousticRepairScan

namespace JanusFormal
namespace P0EFTJanusZ4GRBackendPolicy

set_option autoImplicit false

structure GRBackendPolicy where
  cambReferenceAvailable : Prop
  nativeGRMatchesStandardGR : Prop
  defaultProviderUsesSafeGRBaseline : Prop
  nativeSourceEngineAllowedForPlanck : Prop
  z4CorrectionsAllowed : Prop

theorem native_planck_engine_requires_standard_gr_match
    (p : GRBackendPolicy)
    (hPolicy : p.nativeSourceEngineAllowedForPlanck -> p.nativeGRMatchesStandardGR)
    (hNoMatch : Not p.nativeGRMatchesStandardGR) :
    Not p.nativeSourceEngineAllowedForPlanck := by
  intro h
  exact hNoMatch (hPolicy h)

theorem z4_corrections_require_native_gr_or_controlled_baseline
    (p : GRBackendPolicy)
    (hPolicy : p.z4CorrectionsAllowed -> p.nativeGRMatchesStandardGR)
    (hNoMatch : Not p.nativeGRMatchesStandardGR) :
    Not p.z4CorrectionsAllowed := by
  intro h
  exact hNoMatch (hPolicy h)

theorem planck_baseline_can_use_safe_default_provider
    (p : GRBackendPolicy)
    (hCamb : p.cambReferenceAvailable)
    (hDefault : p.defaultProviderUsesSafeGRBaseline) :
    p.cambReferenceAvailable /\ p.defaultProviderUsesSafeGRBaseline := by
  exact And.intro hCamb hDefault

end P0EFTJanusZ4GRBackendPolicy
end JanusFormal
