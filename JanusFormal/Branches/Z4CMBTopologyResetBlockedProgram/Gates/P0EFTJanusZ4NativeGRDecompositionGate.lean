import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4NativeGRReferenceGate

namespace JanusFormal
namespace P0EFTJanusZ4NativeGRDecompositionGate

set_option autoImplicit false

structure NativeGRDecompositionGate where
  interfaceChecked : Prop
  backgroundGeometryChecked : Prop
  visibilityChecked : Prop
  fixedKSourceDiagnosticsChecked : Prop
  unlensedSpectraChecked : Prop
  lensingSplitChecked : Prop
  nativeGRMatchesStandardGR : Prop
  physicalPlanckInterpretationAllowed : Prop
  z4CorrectionsAllowed : Prop

def decompositionExecuted (g : NativeGRDecompositionGate) : Prop :=
  g.interfaceChecked /\
  g.backgroundGeometryChecked /\
  g.visibilityChecked /\
  g.fixedKSourceDiagnosticsChecked /\
  g.unlensedSpectraChecked /\
  g.lensingSplitChecked

theorem planck_interpretation_requires_native_gr_match
    (g : NativeGRDecompositionGate)
    (hPolicy : g.physicalPlanckInterpretationAllowed -> g.nativeGRMatchesStandardGR)
    (hNoMatch : Not g.nativeGRMatchesStandardGR) :
    Not g.physicalPlanckInterpretationAllowed := by
  intro h
  exact hNoMatch (hPolicy h)

theorem z4_corrections_require_decomposed_native_gr_match
    (g : NativeGRDecompositionGate)
    (hPolicy : g.z4CorrectionsAllowed -> decompositionExecuted g /\ g.nativeGRMatchesStandardGR)
    (hNoMatch : Not g.nativeGRMatchesStandardGR) :
    Not g.z4CorrectionsAllowed := by
  intro h
  exact hNoMatch (hPolicy h).right

end P0EFTJanusZ4NativeGRDecompositionGate
end JanusFormal
