import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4GRBaselineGate

namespace JanusFormal
namespace P0EFTJanusZ4NativeGRReferenceGate

set_option autoImplicit false

structure NativeGRReferenceGate where
  z4SectorEnabled : Prop
  negativeSectorEnabled : Prop
  torsionEnabled : Prop
  cambReferenceUsed : Prop
  compressedLCDMParametersUsedForValidation : Prop
  nativeGRMatchesStandardGR : Prop
  z4CorrectionsAllowed : Prop

def nativeGRReferenceExecuted (g : NativeGRReferenceGate) : Prop :=
  Not g.z4SectorEnabled /\
  Not g.negativeSectorEnabled /\
  Not g.torsionEnabled /\
  g.cambReferenceUsed /\
  Not g.compressedLCDMParametersUsedForValidation

def nativeGRReferenceAccepted (g : NativeGRReferenceGate) : Prop :=
  nativeGRReferenceExecuted g /\ g.nativeGRMatchesStandardGR

theorem z4_corrections_require_standard_gr_baseline
    (g : NativeGRReferenceGate)
    (hTransport : g.z4CorrectionsAllowed -> g.nativeGRMatchesStandardGR)
    (hNoMatch : Not g.nativeGRMatchesStandardGR) :
    Not g.z4CorrectionsAllowed := by
  intro h
  exact hNoMatch (hTransport h)

theorem accepted_gate_allows_z4_corrections
    (g : NativeGRReferenceGate)
    (_h : nativeGRReferenceAccepted g)
    (hPolicy : g.nativeGRMatchesStandardGR -> g.z4CorrectionsAllowed) :
    g.z4CorrectionsAllowed := by
  exact hPolicy _h.right

end P0EFTJanusZ4NativeGRReferenceGate
end JanusFormal
