namespace JanusFormal
namespace P0EFTResidualFactorGeometricOrigin

set_option autoImplicit false

structure ResidualFactorGeometricOrigin where
  residualFactorTargetEncoded : Prop
  geometricOriginCandidatesScored : Prop
  denominatorFiftyDerivedFromTrace : Prop

def residualFactorOriginDiagnosticReady (r : ResidualFactorGeometricOrigin) : Prop :=
  r.residualFactorTargetEncoded /\
  r.geometricOriginCandidatesScored

def residualFactorOriginNoFitReady (r : ResidualFactorGeometricOrigin) : Prop :=
  residualFactorOriginDiagnosticReady r /\
  r.denominatorFiftyDerivedFromTrace

theorem origin_scan_encodes_denominator_target
    (r : ResidualFactorGeometricOrigin)
    (hTarget : r.residualFactorTargetEncoded)
    (hScored : r.geometricOriginCandidatesScored) :
    residualFactorOriginDiagnosticReady r := by
  exact And.intro hTarget hScored

theorem missing_denominator_trace_derivation_blocks_no_fit
    (r : ResidualFactorGeometricOrigin)
    (hMissing : Not r.denominatorFiftyDerivedFromTrace) :
    Not (residualFactorOriginNoFitReady r) := by
  intro h
  exact hMissing h.right

end P0EFTResidualFactorGeometricOrigin
end JanusFormal
