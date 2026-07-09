import JanusFormal.Legacy.P0EFT.Gates.P0EFTAPSPinTraceNormalization

namespace JanusFormal
namespace P0EFTAPSPinTraceGlobalDerivation

set_option autoImplicit false

structure APSPinGlobalIndexPackage where
  pinMinusLiftSquaredMinusOne : Prop
  apsBoundaryProjectorFredholm : Prop
  boundaryEtaZeroModeCancellation : Prop
  noParityAnomaly : Prop
  traceRegularizationStandard : Prop

def apsPinIndexPackageClosed (p : APSPinGlobalIndexPackage) : Prop :=
  p.pinMinusLiftSquaredMinusOne /\
  p.apsBoundaryProjectorFredholm /\
  p.boundaryEtaZeroModeCancellation /\
  p.noParityAnomaly /\
  p.traceRegularizationStandard

theorem aps_pin_index_package_fixes_trace_normalization
    (p : APSPinGlobalIndexPackage)
    (h : JanusFormal.Legacy.P0EFT.Gates.P0EFTAPSPinTraceNormalization.APSPinTraceNormalization)
    (_hClosed : apsPinIndexPackageClosed p)
    (hPin : h.bulkHasPinMinusStructure)
    (hAPS : h.apsBoundaryDomainDefined)
    (hEtaReg : h.etaInvariantGlobalRegularizationFixed)
    (hTrace : h.cliffordTraceRankFixedToFour)
    (hHalf : h.apsProjectorRankFixedToHalf) :
    JanusFormal.Legacy.P0EFT.Gates.P0EFTAPSPinTraceNormalization.standardTraceNormalizationDerived h := by
  unfold JanusFormal.Legacy.P0EFT.Gates.P0EFTAPSPinTraceNormalization.standardTraceNormalizationDerived
  unfold JanusFormal.Legacy.P0EFT.Gates.P0EFTAPSPinTraceNormalization.apsPinGlobalHypothesis
  exact And.intro
    (And.intro hPin (And.intro hAPS hEtaReg))
    (And.intro hTrace hHalf)

theorem aps_pin_global_package_derives_eta_h_lock
    (p : APSPinGlobalIndexPackage)
    (h : JanusFormal.Legacy.P0EFT.Gates.P0EFTAPSPinTraceNormalization.APSPinTraceNormalization)
    (l : P0EFTNiehYanAnomalyDerivation.NiehYanTraceLock)
    (hClosed : apsPinIndexPackageClosed p)
    (hPin : h.bulkHasPinMinusStructure)
    (hAPS : h.apsBoundaryDomainDefined)
    (hEtaReg : h.etaInvariantGlobalRegularizationFixed)
    (hTrace : h.cliffordTraceRankFixedToFour)
    (hHalf : h.apsProjectorRankFixedToHalf)
    (hLocal : P0EFTNiehYanAnomalyDerivation.localTraceDerivesEtaMinusTwo l) :
    P0EFTNiehYanAnomalyDerivation.etaHPlusTwoClosed l := by
  apply JanusFormal.Legacy.P0EFT.Gates.P0EFTAPSPinTraceNormalization.aps_pin_hypothesis_derives_local_trace_lock h l
  · exact aps_pin_index_package_fixes_trace_normalization
      p h hClosed hPin hAPS hEtaReg hTrace hHalf
  · exact hLocal

theorem missing_eta_zero_mode_cancellation_blocks_global_package
    (p : APSPinGlobalIndexPackage)
    (hMissing : Not p.boundaryEtaZeroModeCancellation) :
    Not (apsPinIndexPackageClosed p) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTAPSPinTraceGlobalDerivation
end JanusFormal
