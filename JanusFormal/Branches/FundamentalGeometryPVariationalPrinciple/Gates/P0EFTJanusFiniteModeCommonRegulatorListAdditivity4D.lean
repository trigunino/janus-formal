import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

/-!
# Additivity of the common finite-mode regulator

For a fixed finite mode type, sectors may have different spectra,
multiplicities and statistics.  One `RegulatorTime` is used throughout.
This does not combine genuinely different mode types or construct a cutoff
limit.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteModeCommonRegulatorListAdditivity4D

open P0EFTJanusFiniteModeHeatKernelAnomalyRegulator
open P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

set_option autoImplicit false

noncomputable section

/-- The common finite heat trace decomposes exactly across concatenated
sector ledgers, without changing the regulator time. -/
theorem commonFiniteHeatTrace_append
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (first second : List (WeightedSector Mode)) :
    commonFiniteHeatTrace regulatorTime (first ++ second) =
      commonFiniteHeatTrace regulatorTime first +
        commonFiniteHeatTrace regulatorTime second := by
  simp [commonFiniteHeatTrace, List.map_append, List.sum_append]

/-- Every finite heterogeneous ledger has vanishing total signed PT-paired
chiral trace. -/
theorem signedPairedChiralTrace_sum_eq_zero
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (sectors : List (WeightedSector Mode)) :
    (sectors.map (signedPairedChiralTrace regulatorTime)).sum = 0 := by
  induction sectors with
  | nil => rfl
  | cons sector sectors inductionHypothesis =>
      simp [signedPairedChiralTrace_eq_zero, inductionHypothesis]

/-- PT cancellation is additive under concatenation of two finite ledgers. -/
theorem signedPairedChiralTrace_sum_append_eq_zero
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (first second : List (WeightedSector Mode)) :
    ((first ++ second).map (signedPairedChiralTrace regulatorTime)).sum = 0 := by
  exact signedPairedChiralTrace_sum_eq_zero regulatorTime (first ++ second)

end

end P0EFTJanusFiniteModeCommonRegulatorListAdditivity4D
end JanusFormal
