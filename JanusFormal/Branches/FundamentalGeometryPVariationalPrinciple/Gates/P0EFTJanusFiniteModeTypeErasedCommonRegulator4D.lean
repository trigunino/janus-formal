import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

/-!
# Type-erased heterogeneous finite-mode regulator

The erased sector retains its finite mode type, its `Fintype` instance and the
actual `WeightedSector`; only list storage is type-erased.  Thus traces are
recomputed from the original spectra at one supplied `RegulatorTime`, and the
PT cancellation proof is obtained from the existing theorem rather than stored
as an assumed proposition.  No cutoff limit or global operator is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteModeTypeErasedCommonRegulator4D

open P0EFTJanusFiniteModeHeatKernelAnomalyRegulator
open P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

set_option autoImplicit false

noncomputable section

/-- A genuine finite weighted sector with its mode type hidden from clients. -/
structure ErasedWeightedSector where
  Mode : Type
  finiteMode : Fintype Mode
  sector : WeightedSector Mode

/-- Type erasure constructor from an actual weighted sector. -/
def eraseWeightedSector
    {Mode : Type} [Fintype Mode] (sector : WeightedSector Mode) :
    ErasedWeightedSector :=
  ⟨Mode, inferInstance, sector⟩

/-- Recompute the signed heat trace from the retained spectrum. -/
def ErasedWeightedSector.heatTrace
    (regulatorTime : RegulatorTime) (erased : ErasedWeightedSector) : ℝ := by
  letI : Fintype erased.Mode := erased.finiteMode
  exact signedMultiplicityHeatTrace regulatorTime erased.sector

/-- Recompute the signed PT-paired chiral trace from the retained spectrum. -/
def ErasedWeightedSector.chiralTrace
    (regulatorTime : RegulatorTime) (erased : ErasedWeightedSector) : ℝ := by
  letI : Fintype erased.Mode := erased.finiteMode
  exact signedPairedChiralTrace regulatorTime erased.sector

/-- One common time regulates a heterogeneous finite ledger. -/
def heterogeneousCommonFiniteHeatTrace
    (regulatorTime : RegulatorTime) (sectors : List ErasedWeightedSector) : ℝ :=
  (sectors.map (ErasedWeightedSector.heatTrace regulatorTime)).sum

/-- Concatenation gives exact additivity at the same regulator time. -/
theorem heterogeneousCommonFiniteHeatTrace_append
    (regulatorTime : RegulatorTime)
    (first second : List ErasedWeightedSector) :
    heterogeneousCommonFiniteHeatTrace regulatorTime (first ++ second) =
      heterogeneousCommonFiniteHeatTrace regulatorTime first +
        heterogeneousCommonFiniteHeatTrace regulatorTime second := by
  simp [heterogeneousCommonFiniteHeatTrace, List.map_append, List.sum_append]

/-- Each erased sector cancels because it still contains an actual
`WeightedSector`, to which the existing PT theorem applies. -/
theorem erased_signedPairedChiralTrace_eq_zero
    (regulatorTime : RegulatorTime) (erased : ErasedWeightedSector) :
    erased.chiralTrace regulatorTime = 0 := by
  letI : Fintype erased.Mode := erased.finiteMode
  exact signedPairedChiralTrace_eq_zero regulatorTime erased.sector

/-- The signed PT-paired chiral trace of every heterogeneous finite ledger
vanishes. -/
theorem heterogeneousSignedPairedChiralTrace_sum_eq_zero
    (regulatorTime : RegulatorTime) (sectors : List ErasedWeightedSector) :
    (sectors.map (ErasedWeightedSector.chiralTrace regulatorTime)).sum = 0 := by
  induction sectors with
  | nil => rfl
  | cons sector sectors inductionHypothesis =>
      simp [erased_signedPairedChiralTrace_eq_zero, inductionHypothesis]

end

end P0EFTJanusFiniteModeTypeErasedCommonRegulator4D
end JanusFormal
