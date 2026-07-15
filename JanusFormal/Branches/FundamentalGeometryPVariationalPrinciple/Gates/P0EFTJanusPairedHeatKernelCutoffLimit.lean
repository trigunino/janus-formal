import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeHeatKernelAnomalyRegulator

/-!
# Countable PT-paired heat-kernel cutoff limit

An abstract countable chiral spectrum is truncated to its first `cutoff`
modes.  At every cutoff the finite heat-kernel trace is paired with the
isospectral opposite-chirality spectrum, so the paired trace vanishes
exactly.  Consequently both the raw and explicitly averaged paired cutoff
sequences converge to zero.

When the one-fold regulated mode series is summable, the finite cutoffs also
converge to its `tsum`; the PT-partner series is summable and has the opposite
sum, hence the paired infinite regulated trace is well-defined and zero.

This is a countable spectral model with supplied squared eigenvalues and PT
pairing.  It does not construct a continuum Dirac operator, a local
heat-kernel coefficient or anomaly density, a determinant line, or a
microscopic physical normalization.
-/

namespace JanusFormal
namespace P0EFTJanusPairedHeatKernelCutoffLimit

set_option autoImplicit false

noncomputable section

open Filter
open P0EFTJanusFiniteModeHeatKernelAnomalyRegulator

/-- Supplied countable squared spectrum and chirality weights for one fold. -/
structure CountableChiralSpectrum where
  eigenvalueSq : ℕ → ℝ
  eigenvalueSq_nonnegative : ∀ mode, 0 ≤ eigenvalueSq mode
  chirality : ℕ → ℝ

/-- The first `cutoff` modes, as an actual finite spectrum. -/
def finiteTruncation
    (spectrum : CountableChiralSpectrum) (cutoff : ℕ) :
    FiniteChiralSpectrum (Fin cutoff) where
  eigenvalueSq := fun mode => spectrum.eigenvalueSq mode.1
  eigenvalueSq_nonnegative := fun mode =>
    spectrum.eigenvalueSq_nonnegative mode.1
  chirality := fun mode => spectrum.chirality mode.1

/-- One regulated mode contribution. -/
def regulatedModeTerm
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) (mode : ℕ) : ℝ :=
  spectrum.chirality mode *
    heatWeight regulatorTime (spectrum.eigenvalueSq mode)

/-- Unpaired regulated trace of the first `cutoff` modes. -/
def cutoffChiralTrace
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) (cutoff : ℕ) : ℝ :=
  regulatedChiralTrace regulatorTime (finiteTruncation spectrum cutoff)

/-- The finite trace is the usual `Finset.range` partial sum of the
countable regulated mode series. -/
theorem cutoffChiralTrace_eq_sum_range
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) (cutoff : ℕ) :
    cutoffChiralTrace regulatorTime spectrum cutoff =
      ∑ mode ∈ Finset.range cutoff,
        regulatedModeTerm regulatorTime spectrum mode := by
  classical
  simpa [cutoffChiralTrace, regulatedChiralTrace, finiteTruncation,
    regulatedModeTerm] using
    (Fin.sum_univ_eq_sum_range
      (fun mode => regulatedModeTerm regulatorTime spectrum mode) cutoff)

/-- PT-paired regulated trace at one finite cutoff. -/
def pairedCutoffChiralTrace
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) (cutoff : ℕ) : ℝ :=
  pairedRegulatedChiralTrace regulatorTime
    (finiteTruncation spectrum cutoff)

/-- Exact chiral cancellation holds before taking any cutoff limit. -/
@[simp]
theorem pairedCutoffChiralTrace_eq_zero
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) (cutoff : ℕ) :
    pairedCutoffChiralTrace regulatorTime spectrum cutoff = 0 := by
  exact pairedRegulatedChiralTrace_eq_zero regulatorTime
    (finiteTruncation spectrum cutoff)

/-- The identically zero paired cutoff sequence converges to zero. -/
theorem pairedCutoffChiralTrace_tendsto_zero
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) :
    Tendsto (fun cutoff =>
      pairedCutoffChiralTrace regulatorTime spectrum cutoff)
      atTop (nhds 0) := by
  simpa only [pairedCutoffChiralTrace_eq_zero] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- Explicit arithmetic averaging factor.  It is bookkeeping only, not a
derived physical normalization. -/
def cutoffAverageNormalization (cutoff : ℕ) : ℝ :=
  (((cutoff + 1 : ℕ) : ℝ))⁻¹

/-- Averaged paired cutoff trace. -/
def normalizedPairedCutoffChiralTrace
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) (cutoff : ℕ) : ℝ :=
  cutoffAverageNormalization cutoff *
    pairedCutoffChiralTrace regulatorTime spectrum cutoff

@[simp]
theorem normalizedPairedCutoffChiralTrace_eq_zero
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) (cutoff : ℕ) :
    normalizedPairedCutoffChiralTrace regulatorTime spectrum cutoff = 0 := by
  simp [normalizedPairedCutoffChiralTrace]

theorem normalizedPairedCutoffChiralTrace_tendsto_zero
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) :
    Tendsto (fun cutoff =>
      normalizedPairedCutoffChiralTrace regulatorTime spectrum cutoff)
      atTop (nhds 0) := by
  simpa only [normalizedPairedCutoffChiralTrace_eq_zero] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

/-- Countable PT partner: identical squared spectrum and reversed chirality. -/
def countablePTPartner
    (spectrum : CountableChiralSpectrum) : CountableChiralSpectrum where
  eigenvalueSq := spectrum.eigenvalueSq
  eigenvalueSq_nonnegative := spectrum.eigenvalueSq_nonnegative
  chirality := fun mode => -spectrum.chirality mode

@[simp]
theorem regulatedModeTerm_countablePTPartner
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) (mode : ℕ) :
    regulatedModeTerm regulatorTime (countablePTPartner spectrum) mode =
      -regulatedModeTerm regulatorTime spectrum mode := by
  simp [regulatedModeTerm, countablePTPartner]

/-- Absolute convergence obligation for one regulated fold. -/
def RegulatedSummable
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) : Prop :=
  Summable (regulatedModeTerm regulatorTime spectrum)

/-- The countable regulated chiral trace, used only with an explicit
summability witness below. -/
def regulatedInfiniteChiralTrace
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) : ℝ :=
  ∑' mode, regulatedModeTerm regulatorTime spectrum mode

/-- A summable one-fold series is the limit of the actual finite cutoffs. -/
theorem cutoffChiralTrace_tendsto_infiniteTrace
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum)
    (hSummable : RegulatedSummable regulatorTime spectrum) :
    Tendsto (fun cutoff => cutoffChiralTrace regulatorTime spectrum cutoff)
      atTop (nhds (regulatedInfiniteChiralTrace regulatorTime spectrum)) := by
  have hLimit := hSummable.hasSum.tendsto_sum_nat
  simpa only [cutoffChiralTrace_eq_sum_range,
    regulatedInfiniteChiralTrace] using hLimit

/-- PT reversal preserves summability. -/
theorem regulatedSummable_countablePTPartner
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum)
    (hSummable : RegulatedSummable regulatorTime spectrum) :
    RegulatedSummable regulatorTime (countablePTPartner spectrum) := by
  unfold RegulatedSummable at hSummable ⊢
  have hTerms :
      regulatedModeTerm regulatorTime (countablePTPartner spectrum) =
        fun mode => -regulatedModeTerm regulatorTime spectrum mode := by
    funext mode
    exact regulatedModeTerm_countablePTPartner
      regulatorTime spectrum mode
  rw [hTerms]
  exact hSummable.neg

/-- The summable PT-partner trace is the negative of the original trace. -/
theorem regulatedInfiniteChiralTrace_countablePTPartner
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) :
    regulatedInfiniteChiralTrace regulatorTime
        (countablePTPartner spectrum) =
      -regulatedInfiniteChiralTrace regulatorTime spectrum := by
  simp only [regulatedInfiniteChiralTrace,
    regulatedModeTerm_countablePTPartner, tsum_neg]

/-- Infinite PT-paired regulated trace. -/
def pairedInfiniteChiralTrace
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum) : ℝ :=
  regulatedInfiniteChiralTrace regulatorTime spectrum +
    regulatedInfiniteChiralTrace regulatorTime
      (countablePTPartner spectrum)

/-- Under the explicit one-fold summability obligation, both infinite traces
are well-defined and cancel exactly. -/
theorem pairedInfiniteChiralTrace_eq_zero
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum)
    (hSummable : RegulatedSummable regulatorTime spectrum) :
    pairedInfiniteChiralTrace regulatorTime spectrum = 0 := by
  have _hPartner :=
    regulatedSummable_countablePTPartner regulatorTime spectrum hSummable
  rw [pairedInfiniteChiralTrace,
    regulatedInfiniteChiralTrace_countablePTPartner]
  ring

/-- The exact finite-cutoff cancellation converges to the summable infinite
paired trace, which is itself zero. -/
theorem pairedCutoffChiralTrace_tendsto_infinitePair
    (regulatorTime : RegulatorTime)
    (spectrum : CountableChiralSpectrum)
    (hSummable : RegulatedSummable regulatorTime spectrum) :
    Tendsto (fun cutoff =>
      pairedCutoffChiralTrace regulatorTime spectrum cutoff)
      atTop (nhds (pairedInfiniteChiralTrace regulatorTime spectrum)) := by
  rw [pairedInfiniteChiralTrace_eq_zero regulatorTime spectrum hSummable]
  exact pairedCutoffChiralTrace_tendsto_zero regulatorTime spectrum

end

end P0EFTJanusPairedHeatKernelCutoffLimit
end JanusFormal
