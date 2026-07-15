import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Finite-mode heat-kernel anomaly regulator

This gate replaces the supplied integer anomaly proxy by an actual regulated
finite spectral sum.  For a finite chiral spectrum, the Fujikawa-type trace
uses the heat weight `exp (-time * eigenvalueSq)`.  The PT partner has the same
squared spectrum and opposite chirality, so the paired regulated chiral trace
cancels at every regulator time, while the parity-even heat trace doubles.

This is a genuine finite-mode regulator calculation, but it is not the
continuum Janus Dirac operator, a heat-kernel asymptotic coefficient, a local
anomaly density, or a global determinant-line holonomy.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteModeHeatKernelAnomalyRegulator

set_option autoImplicit false

noncomputable section

/-- Finite spectral input for one chiral fold. -/
structure FiniteChiralSpectrum (Mode : Type*) where
  eigenvalueSq : Mode → ℝ
  eigenvalueSq_nonnegative : ∀ mode, 0 ≤ eigenvalueSq mode
  chirality : Mode → ℝ

/-- Physical heat-kernel times are nonnegative. -/
abbrev RegulatorTime := {time : ℝ // 0 ≤ time}

/-- Explicit heat-kernel regulator weight. -/
def heatWeight (regulatorTime : RegulatorTime) (eigenvalueSq : ℝ) : ℝ :=
  Real.exp (-regulatorTime.1 * eigenvalueSq)

/-- Actual finite Fujikawa-type regulated chiral trace. -/
def regulatedChiralTrace
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (spectrum : FiniteChiralSpectrum Mode) : ℝ :=
  ∑ mode, spectrum.chirality mode *
    heatWeight regulatorTime (spectrum.eigenvalueSq mode)

/-- Parity-even regulated heat trace on the same finite spectrum. -/
def regulatedEvenHeatTrace
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (spectrum : FiniteChiralSpectrum Mode) : ℝ :=
  ∑ mode, heatWeight regulatorTime (spectrum.eigenvalueSq mode)

/-- PT partner: isospectral squared operator and opposite chirality. -/
def ptPartner
    {Mode : Type*} (spectrum : FiniteChiralSpectrum Mode) :
    FiniteChiralSpectrum Mode where
  eigenvalueSq := spectrum.eigenvalueSq
  eigenvalueSq_nonnegative := spectrum.eigenvalueSq_nonnegative
  chirality := fun mode => -spectrum.chirality mode

theorem ptPartner_eigenvalueSq
    {Mode : Type*} (spectrum : FiniteChiralSpectrum Mode) (mode : Mode) :
    (ptPartner spectrum).eigenvalueSq mode = spectrum.eigenvalueSq mode := rfl

theorem ptPartner_chirality
    {Mode : Type*} (spectrum : FiniteChiralSpectrum Mode) (mode : Mode) :
    (ptPartner spectrum).chirality mode = -spectrum.chirality mode := rfl

/-- The PT partner reverses the actual regulated chiral trace. -/
theorem regulatedChiralTrace_ptPartner
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (spectrum : FiniteChiralSpectrum Mode) :
    regulatedChiralTrace regulatorTime (ptPartner spectrum) =
      -regulatedChiralTrace regulatorTime spectrum := by
  classical
  simp [regulatedChiralTrace, ptPartner, Finset.sum_neg_distrib]

/-- The PT partner preserves the parity-even regulated trace. -/
theorem regulatedEvenHeatTrace_ptPartner
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (spectrum : FiniteChiralSpectrum Mode) :
    regulatedEvenHeatTrace regulatorTime (ptPartner spectrum) =
      regulatedEvenHeatTrace regulatorTime spectrum := by
  rfl

/-- Regulated PT-paired chiral trace. -/
def pairedRegulatedChiralTrace
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (spectrum : FiniteChiralSpectrum Mode) : ℝ :=
  regulatedChiralTrace regulatorTime spectrum +
    regulatedChiralTrace regulatorTime (ptPartner spectrum)

/-- Exact cancellation holds at every finite regulator time. -/
theorem pairedRegulatedChiralTrace_eq_zero
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (spectrum : FiniteChiralSpectrum Mode) :
    pairedRegulatedChiralTrace regulatorTime spectrum = 0 := by
  rw [pairedRegulatedChiralTrace, regulatedChiralTrace_ptPartner]
  ring

/-- Regulated PT-paired parity-even trace. -/
def pairedRegulatedEvenHeatTrace
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (spectrum : FiniteChiralSpectrum Mode) : ℝ :=
  regulatedEvenHeatTrace regulatorTime spectrum +
    regulatedEvenHeatTrace regulatorTime (ptPartner spectrum)

/-- PT pairing preserves and doubles the even heat trace. -/
theorem pairedRegulatedEvenHeatTrace_eq_two_mul
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (spectrum : FiniteChiralSpectrum Mode) :
    pairedRegulatedEvenHeatTrace regulatorTime spectrum =
      2 * regulatedEvenHeatTrace regulatorTime spectrum := by
  rw [pairedRegulatedEvenHeatTrace, regulatedEvenHeatTrace_ptPartner]
  ring

/-- One explicit zero-eigenvalue chiral mode. -/
def oneZeroModeSpectrum : FiniteChiralSpectrum Unit where
  eigenvalueSq := fun _ => 0
  eigenvalueSq_nonnegative := by intro; norm_num
  chirality := fun _ => 1

/-- The paired anomaly trace vanishes while the even regulated content is
nonzero, so cancellation does not erase or normalize the even sector. -/
theorem oneZeroMode_regulated_witness (regulatorTime : RegulatorTime) :
    pairedRegulatedChiralTrace regulatorTime oneZeroModeSpectrum = 0 ∧
      pairedRegulatedEvenHeatTrace regulatorTime oneZeroModeSpectrum = 2 := by
  constructor
  · exact pairedRegulatedChiralTrace_eq_zero regulatorTime oneZeroModeSpectrum
  · norm_num [pairedRegulatedEvenHeatTrace, regulatedEvenHeatTrace,
      ptPartner, oneZeroModeSpectrum, heatWeight]

end

end P0EFTJanusFiniteModeHeatKernelAnomalyRegulator
end JanusFormal
