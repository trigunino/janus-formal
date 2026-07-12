import Mathlib

namespace JanusFormal
namespace P0EFTJanusFiniteEtaPairing

set_option autoImplicit false

/-- Signed contribution of a nonzero real eigenvalue to a finite eta proxy. -/
noncomputable def spectralSign (eigenvalue : ℝ) : ℤ :=
  if 0 < eigenvalue then 1
  else if eigenvalue < 0 then -1
  else 0

/-- Spectral sign is odd under PT eigenvalue reversal. -/
theorem spectral_sign_neg (eigenvalue : ℝ) :
    spectralSign (-eigenvalue) = -spectralSign eigenvalue := by
  by_cases hPositive : 0 < eigenvalue
  · have hNegNegative : -eigenvalue < 0 := neg_neg_of_pos hPositive
    have hNotNegPositive : ¬ 0 < -eigenvalue :=
      not_lt.mpr (le_of_lt hNegNegative)
    simp [spectralSign, hPositive, hNegNegative, hNotNegPositive]
  · by_cases hNegative : eigenvalue < 0
    · have hNegPositive : 0 < -eigenvalue := neg_pos.mpr hNegative
      simp [spectralSign, hPositive, hNegative, hNegPositive]
    · have hZero : eigenvalue = 0 := by linarith
      simp [spectralSign, hZero]

/-- Finite eta proxy obtained by summing spectral signs. -/
noncomputable def finiteEta (spectrum : List ℝ) : ℤ :=
  (spectrum.map spectralSign).sum

/-- Eta is additive under concatenation of finite spectra. -/
theorem finite_eta_append
    (left right : List ℝ) :
    finiteEta (left ++ right) = finiteEta left + finiteEta right := by
  simp [finiteEta]

/-- Negating every eigenvalue reverses the finite eta proxy. -/
theorem finite_eta_negated_spectrum
    (spectrum : List ℝ) :
    finiteEta (spectrum.map (fun eigenvalue => -eigenvalue)) =
      -finiteEta spectrum := by
  induction spectrum with
  | nil => simp [finiteEta]
  | cons eigenvalue rest ih =>
      change
        spectralSign (-eigenvalue) +
            finiteEta (rest.map (fun value => -value)) =
          -(spectralSign eigenvalue + finiteEta rest)
      rw [spectral_sign_neg, ih]
      ring

/-- A spectrum paired eigenvalue-by-eigenvalue with its PT reverse has zero eta proxy. -/
theorem pt_paired_spectrum_has_zero_finite_eta
    (spectrum : List ℝ) :
    finiteEta
      (spectrum ++ spectrum.map (fun eigenvalue => -eigenvalue)) = 0 := by
  rw [finite_eta_append, finite_eta_negated_spectrum]
  ring

/-- The two PT-related folds carry opposite finite eta proxies. -/
theorem pt_related_folds_have_opposite_eta
    (positiveFoldSpectrum : List ℝ) :
    finiteEta
      (positiveFoldSpectrum.map (fun eigenvalue => -eigenvalue)) =
      -finiteEta positiveFoldSpectrum :=
  finite_eta_negated_spectrum positiveFoldSpectrum

/-- Zero eigenvalues do not contribute to the eta sign sum. -/
@[simp] theorem zero_eigenvalue_has_zero_spectral_sign :
    spectralSign 0 = 0 := by
  simp [spectralSign]

/-- But a zero eigenvalue makes the unregularized finite determinant product vanish. -/
def finiteDeterminantProduct (spectrum : List ℝ) : ℝ :=
  spectrum.prod

/-- Prepending a zero mode kills the finite determinant product. -/
@[simp] theorem zero_mode_kills_finite_determinant
    (spectrum : List ℝ) :
    finiteDeterminantProduct (0 :: spectrum) = 0 := by
  simp [finiteDeterminantProduct]

/--
The finite pairing theorem isolates the analytic frontier. For the actual
Dirac operator one must prove spectral discreteness, define eta by analytic
continuation, control zero modes and regulator phases, and verify gluing under
the mapping-torus/bridge construction.
-/
structure EtaAnalyticClosureStatus where
  selfAdjointDiracOperatorConstructed : Prop
  discreteRealSpectrumProved : Prop
  ptSpectralPairingProved : Prop
  heatKernelAsymptoticsDerived : Prop
  etaFunctionMeromorphicallyContinued : Prop
  etaValueAtZeroRegularized : Prop
  zeroModePrescriptionDerived : Prop
  determinantPhaseDerived : Prop
  gluingLawProved : Prop
  pairedFoldAnomalyCancellationProved : Prop


def etaAnalyticClosure
    (s : EtaAnalyticClosureStatus) : Prop :=
  s.selfAdjointDiracOperatorConstructed /\
  s.discreteRealSpectrumProved /\
  s.ptSpectralPairingProved /\
  s.heatKernelAsymptoticsDerived /\
  s.etaFunctionMeromorphicallyContinued /\
  s.etaValueAtZeroRegularized /\
  s.zeroModePrescriptionDerived /\
  s.determinantPhaseDerived /\
  s.gluingLawProved /\
  s.pairedFoldAnomalyCancellationProved

end P0EFTJanusFiniteEtaPairing
end JanusFormal
