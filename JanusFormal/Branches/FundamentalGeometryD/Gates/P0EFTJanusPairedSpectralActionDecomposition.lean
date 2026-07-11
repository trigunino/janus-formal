import Mathlib

namespace JanusFormal
namespace P0EFTJanusPairedSpectralActionDecomposition

set_option autoImplicit false

/-- Real bookkeeping for a spectral effective action: parity-even magnitude and parity-odd eta phase. -/
structure SpectralActionParts where
  evenPart : ℝ
  oddEtaPart : ℝ

/-- PT preserves the `D^2`/heat-kernel part and reverses the eta part. -/
def ptTransform (s : SpectralActionParts) : SpectralActionParts :=
  { evenPart := s.evenPart
    oddEtaPart := -s.oddEtaPart }

@[simp] theorem pt_transform_involutive
    (s : SpectralActionParts) :
    ptTransform (ptTransform s) = s := by
  ext <;> simp [ptTransform]

/-- Pair two effective-action contributions componentwise. -/
def pairAction
    (first second : SpectralActionParts) : SpectralActionParts :=
  { evenPart := first.evenPart + second.evenPart
    oddEtaPart := first.oddEtaPart + second.oddEtaPart }

/-- A PT pair doubles the even heat-kernel part and cancels the eta part. -/
theorem pt_pair_doubles_even_cancels_odd
    (s : SpectralActionParts) :
    pairAction s (ptTransform s) =
      { evenPart := 2 * s.evenPart
        oddEtaPart := 0 } := by
  ext <;> simp [pairAction, ptTransform] <;> ring

/-- Derivative bookkeeping for a modulus-dependent spectral action. -/
structure SpectralActionDerivativeParts where
  evenDerivative : ℝ
  oddEtaDerivative : ℝ

/-- PT action on derivatives. -/
def ptDerivativeTransform
    (s : SpectralActionDerivativeParts) : SpectralActionDerivativeParts :=
  { evenDerivative := s.evenDerivative
    oddEtaDerivative := -s.oddEtaDerivative }

/-- Pair derivative data. -/
def pairDerivative
    (first second : SpectralActionDerivativeParts) :
    SpectralActionDerivativeParts :=
  { evenDerivative := first.evenDerivative + second.evenDerivative
    oddEtaDerivative := first.oddEtaDerivative + second.oddEtaDerivative }

/-- PT pairing cannot remove a nonzero parity-even slope. -/
theorem pt_pair_doubles_even_slope
    (s : SpectralActionDerivativeParts) :
    pairDerivative s (ptDerivativeTransform s) =
      { evenDerivative := 2 * s.evenDerivative
        oddEtaDerivative := 0 } := by
  ext <;> simp [pairDerivative, ptDerivativeTransform] <;> ring

/-- A strictly negative one-fold even slope remains strictly negative after pairing. -/
theorem negative_even_runaway_survives_pt_pairing
    (s : SpectralActionDerivativeParts)
    (hNegative : s.evenDerivative < 0) :
    (pairDerivative s (ptDerivativeTransform s)).evenDerivative < 0 := by
  rw [pt_pair_doubles_even_slope]
  nlinarith

/-- A strictly positive one-fold even slope also survives pairing. -/
theorem positive_even_runaway_survives_pt_pairing
    (s : SpectralActionDerivativeParts)
    (hPositive : 0 < s.evenDerivative) :
    0 < (pairDerivative s (ptDerivativeTransform s)).evenDerivative := by
  rw [pt_pair_doubles_even_slope]
  nlinarith

/-- Local heat-kernel coefficient package. -/
structure LocalHeatCoefficientParts where
  a0 : ℝ
  a2 : ℝ
  a4 : ℝ

/-- PT does not change local coefficients of `D^2`; pairing doubles all of them. -/
def pairedLocalHeatCoefficients
    (s : LocalHeatCoefficientParts) : LocalHeatCoefficientParts :=
  { a0 := 2 * s.a0
    a2 := 2 * s.a2
    a4 := 2 * s.a4 }

/-- A finite local counterterm ambiguity also doubles rather than cancels. -/
theorem paired_finite_counterterm_shift
    (oneFoldShift : ℝ) :
    oneFoldShift + oneFoldShift = 2 * oneFoldShift := by
  ring

/--
PT pairing is essential for anomaly cancellation but does not select the
parity-even modulus or its finite counterterms. That information must come from
the full even effective action and a microscopic renormalization law.
-/
structure PairedSpectralActionClosureStatus where
  oneFoldDiracOperatorConstructed : Prop
  ptConjugateOperatorConstructed : Prop
  squaredOperatorsIsospectral : Prop
  etaOddnessProved : Prop
  evenDeterminantComputed : Prop
  localHeatCoefficientsComputed : Prop
  finiteCountertermsFixed : Prop
  pairedAnomalyCancelled : Prop
  pairedEvenVacuumStable : Prop


def pairedSpectralActionClosure
    (s : PairedSpectralActionClosureStatus) : Prop :=
  s.oneFoldDiracOperatorConstructed /\
  s.ptConjugateOperatorConstructed /\
  s.squaredOperatorsIsospectral /\
  s.etaOddnessProved /\
  s.evenDeterminantComputed /\
  s.localHeatCoefficientsComputed /\
  s.finiteCountertermsFixed /\
  s.pairedAnomalyCancelled /\
  s.pairedEvenVacuumStable

end P0EFTJanusPairedSpectralActionDecomposition
end JanusFormal
