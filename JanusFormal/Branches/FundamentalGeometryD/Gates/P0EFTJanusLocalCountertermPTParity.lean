import Mathlib

namespace JanusFormal
namespace P0EFTJanusLocalCountertermPTParity

set_option autoImplicit false

/-- PT parity of a local effective-action term. -/
inductive PTParity where
  | even
  | odd
  deriving DecidableEq, Repr

/-- PT transform of one real coefficient. -/
def ptTransformCoefficient
    (parity : PTParity) (coefficient : ℝ) : ℝ :=
  match parity with
  | PTParity.even => coefficient
  | PTParity.odd => -coefficient

/-- Coefficient in the two-fold PT-paired action. -/
def pairedCoefficient
    (parity : PTParity) (coefficient : ℝ) : ℝ :=
  coefficient + ptTransformCoefficient parity coefficient

/-- PT-even local terms double. -/
@[simp] theorem even_counterterm_doubles
    (coefficient : ℝ) :
    pairedCoefficient PTParity.even coefficient = 2 * coefficient := by
  simp [pairedCoefficient, ptTransformCoefficient]
  ring

/-- PT-odd local terms cancel. -/
@[simp] theorem odd_counterterm_cancels
    (coefficient : ℝ) :
    pairedCoefficient PTParity.odd coefficient = 0 := by
  simp [pairedCoefficient, ptTransformCoefficient]

/-- Named local invariant classes relevant to the throat effective action. -/
inductive LocalInvariantKind where
  | volume
  | scalarCurvature
  | curvatureSquared
  | gaugeFieldSquared
  | gravitationalChernSimons
  | gaugeChernSimons
  deriving DecidableEq, Repr

/-- Standard PT parity assignment at the level of the real effective action. -/
def invariantParity : LocalInvariantKind → PTParity
  | LocalInvariantKind.volume => PTParity.even
  | LocalInvariantKind.scalarCurvature => PTParity.even
  | LocalInvariantKind.curvatureSquared => PTParity.even
  | LocalInvariantKind.gaugeFieldSquared => PTParity.even
  | LocalInvariantKind.gravitationalChernSimons => PTParity.odd
  | LocalInvariantKind.gaugeChernSimons => PTParity.odd

/-- Every parity-even geometric counterterm survives and doubles in the PT pair. -/
theorem geometric_even_counterterms_double
    (coefficient : ℝ) :
    pairedCoefficient (invariantParity LocalInvariantKind.volume)
        coefficient = 2 * coefficient /\
    pairedCoefficient (invariantParity LocalInvariantKind.scalarCurvature)
        coefficient = 2 * coefficient /\
    pairedCoefficient (invariantParity LocalInvariantKind.curvatureSquared)
        coefficient = 2 * coefficient /\
    pairedCoefficient (invariantParity LocalInvariantKind.gaugeFieldSquared)
        coefficient = 2 * coefficient := by
  norm_num [invariantParity]

/-- Both Chern-Simons counterterms cancel in a perfectly PT-related pair. -/
theorem chern_simons_counterterms_cancel
    (gravitationalCoefficient gaugeCoefficient : ℝ) :
    pairedCoefficient
        (invariantParity LocalInvariantKind.gravitationalChernSimons)
        gravitationalCoefficient = 0 /\
    pairedCoefficient
        (invariantParity LocalInvariantKind.gaugeChernSimons)
        gaugeCoefficient = 0 := by
  norm_num [invariantParity]

/-- PT symmetry cannot force an arbitrary even finite coefficient to vanish. -/
theorem pt_pair_does_not_remove_nonzero_even_coefficient
    (coefficient : ℝ)
    (hNonzero : coefficient ≠ 0) :
    pairedCoefficient PTParity.even coefficient ≠ 0 := by
  rw [even_counterterm_doubles]
  exact mul_ne_zero (by norm_num) hNonzero

/--
Anomaly cancellation constrains the odd part but does not determine the finite
volume, Einstein, Maxwell or curvature-squared coefficients.  Their
renormalized values require an additional microscopic matching principle.
-/
structure LocalCountertermParityClosureStatus where
  regulatorPreservesGaugeSymmetry : Prop
  regulatorPreservesPairedPT : Prop
  oddCountertermsClassified : Prop
  evenCountertermsClassified : Prop
  chernSimonsCancellationDerived : Prop
  finiteEvenCoefficientsMatchedMicroscopically : Prop
  schemeIndependenceProved : Prop


def localCountertermParityClosure
    (s : LocalCountertermParityClosureStatus) : Prop :=
  s.regulatorPreservesGaugeSymmetry /\
  s.regulatorPreservesPairedPT /\
  s.oddCountertermsClassified /\
  s.evenCountertermsClassified /\
  s.chernSimonsCancellationDerived /\
  s.finiteEvenCoefficientsMatchedMicroscopically /\
  s.schemeIndependenceProved

end P0EFTJanusLocalCountertermPTParity
end JanusFormal
