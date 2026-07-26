import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConcreteFullActionFrechetBridge4D

/-!
# Concrete linewise C² closure for the full-action Fréchet bridge

This gate proves the strongest unconditional regularity prerequisite currently
derivable from the concrete Candidate-A formulas.  It neither changes the
full-action bridge nor promotes a sectorial model to a global field-space
action.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPConcreteFullActionFrechetC2Closure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Filter
open scoped ContDiff Matrix.Norms.Frobenius BigOperators Topology
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusExplicitReciprocalCrossDensities
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusCoDiagonalLorentzRootChart
open P0EFTJanusCoDiagonalLorentzRootFirstDerivative
open P0EFTJanusCoDiagonalInteractionDensityFrechet

private theorem ambientPlusMetricVolume_eq_prod
    (point : P0EFTJanusCoDiagonalInteractionDensityFrechet.ScalePair)
    (hPoint : point ∈ ambientPositiveScalePairDomain) :
    ambientPlusMetricVolume point = ∏ i : Fin 4, point.1 i := by
  simp only [ambientPlusMetricVolume, ambientPlusMetric, ambientLorentzMetric,
    Matrix.det_diagonal]
  simp only [Fin.prod_univ_four, abs_mul]
  have hProduct : 0 <
      point.1 0 * point.1 1 * point.1 2 * point.1 3 :=
    mul_pos (mul_pos (mul_pos (hPoint.1 0) (hPoint.1 1))
      (hPoint.1 2)) (hPoint.1 3)
  rw [show
      |lorentzSign 0| * |point.1 0 ^ 2| *
          (|lorentzSign 1| * |point.1 1 ^ 2|) *
          (|lorentzSign 2| * |point.1 2 ^ 2|) *
          (|lorentzSign 3| * |point.1 3 ^ 2|) =
        (point.1 0 * point.1 1 * point.1 2 * point.1 3) ^ 2 by
      have hTwo : (2 : Fin 4) ≠ 0 := by decide
      have hThree : (3 : Fin 4) ≠ 0 := by decide
      simp [lorentzSign, hTwo, hThree,
        abs_of_nonneg (sq_nonneg (point.1 0)),
        abs_of_nonneg (sq_nonneg (point.1 1)),
        abs_of_nonneg (sq_nonneg (point.1 2)),
        abs_of_nonneg (sq_nonneg (point.1 3))]
      ring]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hProduct]

/-- Rational-polynomial representative of the co-diagonal density on its
positive chart. -/
private def smoothCoDiagonalInteractionDensity
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (point : P0EFTJanusCoDiagonalInteractionDensityFrechet.ScalePair) : Real :=
  -interactionScale * (∏ i : Fin 4, point.1 i) *
    spectralPotential coefficients (ambientRootRatio point)

private theorem smoothCoDiagonalInteractionDensity_eq
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (point : P0EFTJanusCoDiagonalInteractionDensityFrechet.ScalePair)
    (hPoint : point ∈ ambientPositiveScalePairDomain) :
    smoothCoDiagonalInteractionDensity interactionScale coefficients point =
      coDiagonalInteractionDensity interactionScale coefficients point := by
  rw [coDiagonalInteractionDensity, ambientPlusMetricVolume_eq_prod point hPoint,
    ambientRootMatrix, matrixSpectralPotential_diagonal]
  rfl

private theorem smoothCoDiagonalInteractionDensity_contDiffAt
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (point : P0EFTJanusCoDiagonalInteractionDensityFrechet.ScalePair)
    (hPoint : point ∈ ambientPositiveScalePairDomain) :
    ContDiffAt Real ∞
      (smoothCoDiagonalInteractionDensity interactionScale coefficients) point := by
  unfold smoothCoDiagonalInteractionDensity spectralPotential elementary0
    elementary1 elementary2 elementary3 elementary4 ambientRootRatio
  fun_prop (disch := exact ne_of_gt (hPoint.1 _))

/-- The genuine co-diagonal Candidate-A density is smooth on the complete
positive scale chart; positivity removes the apparent `sqrt |det|` singularity
and the diagonal identity reduces the matrix potential to its exact spectral
polynomial. -/
theorem coDiagonalInteractionDensity_contDiffOn
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffOn Real ∞
      (coDiagonalInteractionDensity interactionScale coefficients)
      ambientPositiveScalePairDomain := by
  rw [ambientPositiveScalePairDomain_isOpen.contDiffOn_iff]
  intro point hPoint
  apply (smoothCoDiagonalInteractionDensity_contDiffAt interactionScale
    coefficients point hPoint).congr_of_eventuallyEq
  filter_upwards [ambientPositiveScalePairDomain_isOpen.mem_nhds hPoint]
    with varied hVaried
  exact (smoothCoDiagonalInteractionDensity_eq interactionScale coefficients
    varied hVaried).symm

end

end P0EFTJanusProgramPConcreteFullActionFrechetC2Closure4D
end JanusFormal
