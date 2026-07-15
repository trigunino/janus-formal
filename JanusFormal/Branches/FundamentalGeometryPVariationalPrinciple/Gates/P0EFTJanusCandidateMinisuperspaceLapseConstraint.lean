import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitReciprocalCrossDensities

/-!
FLRW minisuperspace lapse gate for the explicit reciprocal bimetric candidate.
The time eigenvalue of `X = sqrt(g_plus^{-1} g_minus)` is
`lapseMinus / lapsePlus`, while its three spatial eigenvalues equal the scale
ratio `r`.  Multiplication by the plus-sector lapse makes the common
elementary-symmetric interaction affine in both lapses.

This is an exact reduced algebraic gate.  Lapse affinity supplies primary
constraint precursors only; it does not derive the ADM shift redefinition,
Poisson brackets, an independent secondary constraint, or removal of the
Boulware--Deser mode in the covariant theory.
-/

namespace JanusFormal
namespace P0EFTJanusCandidateMinisuperspaceLapseConstraint

set_option autoImplicit false

noncomputable section

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusExplicitReciprocalCrossDensities

/-- FLRW spectrum `(lapseMinus/lapsePlus, r, r, r)` before substituting the
lapse ratio. -/
def flrwDiagonalSpectrum
    (timeEigenvalue spatialRatio : ℝ) : SquareRootSpectrum :=
  fun i => if i = 0 then timeEigenvalue else spatialRatio

theorem flrwDiagonalSpectrum_nonzero
    (timeEigenvalue spatialRatio : ℝ)
    (hTime : timeEigenvalue ≠ 0)
    (hSpatial : spatialRatio ≠ 0) :
    SpectrumNonzero (flrwDiagonalSpectrum timeEigenvalue spatialRatio) := by
  intro i
  fin_cases i <;> simp [flrwDiagonalSpectrum, hTime, hSpatial]

/-- Exact four-dimensional elementary-symmetric expansion on the FLRW
diagonal spectrum. -/
theorem spectralPotential_on_flrwDiagonalSpectrum
    (coefficients : PotentialCoefficients)
    (timeEigenvalue spatialRatio : ℝ) :
    spectralPotential coefficients
        (flrwDiagonalSpectrum timeEigenvalue spatialRatio) =
      coefficients.beta0 +
        coefficients.beta1 * (timeEigenvalue + 3 * spatialRatio) +
        coefficients.beta2 *
          (3 * timeEigenvalue * spatialRatio + 3 * spatialRatio ^ 2) +
        coefficients.beta3 *
          (3 * timeEigenvalue * spatialRatio ^ 2 + spatialRatio ^ 3) +
        coefficients.beta4 * timeEigenvalue * spatialRatio ^ 3 := by
  unfold spectralPotential elementary0 elementary1 elementary2 elementary3
    elementary4 flrwDiagonalSpectrum
  simp [show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide]
  ring

/-- Coefficient of the plus lapse in the reduced interaction. -/
def plusLapseCoefficient
    (coefficients : PotentialCoefficients) (spatialRatio : ℝ) : ℝ :=
  coefficients.beta0 + 3 * coefficients.beta1 * spatialRatio +
    3 * coefficients.beta2 * spatialRatio ^ 2 +
    coefficients.beta3 * spatialRatio ^ 3

/-- Coefficient of the minus lapse in the reduced interaction. -/
def minusLapseCoefficient
    (coefficients : PotentialCoefficients) (spatialRatio : ℝ) : ℝ :=
  coefficients.beta1 + 3 * coefficients.beta2 * spatialRatio +
    3 * coefficients.beta3 * spatialRatio ^ 2 +
    coefficients.beta4 * spatialRatio ^ 3

/-- Lapse-dependent part of the common Candidate A interaction.  Factors fixed
during lapse variation, including the spatial volume, may be absorbed into
`interactionScale`. -/
def candidateLapseInteraction
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (spatialRatio lapsePlus lapseMinus : ℝ) : ℝ :=
  -interactionScale *
    (lapsePlus * plusLapseCoefficient coefficients spatialRatio +
      lapseMinus * minusLapseCoefficient coefficients spatialRatio)

/-- The unsplit common interaction representing the two reciprocal M30 slots
is exactly affine in the FLRW lapses. -/
theorem reciprocal_spectral_interaction_is_lapse_linear
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (spatialRatio lapsePlus lapseMinus : ℝ)
    (hLapsePlus : lapsePlus ≠ 0) :
    lapsePlus *
        commonInteractionPotential interactionScale coefficients
          (flrwDiagonalSpectrum (lapseMinus / lapsePlus) spatialRatio) =
      candidateLapseInteraction interactionScale coefficients spatialRatio
        lapsePlus lapseMinus := by
  unfold commonInteractionPotential
  rw [spectralPotential_on_flrwDiagonalSpectrum]
  unfold candidateLapseInteraction plusLapseCoefficient minusLapseCoefficient
  field_simp [hLapsePlus]
  ring

/-- Finite plus-lapse variation.  Its coefficient is lapse-independent and is
therefore a primary-constraint precursor, not yet a covariant constraint. -/
theorem plus_lapse_variation_is_primary_constraint_precursor
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (spatialRatio lapsePlus lapseMinus increment : ℝ) :
    candidateLapseInteraction interactionScale coefficients spatialRatio
          (lapsePlus + increment) lapseMinus -
        candidateLapseInteraction interactionScale coefficients spatialRatio
          lapsePlus lapseMinus =
      increment *
        (-interactionScale * plusLapseCoefficient coefficients spatialRatio) := by
  unfold candidateLapseInteraction
  ring

/-- Finite minus-lapse variation with a lapse-independent coefficient. -/
theorem minus_lapse_variation_is_primary_constraint_precursor
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (spatialRatio lapsePlus lapseMinus increment : ℝ) :
    candidateLapseInteraction interactionScale coefficients spatialRatio
          lapsePlus (lapseMinus + increment) -
        candidateLapseInteraction interactionScale coefficients spatialRatio
          lapsePlus lapseMinus =
      increment *
        (-interactionScale * minusLapseCoefficient coefficients spatialRatio) := by
  unfold candidateLapseInteraction
  ring

/-- The pure plus-lapse second finite variation vanishes. -/
theorem plus_lapse_second_variation_vanishes
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (spatialRatio lapsePlus lapseMinus first second : ℝ) :
    (candidateLapseInteraction interactionScale coefficients spatialRatio
          (lapsePlus + first + second) lapseMinus -
        candidateLapseInteraction interactionScale coefficients spatialRatio
          (lapsePlus + first) lapseMinus) -
      (candidateLapseInteraction interactionScale coefficients spatialRatio
          (lapsePlus + second) lapseMinus -
        candidateLapseInteraction interactionScale coefficients spatialRatio
          lapsePlus lapseMinus) = 0 := by
  unfold candidateLapseInteraction
  ring

/-- The pure minus-lapse second finite variation vanishes. -/
theorem minus_lapse_second_variation_vanishes
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (spatialRatio lapsePlus lapseMinus first second : ℝ) :
    (candidateLapseInteraction interactionScale coefficients spatialRatio
          lapsePlus (lapseMinus + first + second) -
        candidateLapseInteraction interactionScale coefficients spatialRatio
          lapsePlus (lapseMinus + first)) -
      (candidateLapseInteraction interactionScale coefficients spatialRatio
          lapsePlus (lapseMinus + second) -
        candidateLapseInteraction interactionScale coefficients spatialRatio
          lapsePlus lapseMinus) = 0 := by
  unfold candidateLapseInteraction
  ring

/-- There is no lapse-lapse mixed Hessian term either. -/
theorem mixed_lapse_second_variation_vanishes
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (spatialRatio lapsePlus lapseMinus plusIncrement minusIncrement : ℝ) :
    candidateLapseInteraction interactionScale coefficients spatialRatio
          (lapsePlus + plusIncrement) (lapseMinus + minusIncrement) -
        candidateLapseInteraction interactionScale coefficients spatialRatio
          (lapsePlus + plusIncrement) lapseMinus -
      (candidateLapseInteraction interactionScale coefficients spatialRatio
          lapsePlus (lapseMinus + minusIncrement) -
        candidateLapseInteraction interactionScale coefficients spatialRatio
          lapsePlus lapseMinus) = 0 := by
  unfold candidateLapseInteraction
  ring

/-- Honest ledger separating the proved reduced lapse algebra from the missing
full Hassan--Rosen constraint analysis. -/
structure ConstraintClosureStatus where
  reciprocalSpectralDensityReduced : Prop
  interactionLapseAffine : Prop
  primaryConstraintPrecursorsDerived : Prop
  admShiftRedefinitionDerived : Prop
  poissonBracketComputed : Prop
  independentSecondaryConstraintDerived : Prop
  boulwareDeserModeRemoved : Prop

def constraintClosed (status : ConstraintClosureStatus) : Prop :=
  status.reciprocalSpectralDensityReduced ∧
  status.interactionLapseAffine ∧
  status.primaryConstraintPrecursorsDerived ∧
  status.admShiftRedefinitionDerived ∧
  status.poissonBracketComputed ∧
  status.independentSecondaryConstraintDerived ∧
  status.boulwareDeserModeRemoved

/-- Lapse affinity and its primary precursors alone do not logically provide
the independent secondary constraint. -/
theorem lapse_linearity_alone_does_not_supply_secondary_constraint :
    ∃ status : ConstraintClosureStatus,
      status.reciprocalSpectralDensityReduced ∧
      status.interactionLapseAffine ∧
      status.primaryConstraintPrecursorsDerived ∧
      ¬ status.independentSecondaryConstraintDerived ∧
      ¬ constraintClosed status := by
  let status : ConstraintClosureStatus :=
    { reciprocalSpectralDensityReduced := True
      interactionLapseAffine := True
      primaryConstraintPrecursorsDerived := True
      admShiftRedefinitionDerived := False
      poissonBracketComputed := False
      independentSecondaryConstraintDerived := False
      boulwareDeserModeRemoved := False }
  refine ⟨status, trivial, trivial, trivial, ?_, ?_⟩
  · exact id
  · intro hClosed
    exact hClosed.2.2.2.2.2.1

end

end P0EFTJanusCandidateMinisuperspaceLapseConstraint
end JanusFormal
