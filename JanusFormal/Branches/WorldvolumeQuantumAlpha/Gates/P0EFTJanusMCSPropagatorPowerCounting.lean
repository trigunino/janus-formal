import Mathlib

namespace JanusFormal.P0EFTJanusMCSPropagatorPowerCounting

set_option autoImplicit false

/-- Scalar coefficients of the inverse of
`K = a*p^2*P_T + kappa*E`, using `E^2=-p^2 P_T`. -/
structure MCSMomentumData where
  maxwellCoefficient : ℝ
  momentumSquared : ℝ
  chernSimonsCoefficient : ℝ
  maxwellCoefficientPositive : 0 < maxwellCoefficient
  momentumSquaredPositive : 0 < momentumSquared

noncomputable def transverseCoefficient (s : MCSMomentumData) : ℝ :=
  s.maxwellCoefficient /
    (s.maxwellCoefficient ^ 2 * s.momentumSquared +
      s.chernSimonsCoefficient ^ 2)

noncomputable def oddCoefficient (s : MCSMomentumData) : ℝ :=
  -s.chernSimonsCoefficient /
    (s.momentumSquared *
      (s.maxwellCoefficient ^ 2 * s.momentumSquared +
        s.chernSimonsCoefficient ^ 2))

theorem mcs_denominator_positive (s : MCSMomentumData) :
    0 < s.maxwellCoefficient ^ 2 * s.momentumSquared +
      s.chernSimonsCoefficient ^ 2 := by
  have hMaxwellSquare : 0 < s.maxwellCoefficient ^ 2 :=
    sq_pos_of_pos s.maxwellCoefficientPositive
  exact add_pos_of_pos_of_nonneg
    (mul_pos hMaxwellSquare s.momentumSquaredPositive)
    (sq_nonneg s.chernSimonsCoefficient)

/-- The proposed coefficients multiply to the transverse identity. -/
theorem mcs_inverse_coefficient_equations (s : MCSMomentumData) :
    s.maxwellCoefficient * s.momentumSquared * transverseCoefficient s -
        s.chernSimonsCoefficient * oddCoefficient s * s.momentumSquared = 1 ∧
      s.maxwellCoefficient * s.momentumSquared * oddCoefficient s +
        s.chernSimonsCoefficient * transverseCoefficient s = 0 := by
  have hDenom :
      s.maxwellCoefficient ^ 2 * s.momentumSquared +
        s.chernSimonsCoefficient ^ 2 ≠ 0 :=
    ne_of_gt (mcs_denominator_positive s)
  have hMomentum : s.momentumSquared ≠ 0 :=
    ne_of_gt s.momentumSquaredPositive
  unfold transverseCoefficient oddCoefficient
  constructor <;> field_simp [hDenom, hMomentum] <;> ring

/-- Connected gauge rings from `eta^n F^2` vertices are superficially cubic:
`omega = 3L + 2V - 2I = 3` for `L=1` and `I=V`. -/
theorem gauge_ring_superficial_degree_three
    (vertices internalEdges loops degree : ℤ)
    (hRing : internalEdges = vertices)
    (hOneLoop : loops = 1)
    (hDegree : degree = 3 * loops + 2 * vertices - 2 * internalEdges) :
    degree = 3 := by
  omega

/-- Cubic superficial degree does not itself determine a beta function:
power divergences depend on regulator/subtraction, while the logarithmic part
must be extracted from the full tensor integral. -/
structure MCSLoopRenormalizationStatus where
  transversePropagatorDerived : Prop
  longitudinalGaugeBlockDerived : Prop
  topologicalPolePrescriptionFixed : Prop
  regulatedTensorIntegralsComputed : Prop
  powerDivergencesSubtracted : Prop
  logarithmicResidueExtracted : Prop

def mcsLoopRenormalizationClosed
    (s : MCSLoopRenormalizationStatus) : Prop :=
  s.transversePropagatorDerived ∧
  s.longitudinalGaugeBlockDerived ∧
  s.topologicalPolePrescriptionFixed ∧
  s.regulatedTensorIntegralsComputed ∧
  s.powerDivergencesSubtracted ∧
  s.logarithmicResidueExtracted

end JanusFormal.P0EFTJanusMCSPropagatorPowerCounting
