import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFinitePeriodicHolonomicScalarVariation

/-!
# Finite metric-determinant holonomic scalar variation

This gate couples the periodic holonomic scalar model to one positive metric
coefficient.  The inverse metric weight is `sqrt(g) / g` and the mass weight
is `sqrt(g) m^2`, so the measure and inverse coefficient are induced by the
same metric variable rather than varied independently.  The simultaneous
metric/field derivative, the fixed-metric strong Euler equation, and the
metric-only response are actual derivatives.

This is a finite one-dimensional periodic metric model.  It is not a
continuum covariant scalar PDE, a four-dimensional determinant variation, or
a spacetime stress-energy conservation theorem.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteMetricHolonomicScalarVariation

set_option autoImplicit false

noncomputable section

open P0EFTJanusFinitePeriodicHolonomicScalarVariation

/-- Positive one-dimensional metric line. -/
def metricLine (metric metricVariation epsilon : ℝ) : ℝ :=
  metric + epsilon * metricVariation

/-- The induced `sqrt(g) g^{-1}` kinetic coefficient. -/
def metricKineticWeight (metric : ℝ) : ℝ :=
  Real.sqrt metric / metric

/-- The induced `sqrt(g) m^2` mass coefficient. -/
def metricMassWeight (metric massSquared : ℝ) : ℝ :=
  Real.sqrt metric * massSquared

/-- Exact variation of the induced kinetic coefficient. -/
def metricKineticWeightVariation
    (metric metricVariation : ℝ) : ℝ :=
  ((metricVariation / (2 * Real.sqrt metric)) * metric -
      Real.sqrt metric * metricVariation) / metric ^ 2

/-- Exact variation of the induced mass coefficient. -/
def metricMassWeightVariation
    (metric metricVariation massSquared : ℝ) : ℝ :=
  metricVariation / (2 * Real.sqrt metric) * massSquared

private theorem realIdentity_hasDerivAt (parameter : ℝ) :
    HasDerivAt (fun varied : ℝ => varied) 1 parameter := by
  exact hasDerivAt_id (x := parameter)

private theorem metricLine_hasDerivAt
    (metric metricVariation : ℝ) :
    HasDerivAt (metricLine metric metricVariation) metricVariation 0 := by
  have hRaw :=
    ((hasDerivAt_id (x := (0 : ℝ))).mul_const metricVariation).const_add
      metric
  refine (hRaw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    simp [metricLine]
  · ring

theorem metricKineticWeight_line_hasDerivAt
    (metric metricVariation : ℝ) (hMetric : 0 < metric) :
    HasDerivAt
      (fun epsilon => metricKineticWeight
        (metricLine metric metricVariation epsilon))
      (metricKineticWeightVariation metric metricVariation) 0 := by
  have hLine := metricLine_hasDerivAt metric metricVariation
  have hLineZero : metricLine metric metricVariation 0 ≠ 0 := by
    simpa [metricLine] using ne_of_gt hMetric
  have hSqrt := hLine.sqrt hLineZero
  have hRaw := hSqrt.div hLine hLineZero
  refine (hRaw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    rfl
  · simp [metricLine, metricKineticWeightVariation]

theorem metricMassWeight_line_hasDerivAt
    (metric metricVariation massSquared : ℝ) (hMetric : 0 < metric) :
    HasDerivAt
      (fun epsilon => metricMassWeight
        (metricLine metric metricVariation epsilon) massSquared)
      (metricMassWeightVariation metric metricVariation massSquared) 0 := by
  have hLine := metricLine_hasDerivAt metric metricVariation
  have hLineZero : metricLine metric metricVariation 0 ≠ 0 := by
    simpa [metricLine] using ne_of_gt hMetric
  simpa [metricMassWeight, metricMassWeightVariation, metricLine] using
    (hLine.sqrt hLineZero).mul_const massSquared

theorem metricKineticWeightVariation_eq
    (metric metricVariation : ℝ) (hMetric : 0 < metric) :
    metricKineticWeightVariation metric metricVariation =
      -metricVariation / (2 * metric * Real.sqrt metric) := by
  have hMetricZero : metric ≠ 0 := ne_of_gt hMetric
  have hSqrtZero : Real.sqrt metric ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hMetric)
  have hSquare := Real.sq_sqrt (le_of_lt hMetric)
  unfold metricKineticWeightVariation
  field_simp [hMetricZero, hSqrtZero]
  rw [hSquare]
  ring

/-- Scalar action with measure and inverse coefficient induced by one metric. -/
def metricHolonomicAction {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site) (massSquared metric : ℝ)
    (field : ScalarField Site) : ℝ :=
  scalarAction shift (metricKineticWeight metric)
    (metricMassWeight metric massSquared) field

/-- Simultaneous metric/holonomic-field first variation. -/
def metricHolonomicFirstVariation {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site) (massSquared metric metricVariation : ℝ)
    (field variation : ScalarField Site) : ℝ :=
  ∑ site, (
    (metricKineticWeightVariation metric metricVariation / 2) *
        (discreteGradient shift field site) ^ 2 +
      metricKineticWeight metric * discreteGradient shift field site *
        discreteGradient shift variation site +
      (metricMassWeightVariation metric metricVariation massSquared / 2) *
        (field site) ^ 2 +
      metricMassWeight metric massSquared * field site * variation site)

/-- The coupled measure/inverse-metric/holonomic-field formula is the actual
derivative along every simultaneous affine line. -/
theorem metricHolonomicAction_line_hasDerivAt
    {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site) (massSquared metric metricVariation : ℝ)
    (field variation : ScalarField Site) (hMetric : 0 < metric) :
    HasDerivAt
      (fun epsilon => metricHolonomicAction shift massSquared
        (metricLine metric metricVariation epsilon)
        (fieldLine field variation epsilon))
      (metricHolonomicFirstVariation shift massSquared metric metricVariation
        field variation) 0 := by
  unfold metricHolonomicAction scalarAction metricHolonomicFirstVariation
  apply HasDerivAt.fun_sum
  intro site _
  have hKineticWeight := metricKineticWeight_line_hasDerivAt
    metric metricVariation hMetric
  have hMassWeight := metricMassWeight_line_hasDerivAt
    metric metricVariation massSquared hMetric
  have hGradient := discreteGradient_fieldLine_hasDerivAt
    shift field variation site
  have hField : HasDerivAt
      (fun epsilon : ℝ => field site + epsilon * variation site)
      (variation site) 0 := by
    simpa using (realIdentity_hasDerivAt 0).mul_const (variation site)
      |>.const_add (field site)
  have hKinetic :=
    (hKineticWeight.mul (hGradient.mul hGradient)).const_mul (1 / 2 : ℝ)
  have hMass :=
    (hMassWeight.mul (hField.mul hField)).const_mul (1 / 2 : ℝ)
  refine ((hKinetic.add hMass).congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    simp [metricKineticWeight, metricMassWeight, metricLine, fieldLine,
      discreteGradient, pow_two]
    ring
  · simp [metricKineticWeight, metricMassWeight, metricLine, fieldLine,
      discreteGradient]
    ring

theorem metricHolonomicFirstVariation_fixedMetric
    {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site) (massSquared metric : ℝ)
    (field variation : ScalarField Site) :
    metricHolonomicFirstVariation shift massSquared metric 0 field variation =
      scalarActionFirstVariation shift (metricKineticWeight metric)
        (metricMassWeight metric massSquared) field variation := by
  unfold metricHolonomicFirstVariation scalarActionFirstVariation
  apply Finset.sum_congr rfl
  intro site _
  simp [metricKineticWeightVariation, metricMassWeightVariation]

/-- At fixed metric, the weak variation is exactly the pairing with the strong
nearest-neighbour Euler equation using induced coefficients. -/
theorem fixedMetric_firstVariation_eq_strongEuler_pairing
    {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site) (massSquared metric : ℝ)
    (field variation : ScalarField Site) :
    metricHolonomicFirstVariation shift massSquared metric 0 field variation =
      ∑ site,
        strongEuler shift (metricKineticWeight metric)
          (metricMassWeight metric massSquared) field site * variation site := by
  rw [metricHolonomicFirstVariation_fixedMetric]
  exact scalarActionFirstVariation_eq_strongEuler_pairing
    shift (metricKineticWeight metric) (metricMassWeight metric massSquared)
      field variation

theorem fixedMetric_stationary_iff_strongEuler_eq_zero
    {Site : Type*} [Fintype Site] [DecidableEq Site]
    (shift : Equiv.Perm Site) (massSquared metric : ℝ)
    (field : ScalarField Site) :
    (∀ variation : ScalarField Site,
      metricHolonomicFirstVariation shift massSquared metric 0
        field variation = 0) ↔
      strongEuler shift (metricKineticWeight metric)
        (metricMassWeight metric massSquared) field = 0 := by
  simpa [metricHolonomicFirstVariation_fixedMetric] using
    stationary_iff_strongEuler_eq_zero shift (metricKineticWeight metric)
      (metricMassWeight metric massSquared) field

/-- Metric-only response: the scalar value and its induced gradient are held
fixed while both measure and inverse coefficient vary through `g`. -/
theorem metricHolonomicAction_metricLine_hasDerivAt
    {Site : Type*} [Fintype Site]
    (shift : Equiv.Perm Site) (massSquared metric metricVariation : ℝ)
    (field : ScalarField Site) (hMetric : 0 < metric) :
    HasDerivAt
      (fun epsilon => metricHolonomicAction shift massSquared
        (metricLine metric metricVariation epsilon) field)
      (metricHolonomicFirstVariation shift massSquared metric metricVariation
        field 0) 0 := by
  refine (metricHolonomicAction_line_hasDerivAt shift massSquared metric
    metricVariation field 0 hMetric).congr_of_eventuallyEq
      (Filter.Eventually.of_forall ?_)
  intro epsilon
  apply congrArg (metricHolonomicAction shift massSquared
    (metricLine metric metricVariation epsilon))
  funext site
  simp [fieldLine]

end

end P0EFTJanusFiniteMetricHolonomicScalarVariation
end JanusFormal
