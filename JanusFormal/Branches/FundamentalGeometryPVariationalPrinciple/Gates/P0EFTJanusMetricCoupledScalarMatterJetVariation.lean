import Mathlib

/-!
# Metric-coupled scalar matter jet variation

This gate replaces the purely coordinate-quadratic matter proxy by an explicit
pointwise scalar first-jet density.  For an inverse metric `gInv`, scalar value
`phi`, gradient `p_mu`, and density measure `mu`, it uses

`mu * (1/2 gInv^{mu nu} p_mu p_nu + m2/2 phi^2 + source phi)`.

The simultaneous affine curve varies the measure, inverse metric, scalar and
gradient.  Its derivative is proved from actual `HasDerivAt` rules and finite
sums.  Separate field-, gradient-, metric- and measure-only corollaries expose
the corresponding Euler/stress slots, and the two Janus matter sectors are
shown to have zero mixed response.

This is pointwise first-jet algebra.  The scalar value and supplied gradient,
as well as the measure and inverse metric, are varied independently.  Thus the
coordinate slots below do not yet impose `delta p = d(delta phi)` or the
determinant relation for `delta sqrt(|g|)` and are not covariant field-space
Euler/stress variations.  No spacetime integration, covariant derivative,
wave equation, stress-energy conservation, or Hamiltonian positivity theorem
is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMetricCoupledScalarMatterJetVariation

set_option autoImplicit false

noncomputable section

abbrev Index4 := Fin 4
abbrev Vector4 := Index4 → ℝ
abbrev Matrix4 := Matrix Index4 Index4 ℝ

/-- Scalar value and its supplied coordinate first jet. -/
structure ScalarMatterJet where
  field : ℝ
  gradient : Vector4

/-- Pointwise kinetic scalar `1/2 gInv^{mu nu} p_mu p_nu`. -/
def scalarKinetic
    (inverseMetric : Matrix4) (gradient : Vector4) : ℝ :=
  (1 / 2 : ℝ) * ∑ first : Index4, ∑ second : Index4,
    inverseMetric first second * gradient first * gradient second

/-- Metric-coupled pointwise scalar matter Lagrangian. -/
def scalarMatterLagrangian
    (massSquared source : ℝ) (inverseMetric : Matrix4)
    (jet : ScalarMatterJet) : ℝ :=
  scalarKinetic inverseMetric jet.gradient +
    massSquared / 2 * jet.field ^ 2 + source * jet.field

/-- Coordinate scalar density with an explicit independent measure factor. -/
def scalarMatterDensity
    (measure massSquared source : ℝ) (inverseMetric : Matrix4)
    (jet : ScalarMatterJet) : ℝ :=
  measure * scalarMatterLagrangian massSquared source inverseMetric jet

/-- Affine line in scalar first-jet space. -/
def scalarJetLine
    (jet variation : ScalarMatterJet) (epsilon : ℝ) : ScalarMatterJet where
  field := jet.field + epsilon * variation.field
  gradient := fun index => jet.gradient index + epsilon * variation.gradient index

/-- Affine inverse-metric line. -/
def inverseMetricLine
    (inverseMetric variation : Matrix4) (epsilon : ℝ) : Matrix4 :=
  inverseMetric + epsilon • variation

/-- Exact first variation of the kinetic scalar. -/
def scalarKineticFirstVariation
    (inverseMetric metricVariation : Matrix4)
    (gradient gradientVariation : Vector4) : ℝ :=
  (1 / 2 : ℝ) * ∑ first : Index4, ∑ second : Index4,
    (metricVariation first second * gradient first * gradient second +
      inverseMetric first second * gradientVariation first * gradient second +
      inverseMetric first second * gradient first * gradientVariation second)

/-- Exact first variation of the scalar matter Lagrangian. -/
def scalarMatterFirstVariation
    (massSquared source : ℝ)
    (inverseMetric metricVariation : Matrix4)
    (jet variation : ScalarMatterJet) : ℝ :=
  scalarKineticFirstVariation inverseMetric metricVariation
      jet.gradient variation.gradient +
    massSquared * jet.field * variation.field +
    source * variation.field

/-- Exact first variation including the density measure. -/
def scalarMatterDensityFirstVariation
    (measure measureVariation massSquared source : ℝ)
    (inverseMetric metricVariation : Matrix4)
    (jet variation : ScalarMatterJet) : ℝ :=
  measureVariation *
      scalarMatterLagrangian massSquared source inverseMetric jet +
    measure * scalarMatterFirstVariation massSquared source
      inverseMetric metricVariation jet variation

private theorem triple_product_line_hasDerivAt
    (first firstVariation second secondVariation third thirdVariation : ℝ) :
    HasDerivAt
      (fun epsilon : ℝ =>
        (first + epsilon * firstVariation) *
          (second + epsilon * secondVariation) *
          (third + epsilon * thirdVariation))
      (firstVariation * second * third +
        first * secondVariation * third +
        first * second * thirdVariation) 0 := by
  have hFirst : HasDerivAt
      (fun epsilon : ℝ => first + epsilon * firstVariation)
      firstVariation 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).mul_const firstVariation
      |>.const_add first
  have hSecond : HasDerivAt
      (fun epsilon : ℝ => second + epsilon * secondVariation)
      secondVariation 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).mul_const secondVariation
      |>.const_add second
  have hThird : HasDerivAt
      (fun epsilon : ℝ => third + epsilon * thirdVariation)
      thirdVariation 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).mul_const thirdVariation
      |>.const_add third
  have hProduct := (hFirst.mul hSecond).mul hThird
  refine (hProduct.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    rfl
  · simp
    ring

/-- The kinetic formula is the genuine derivative of the simultaneous
inverse-metric/gradient affine curve. -/
theorem scalarKinetic_line_hasDerivAt
    (inverseMetric metricVariation : Matrix4)
    (gradient gradientVariation : Vector4) :
    HasDerivAt
      (fun epsilon => scalarKinetic
        (inverseMetricLine inverseMetric metricVariation epsilon)
        (fun index => gradient index + epsilon * gradientVariation index))
      (scalarKineticFirstVariation inverseMetric metricVariation
        gradient gradientVariation) 0 := by
  have hSum : HasDerivAt
      (fun epsilon : ℝ => ∑ first : Index4, ∑ second : Index4,
        (inverseMetric first second + epsilon * metricVariation first second) *
          (gradient first + epsilon * gradientVariation first) *
          (gradient second + epsilon * gradientVariation second))
      (∑ first : Index4, ∑ second : Index4,
        (metricVariation first second * gradient first * gradient second +
          inverseMetric first second * gradientVariation first * gradient second +
          inverseMetric first second * gradient first * gradientVariation second))
      0 := by
    apply HasDerivAt.fun_sum
    intro first _
    apply HasDerivAt.fun_sum
    intro second _
    exact triple_product_line_hasDerivAt
      (inverseMetric first second) (metricVariation first second)
      (gradient first) (gradientVariation first)
      (gradient second) (gradientVariation second)
  simpa [scalarKinetic, scalarKineticFirstVariation, inverseMetricLine,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
    hSum.const_mul (1 / 2 : ℝ)

/-- The displayed matter first variation is an actual derivative. -/
theorem scalarMatterLagrangian_line_hasDerivAt
    (massSquared source : ℝ)
    (inverseMetric metricVariation : Matrix4)
    (jet variation : ScalarMatterJet) :
    HasDerivAt
      (fun epsilon => scalarMatterLagrangian massSquared source
        (inverseMetricLine inverseMetric metricVariation epsilon)
        (scalarJetLine jet variation epsilon))
      (scalarMatterFirstVariation massSquared source
        inverseMetric metricVariation jet variation) 0 := by
  have hKinetic := scalarKinetic_line_hasDerivAt
    inverseMetric metricVariation jet.gradient variation.gradient
  have hField : HasDerivAt
      (fun epsilon : ℝ => jet.field + epsilon * variation.field)
      variation.field 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).mul_const variation.field
      |>.const_add jet.field
  have hMass := (hField.mul hField).const_mul (massSquared / 2)
  have hSource := hField.const_mul source
  have hRaw := (hKinetic.add hMass).add hSource
  refine (hRaw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    simp [scalarMatterLagrangian, scalarJetLine, pow_two]
  · simp [scalarMatterFirstVariation]
    ring

/-- Full metric/jet/measure affine variation of the density. -/
theorem scalarMatterDensity_line_hasDerivAt
    (measure measureVariation massSquared source : ℝ)
    (inverseMetric metricVariation : Matrix4)
    (jet variation : ScalarMatterJet) :
    HasDerivAt
      (fun epsilon => scalarMatterDensity
        (measure + epsilon * measureVariation) massSquared source
        (inverseMetricLine inverseMetric metricVariation epsilon)
        (scalarJetLine jet variation epsilon))
      (scalarMatterDensityFirstVariation measure measureVariation
        massSquared source inverseMetric metricVariation jet variation) 0 := by
  have hMeasure : HasDerivAt
      (fun epsilon : ℝ => measure + epsilon * measureVariation)
      measureVariation 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).mul_const measureVariation
      |>.const_add measure
  have hMatter := scalarMatterLagrangian_line_hasDerivAt
    massSquared source inverseMetric metricVariation jet variation
  have hRaw := hMeasure.mul hMatter
  refine (hRaw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    simp [scalarMatterDensity]
  · simp [scalarMatterDensityFirstVariation, inverseMetricLine, scalarJetLine]

/-- Coordinate field slot at fixed gradient, inverse metric and measure. -/
theorem scalarMatterDensity_fieldLine_hasDerivAt
    (measure massSquared source : ℝ) (inverseMetric : Matrix4)
    (jet : ScalarMatterJet) (fieldVariation : ℝ) :
    HasDerivAt
      (fun epsilon => scalarMatterDensity measure massSquared source inverseMetric
        { field := jet.field + epsilon * fieldVariation
          gradient := jet.gradient })
      (measure * (massSquared * jet.field + source) * fieldVariation) 0 := by
  have h := scalarMatterDensity_line_hasDerivAt measure 0 massSquared source
    inverseMetric 0 jet { field := fieldVariation, gradient := 0 }
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    simp [inverseMetricLine, scalarJetLine]
  · simp [scalarMatterDensityFirstVariation, scalarMatterFirstVariation,
      scalarKineticFirstVariation]
    ring

/-- Coordinate inverse-metric slot at fixed matter jet and measure. -/
theorem scalarMatterDensity_inverseMetricLine_hasDerivAt
    (measure massSquared source : ℝ)
    (inverseMetric metricVariation : Matrix4) (jet : ScalarMatterJet) :
    HasDerivAt
      (fun epsilon => scalarMatterDensity measure massSquared source
        (inverseMetricLine inverseMetric metricVariation epsilon) jet)
      (measure * ((1 / 2 : ℝ) * ∑ first : Index4, ∑ second : Index4,
        metricVariation first second * jet.gradient first * jet.gradient second)) 0 := by
  simpa [scalarJetLine, scalarMatterDensityFirstVariation,
    scalarMatterFirstVariation, scalarKineticFirstVariation] using
    scalarMatterDensity_line_hasDerivAt measure 0 massSquared source
      inverseMetric metricVariation jet { field := 0, gradient := 0 }

/-- Coordinate gradient slot at fixed scalar value, inverse metric and measure. -/
theorem scalarMatterDensity_gradientLine_hasDerivAt
    (measure massSquared source : ℝ) (inverseMetric : Matrix4)
    (jet : ScalarMatterJet) (gradientVariation : Vector4) :
    HasDerivAt
      (fun epsilon => scalarMatterDensity measure massSquared source inverseMetric
        { field := jet.field
          gradient := fun index =>
            jet.gradient index + epsilon * gradientVariation index })
      (measure * scalarKineticFirstVariation inverseMetric 0
        jet.gradient gradientVariation) 0 := by
  have h := scalarMatterDensity_line_hasDerivAt measure 0 massSquared source
    inverseMetric 0 jet { field := 0, gradient := gradientVariation }
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    simp [inverseMetricLine, scalarJetLine]
  · simp [scalarMatterDensityFirstVariation, scalarMatterFirstVariation]

/-- Density-measure slot at fixed inverse metric and matter jet. -/
theorem scalarMatterDensity_measureLine_hasDerivAt
    (measure measureVariation massSquared source : ℝ)
    (inverseMetric : Matrix4) (jet : ScalarMatterJet) :
    HasDerivAt
      (fun epsilon => scalarMatterDensity
        (measure + epsilon * measureVariation) massSquared source
        inverseMetric jet)
      (measureVariation *
        scalarMatterLagrangian massSquared source inverseMetric jet) 0 := by
  have h := scalarMatterDensity_line_hasDerivAt
    measure measureVariation massSquared source inverseMetric 0 jet
      { field := 0, gradient := 0 }
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    simp [inverseMetricLine, scalarJetLine]
  · simp [scalarMatterDensityFirstVariation, scalarMatterFirstVariation,
      scalarKineticFirstVariation]

/-- Two independent metric-coupled scalar matter sectors. -/
def twoSectorScalarMatterDensity
    (plusMeasure minusMeasure plusMassSquared minusMassSquared
      plusSource minusSource : ℝ)
    (plusInverseMetric minusInverseMetric : Matrix4)
    (plusJet minusJet : ScalarMatterJet) : ℝ :=
  scalarMatterDensity plusMeasure plusMassSquared plusSource
      plusInverseMetric plusJet +
    scalarMatterDensity minusMeasure minusMassSquared minusSource
      minusInverseMetric minusJet

/-- Varying the plus scalar field produces no minus-sector response. -/
theorem twoSector_plusFieldLine_hasDerivAt
    (plusMeasure minusMeasure plusMassSquared minusMassSquared
      plusSource minusSource : ℝ)
    (plusInverseMetric minusInverseMetric : Matrix4)
    (plusJet minusJet : ScalarMatterJet) (fieldVariation : ℝ) :
    HasDerivAt
      (fun epsilon => twoSectorScalarMatterDensity
        plusMeasure minusMeasure plusMassSquared minusMassSquared
        plusSource minusSource plusInverseMetric minusInverseMetric
        { field := plusJet.field + epsilon * fieldVariation
          gradient := plusJet.gradient } minusJet)
      (plusMeasure * (plusMassSquared * plusJet.field + plusSource) *
        fieldVariation) 0 := by
  have hPlus := scalarMatterDensity_fieldLine_hasDerivAt
    plusMeasure plusMassSquared plusSource plusInverseMetric plusJet fieldVariation
  have hMinus := hasDerivAt_const (x := (0 : ℝ))
    (c := scalarMatterDensity minusMeasure minusMassSquared minusSource
      minusInverseMetric minusJet)
  have hRaw := hPlus.add hMinus
  refine (hRaw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    simp [twoSectorScalarMatterDensity]
  · ring

/-- Exact zero mixed finite response of the independent matter blocks. -/
theorem twoSector_mixed_field_increment_eq_zero
    (plusMeasure minusMeasure plusMassSquared minusMassSquared
      plusSource minusSource : ℝ)
    (plusInverseMetric minusInverseMetric : Matrix4)
    (plusJet minusJet : ScalarMatterJet)
    (plusIncrement minusIncrement : ℝ) :
    (twoSectorScalarMatterDensity
        plusMeasure minusMeasure plusMassSquared minusMassSquared
        plusSource minusSource plusInverseMetric minusInverseMetric
        { plusJet with field := plusJet.field + plusIncrement }
        { minusJet with field := minusJet.field + minusIncrement } -
      twoSectorScalarMatterDensity
        plusMeasure minusMeasure plusMassSquared minusMassSquared
        plusSource minusSource plusInverseMetric minusInverseMetric
        { plusJet with field := plusJet.field + plusIncrement } minusJet) -
    (twoSectorScalarMatterDensity
        plusMeasure minusMeasure plusMassSquared minusMassSquared
        plusSource minusSource plusInverseMetric minusInverseMetric
        plusJet { minusJet with field := minusJet.field + minusIncrement } -
      twoSectorScalarMatterDensity
        plusMeasure minusMeasure plusMassSquared minusMassSquared
        plusSource minusSource plusInverseMetric minusInverseMetric
        plusJet minusJet) = 0 := by
  simp [twoSectorScalarMatterDensity, scalarMatterDensity,
    scalarMatterLagrangian]

end


end P0EFTJanusMetricCoupledScalarMatterJetVariation
end JanusFormal
