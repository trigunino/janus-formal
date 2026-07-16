import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusHolonomicScalarFieldVariation4D

/-!
# Simultaneous holonomic scalar and metric variation in four dimensions

This gate varies one metric and one genuine scalar field along the same real
parameter.  The determinant measure and inverse are induced by that metric,
while the scalar value and covector are induced by one differentiable function.
The pointwise derivative therefore combines the metric stress contribution and
the holonomic `p = d phi` contribution without treating either as independent.

The result is local to the global flat `R^4` chart.  Integration by parts, the
curved wave equation and stress conservation are not asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusHolonomicMetricScalarVariation4D

set_option autoImplicit false

noncomputable section

open Filter
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusHolonomicScalarFieldVariation4D

abbrev Coordinate4 := P0EFTJanusHolonomicScalarFieldVariation4D.Coordinate4
abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

/-- Simultaneous curve: measure and inverse come from the metric curve, while
the matter jet comes from the actual affine scalar-field line. -/
def holonomicMetricScalarDensityCurve
    (data : FixedSignMetric4) (metricVariation : SymmetricMetricVariation4)
    (massSquared source : Real) (field fieldVariation : Coordinate4 → Real)
    (point : Coordinate4) (epsilon : Real) : Real :=
  Real.sqrt |Matrix.det (metricCurve data metricVariation epsilon)| *
    scalarMatterLagrangian massSquared source
      (exactInverseMetricCurve data metricVariation epsilon)
      (holonomicScalarJet
        (scalarFieldLine field fieldVariation epsilon) point)

/-- The exact simultaneous first-variation coefficient. -/
def holonomicMetricScalarDensityFirstVariation
    (data : FixedSignMetric4) (metricVariation : SymmetricMetricVariation4)
    (massSquared source : Real) (field fieldVariation : Coordinate4 → Real)
    (point : Coordinate4) : Real :=
  scalarMatterDensityFirstVariation
    (Real.sqrt |Matrix.det data.metric|)
    ((Real.sqrt |Matrix.det data.metric| / 2) *
      Matrix.trace (relativeMetricVariation data metricVariation))
    massSquared source data.metric⁻¹
    (-(data.metric⁻¹ * metricVariation.tensor * data.metric⁻¹))
    (holonomicScalarJet field point)
    (holonomicScalarJet fieldVariation point)

private theorem exactInverseMetricCurve_entry_hasDerivAt
    (data : FixedSignMetric4) (metricVariation : SymmetricMetricVariation4)
    (first second : Index4) :
    FrobeniusScalarHasDerivAt
      (fun epsilon ↦ exactInverseMetricCurve data metricVariation epsilon first second)
      ((-(data.metric⁻¹ * metricVariation.tensor * data.metric⁻¹)) first second) 0 := by
  unfold FrobeniusScalarHasDerivAt
  letI : NormedAddCommGroup Real := Real.normedAddCommGroup
  letI : NormedSpace Real Real :=
    (RCLike.toInnerProductSpaceReal : InnerProductSpace Real Real).toNormedSpace
  letI : NormedAddCommGroup Matrix4 := Matrix.frobeniusNormedAddCommGroup
  letI : NormedSpace Real Matrix4 := Matrix.frobeniusNormedSpace
  let row : Matrix4 →L[Real] (Index4 → Real) :=
    ContinuousLinearMap.proj first
  let entry : Matrix4 →L[Real] Real :=
    (ContinuousLinearMap.proj second : (Index4 → Real) →L[Real] Real).comp row
  have hInverse := exactInverseMetricCurve_hasDerivAt data metricVariation
  unfold FrobeniusMatrixHasDerivAt at hInverse
  have hEntryF := entry.hasFDerivAt.comp 0 hInverse
  have hDerivative :
      entry.comp (ContinuousLinearMap.toSpanSingleton Real
        (-(data.metric⁻¹ * metricVariation.tensor * data.metric⁻¹))) =
      ContinuousLinearMap.toSpanSingleton Real
        ((-(data.metric⁻¹ * metricVariation.tensor * data.metric⁻¹)) first second) := by
    apply ContinuousLinearMap.ext
    intro scalar
    change entry (scalar •
      (-(data.metric⁻¹ * metricVariation.tensor * data.metric⁻¹))) =
        scalar * (-(data.metric⁻¹ * metricVariation.tensor * data.metric⁻¹)) first second
    change (scalar •
      (-(data.metric⁻¹ * metricVariation.tensor * data.metric⁻¹))) first second =
        scalar * (-(data.metric⁻¹ * metricVariation.tensor * data.metric⁻¹)) first second
    simp
  have hFunction :
      (fun epsilon ↦ exactInverseMetricCurve data metricVariation epsilon first second) =
        entry ∘ exactInverseMetricCurve data metricVariation := by
    funext epsilon
    rfl
  rw [hFunction, ← hDerivative]
  exact hEntryF

private theorem scalarMatter_exactInverse_holonomic_hasDerivAt
    (data : FixedSignMetric4) (metricVariation : SymmetricMetricVariation4)
    (massSquared source : Real) (field fieldVariation : Coordinate4 → Real)
    (point : Coordinate4)
    (hField : DifferentiableAt Real field point)
    (hFieldVariation : DifferentiableAt Real fieldVariation point) :
    FrobeniusScalarHasDerivAt
      (fun epsilon ↦ scalarMatterLagrangian massSquared source
        (exactInverseMetricCurve data metricVariation epsilon)
        (holonomicScalarJet (scalarFieldLine field fieldVariation epsilon) point))
      (scalarMatterFirstVariation massSquared source data.metric⁻¹
        (-(data.metric⁻¹ * metricVariation.tensor * data.metric⁻¹))
        (holonomicScalarJet field point)
        (holonomicScalarJet fieldVariation point)) 0 := by
  unfold FrobeniusScalarHasDerivAt
  letI : NormedAddCommGroup Real := Real.normedAddCommGroup
  letI : NormedSpace Real Real :=
    (RCLike.toInnerProductSpaceReal : InnerProductSpace Real Real).toNormedSpace
  let jet := holonomicScalarJet field point
  let jetVariation := holonomicScalarJet fieldVariation point
  let inverseVariation :=
    -(data.metric⁻¹ * metricVariation.tensor * data.metric⁻¹)
  have hJet (epsilon : Real) :
      holonomicScalarJet (scalarFieldLine field fieldVariation epsilon) point =
        scalarJetLine jet jetVariation epsilon := by
    exact holonomicScalarJet_scalarFieldLine field fieldVariation point epsilon
      hField hFieldVariation
  have hInverseEntry (first second : Index4) :
      HasDerivAt
        (fun epsilon ↦ exactInverseMetricCurve data metricVariation epsilon first second)
        (inverseVariation first second) 0 := by
    have hEntry := exactInverseMetricCurve_entry_hasDerivAt
      data metricVariation first second
    unfold FrobeniusScalarHasDerivAt at hEntry
    have hEntryDeriv := hEntry.hasDerivAt
    have hCoefficient :
        (ContinuousLinearMap.toSpanSingleton Real
          ((-(data.metric⁻¹ * metricVariation.tensor * data.metric⁻¹)) first second)) 1 =
          inverseVariation first second := by
      simp [inverseVariation]
    exact hEntryDeriv.congr_deriv hCoefficient
  have hGradient (index : Index4) :
      HasDerivAt
        (fun epsilon ↦ (scalarJetLine jet jetVariation epsilon).gradient index)
        (jetVariation.gradient index) 0 := by
    simpa [scalarJetLine] using
      ((hasDerivAt_id (x := (0 : Real))).mul_const
        (jetVariation.gradient index)).const_add (jet.gradient index)
  have hKineticSum : HasDerivAt
      (fun epsilon ↦ ∑ first : Index4, ∑ second : Index4,
        exactInverseMetricCurve data metricVariation epsilon first second *
          (scalarJetLine jet jetVariation epsilon).gradient first *
          (scalarJetLine jet jetVariation epsilon).gradient second)
      (∑ first : Index4, ∑ second : Index4,
        (inverseVariation first second * jet.gradient first * jet.gradient second +
          data.metric⁻¹ first second * jetVariation.gradient first * jet.gradient second +
          data.metric⁻¹ first second * jet.gradient first * jetVariation.gradient second)) 0 := by
    apply HasDerivAt.fun_sum
    intro first _
    apply HasDerivAt.fun_sum
    intro second _
    have hProduct :=
      ((hInverseEntry first second).mul (hGradient first)).mul (hGradient second)
    refine hProduct.congr_deriv ?_
    simp [jet, jetVariation, inverseVariation, scalarJetLine,
      exactInverseMetricCurve_zero]
    ring
  have hKinetic : HasDerivAt
      (fun epsilon ↦ scalarKinetic
        (exactInverseMetricCurve data metricVariation epsilon)
        (scalarJetLine jet jetVariation epsilon).gradient)
      (scalarKineticFirstVariation data.metric⁻¹ inverseVariation
        jet.gradient jetVariation.gradient) 0 := by
    simpa [scalarKinetic, scalarKineticFirstVariation] using
      hKineticSum.const_mul (1 / 2 : Real)
  have hFieldLine : HasDerivAt
      (fun epsilon ↦ (scalarJetLine jet jetVariation epsilon).field)
      jetVariation.field 0 := by
    simpa [scalarJetLine] using
      ((hasDerivAt_id (x := (0 : Real))).mul_const jetVariation.field)
        |>.const_add jet.field
  have hMass := (hFieldLine.mul hFieldLine).const_mul (massSquared / 2)
  have hSource := hFieldLine.const_mul source
  have hMatter := (hKinetic.add hMass).add hSource
  have hMatterCorrect : HasDerivAt
      (fun epsilon ↦ scalarMatterLagrangian massSquared source
        (exactInverseMetricCurve data metricVariation epsilon)
        (scalarJetLine jet jetVariation epsilon))
      (scalarMatterFirstVariation massSquared source data.metric⁻¹
        inverseVariation jet jetVariation) 0 := by
    refine (hMatter.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun epsilon ↦ ?_)).congr_deriv ?_
    · simp [scalarMatterLagrangian, scalarJetLine, pow_two]
    · simp [scalarMatterFirstVariation, inverseVariation, scalarJetLine,
        scalarKineticFirstVariation]
      ring
  refine (hMatterCorrect.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun epsilon ↦ ?_)).congr_deriv ?_ |>.hasFDerivAt
  · rw [hJet epsilon]
  · rfl

/-- Pointwise simultaneous derivative on one genuine metric/field curve. -/
theorem holonomicMetricScalarDensityCurve_hasDerivAt
    (data : FixedSignMetric4) (metricVariation : SymmetricMetricVariation4)
    (massSquared source : Real) (field fieldVariation : Coordinate4 → Real)
    (point : Coordinate4)
    (hField : DifferentiableAt Real field point)
    (hFieldVariation : DifferentiableAt Real fieldVariation point) :
    FrobeniusScalarHasDerivAt
      (holonomicMetricScalarDensityCurve data metricVariation massSquared source
        field fieldVariation point)
      (holonomicMetricScalarDensityFirstVariation data metricVariation
        massSquared source field fieldVariation point) 0 := by
  unfold FrobeniusScalarHasDerivAt
  have hMeasure := metricMeasureCurve_hasDerivAt data metricVariation
  have hMatter := scalarMatter_exactInverse_holonomic_hasDerivAt
    data metricVariation massSquared source field fieldVariation point
    hField hFieldVariation
  unfold FrobeniusScalarHasDerivAt at hMatter
  have hMatterDeriv := hMatter.hasDerivAt
  have hProduct := hMeasure.mul hMatterDeriv
  refine (hProduct.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun epsilon ↦ ?_)).congr_deriv ?_ |>.hasFDerivAt
  · rfl
  · rw [holonomicScalarJet_scalarFieldLine field fieldVariation point 0
      hField hFieldVariation]
    simp [holonomicMetricScalarDensityFirstVariation,
      scalarMatterDensityFirstVariation, relativeMetricVariation,
      scalarJetLine, holonomicScalarJet]

/-- The coefficient separates exactly into the fixed-field metric derivative
and the fixed-metric holonomic field derivative. -/
theorem holonomicMetricScalarDensityFirstVariation_split
    (data : FixedSignMetric4) (metricVariation : SymmetricMetricVariation4)
    (massSquared source : Real) (field fieldVariation : Coordinate4 → Real)
    (point : Coordinate4) :
    holonomicMetricScalarDensityFirstVariation data metricVariation
        massSquared source field fieldVariation point =
        metricInducedScalarDensityFirstVariation data metricVariation
        massSquared source (holonomicScalarJet field point) +
      holonomicScalarDensityFirstVariation data massSquared source
        field fieldVariation point := by
  unfold holonomicMetricScalarDensityFirstVariation
  unfold metricInducedScalarDensityFirstVariation
  unfold holonomicScalarDensityFirstVariation
  rw [show relativeMetricVariation data metricVariation =
    data.metric⁻¹ * metricVariation.tensor from rfl]
  simp [scalarMatterDensityFirstVariation, scalarMatterFirstVariation,
    scalarKineticFirstVariation, scalarKinetic, Finset.sum_add_distrib]
  ring

end

end P0EFTJanusHolonomicMetricScalarVariation4D
end JanusFormal
