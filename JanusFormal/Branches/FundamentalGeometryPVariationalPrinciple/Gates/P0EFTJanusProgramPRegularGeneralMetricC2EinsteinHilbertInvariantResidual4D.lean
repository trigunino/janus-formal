import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricInvariantEinsteinVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D

/-! # Invariant Einstein--Hilbert residual plus explicit Palatini flux -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertInvariantResidual4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameAnholonomicPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2MetricCompatiblePalatiniJet4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertCovariantDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothEinsteinCoefficients4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
open P0EFTJanusProgramPRegularGeneralMetricInvariantMaxwellStressVariation4D
open P0EFTJanusProgramPRegularGeneralMetricInvariantEinsteinVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Contraction of an inverse-metric velocity with covariant coefficients,
rewritten in the dual-frame order used by the invariant tensor pairing. -/
private theorem tensorPairing_neg_inverseVariation_eq_dualCoefficientSum
    (inverse variation coefficient : Matrix4)
    (hInverse : ∀ first second,
      inverse first second = inverse second first) :
    tensorPairing (-((inverse * variation) * inverse)) coefficient =
      -(∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
        coefficient lowerFirst lowerSecond *
          (∑ frameFirst : Fin 4, ∑ frameSecond : Fin 4,
            inverse lowerFirst frameFirst * inverse lowerSecond frameSecond *
              variation frameFirst frameSecond)) := by
  have hReindex :
      (∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
        ∑ frameSecond : Fin 4, ∑ frameFirst : Fin 4,
          inverse lowerFirst frameFirst * variation frameFirst frameSecond *
            inverse frameSecond lowerSecond *
              coefficient lowerFirst lowerSecond) =
        ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
          ∑ frameFirst : Fin 4, ∑ frameSecond : Fin 4,
            coefficient lowerFirst lowerSecond *
              (inverse lowerFirst frameFirst *
                inverse lowerSecond frameSecond *
                  variation frameFirst frameSecond) := by
    let swap :
        (Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
          (Fin 4 × Fin 4 × Fin 4 × Fin 4) :=
      { toFun := fun ⟨lowerFirst, lowerSecond, frameSecond, frameFirst⟩ =>
          (lowerFirst, lowerSecond, frameFirst, frameSecond)
        invFun := fun ⟨lowerFirst, lowerSecond, frameFirst, frameSecond⟩ =>
          (lowerFirst, lowerSecond, frameSecond, frameFirst)
        left_inv := by
          rintro ⟨lowerFirst, lowerSecond, frameSecond, frameFirst⟩
          rfl
        right_inv := by
          rintro ⟨lowerFirst, lowerSecond, frameFirst, frameSecond⟩
          rfl }
    let source : (Fin 4 × Fin 4 × Fin 4 × Fin 4) → Real :=
      fun ⟨lowerFirst, lowerSecond, frameSecond, frameFirst⟩ =>
        inverse lowerFirst frameFirst * variation frameFirst frameSecond *
          inverse frameSecond lowerSecond * coefficient lowerFirst lowerSecond
    let target : (Fin 4 × Fin 4 × Fin 4 × Fin 4) → Real :=
      fun ⟨lowerFirst, lowerSecond, frameFirst, frameSecond⟩ =>
        coefficient lowerFirst lowerSecond *
          (inverse lowerFirst frameFirst * inverse lowerSecond frameSecond *
            variation frameFirst frameSecond)
    have h := Fintype.sum_equiv swap source target (by
      rintro ⟨lowerFirst, lowerSecond, frameSecond, frameFirst⟩
      dsimp [source, target, swap]
      rw [hInverse frameSecond lowerSecond]
      ring)
    simpa only [source, target, Fintype.sum_prod_type] using h
  calc
    tensorPairing (-((inverse * variation) * inverse)) coefficient =
        -(∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
          ∑ frameSecond : Fin 4, ∑ frameFirst : Fin 4,
            inverse lowerFirst frameFirst * variation frameFirst frameSecond *
              inverse frameSecond lowerSecond *
                coefficient lowerFirst lowerSecond) := by
      unfold tensorPairing
      simp only [Matrix.neg_apply, Matrix.mul_apply]
      simp_rw [Finset.sum_mul]
      simp_rw [neg_mul, Finset.sum_mul]
      simp only [Finset.sum_neg_distrib]
    _ = -(∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
        ∑ frameFirst : Fin 4, ∑ frameSecond : Fin 4,
          coefficient lowerFirst lowerSecond *
            (inverse lowerFirst frameFirst * inverse lowerSecond frameSecond *
              variation frameFirst frameSecond)) := congrArg Neg.neg hReindex
    _ = _ := by
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro lowerFirst _
      apply Finset.sum_congr rfl
      intro lowerSecond _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro frameFirst _
      rw [Finset.mul_sum]

/-- Expansion of a covariant test tensor on the metric-dual regular frame. -/
private theorem dualFrameTensorPairing_expand_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : Fin 4) :
    variation.tensor point
        (regularFrameDualVectorAt period hPeriod metric point first)
        (regularFrameDualVectorAt period hPeriod metric point second) =
      ∑ frameFirst : Fin 4, ∑ frameSecond : Fin 4,
        regularFrameMetricInverseMatrixMap period hPeriod metric point
            first frameFirst *
          regularFrameMetricInverseMatrixMap period hPeriod metric point
            second frameSecond *
          variation.tensor point (metric.frame frameFirst point)
            (metric.frame frameSecond point) := by
  rw [regularFrameDualVectorAt_eq_sum period hPeriod metric point first]
  rw [map_sum]
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro frameFirst _
  rw [map_smul]
  simp only [smul_apply, smul_eq_mul]
  rw [regularFrameDualVectorAt_eq_sum period hPeriod metric point second]
  rw [map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro frameSecond _
  rw [map_smul]
  simp only [smul_eq_mul]
  ring

/-- The smooth Einstein coefficients are exactly the finite Einstein matrix
appearing in the Palatini density formula. -/
theorem regularGeneralMetricEinsteinCoefficientValue_eq_einsteinTensorAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real)
    (point : EffectiveQuotient period hPeriod)
    (first second : Fin 4) :
    regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
        cosmologicalConstant first second point =
      einsteinTensorAt
        (regularFrameMetricMatrixMap period hPeriod metric point)
        (regularGeneralMetricC0InverseMetricMatrixAt
          period hPeriod metric 0 point)
        (regularGeneralMetricC0RicciMatrixAt
          period hPeriod metric 0 point)
        cosmologicalConstant first second := by
  have hScalar := congrArg
    (fun field => field point)
    (regularGeneralMetricC0ScalarCurvature_zero period hPeriod metric)
  change regularGeneralMetricC0ScalarCurvature period hPeriod metric 0 point =
    globalSmoothScalarCurvature period hPeriod metric.metric point at hScalar
  have hScalarMatrix :
      scalarCurvatureAt
          (regularGeneralMetricC0InverseMetricMatrixAt period hPeriod metric 0
            point)
          (regularGeneralMetricC0RicciMatrixAt period hPeriod metric 0 point) =
        globalSmoothScalarCurvature period hPeriod metric.metric point := by
    calc
      _ = regularGeneralMetricC0ScalarCurvature period hPeriod metric 0
          point := by rfl
      _ = _ := hScalar
  simp only [regularGeneralMetricEinsteinCoefficientValue,
    regularGeneralMetricSmoothEinsteinCoefficient,
    regularGeneralMetricSmoothRicciCoefficient,
    smoothScalarFieldAdd_apply, smoothScalarFieldSub_apply,
    smoothScalarFieldSmul_toFun, smoothScalarFieldMul_apply]
  unfold einsteinTensorAt
  rw [hScalarMatrix]
  simp only [regularGeneralMetricC0RicciMatrixAt,
    regularFrameMetricMatrixMap]
  ring

/-- Arbitrary covariant coefficients contract with the inverse-metric velocity
as the negative metric-dual frame sum. No symmetry of the coefficients is needed. -/
theorem regularGeneralMetricC0InverseMetricVelocity_pairing_eq_dualFrameSum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (coefficient : Matrix4)
    (point : EffectiveQuotient period hPeriod) :
    tensorPairing
        (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod metric
          (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) point)
        coefficient =
      -(∑ first : Fin 4, ∑ second : Fin 4,
        coefficient first second * tensor.tensor point
          (regularFrameDualVectorAt period hPeriod metric point first)
          (regularFrameDualVectorAt period hPeriod metric point second)) := by
  let inverse := regularFrameMetricInverseMatrixMap period hPeriod metric point
  let variation := regularFrameCovariantVariationMatrixAt
    period hPeriod metric tensor point
  have hInverse : ∀ first second,
      inverse first second = inverse second first := by
    intro first second
    change (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹ first second =
      (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹ second first
    have hMetric : (regularFrameMetricMatrixMap period hPeriod metric point).transpose =
        regularFrameMetricMatrixMap period hPeriod metric point := by
      ext row column
      exact metric.metric.tensor.symmetric point _ _
    have hTranspose := Matrix.transpose_nonsing_inv
      (A := regularFrameMetricMatrixMap period hPeriod metric point)
    rw [hMetric] at hTranspose
    exact congrFun (congrFun hTranspose second) first
  rw [regularGeneralMetricC0InverseMetricVelocityAt_smooth]
  change tensorPairing (-((inverse * variation) * inverse)) coefficient = _
  rw [tensorPairing_neg_inverseVariation_eq_dualCoefficientSum inverse
    variation coefficient hInverse]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [dualFrameTensorPairing_expand_local]
  rfl

/-- The Einstein contraction in the exact C² density is the negative
invariant pairing with the covariant Einstein residual. -/
theorem regularGeneralMetricC0EinsteinInverseVelocity_pairing_invariant
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    tensorPairing
        (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod metric
          (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)
          point)
        (einsteinTensorAt
          (regularFrameMetricMatrixMap period hPeriod metric point)
          (regularGeneralMetricC0InverseMetricMatrixAt
            period hPeriod metric 0 point)
          (regularGeneralMetricC0RicciMatrixAt
            period hPeriod metric 0 point)
          cosmologicalConstant) =
      -generalMetricTensorPairingAt period hPeriod metric.metric
        (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
          cosmologicalConstant) tensor point := by
  let inverse := regularFrameMetricInverseMatrixMap period hPeriod metric point
  let variation := regularFrameCovariantVariationMatrixAt
    period hPeriod metric tensor point
  let coefficient : Matrix4 := fun first second =>
    regularGeneralMetricEinsteinCoefficientValue period hPeriod metric
      cosmologicalConstant first second point
  have hInverse : ∀ first second,
      inverse first second = inverse second first := by
    intro first second
    change (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹
        first second =
      (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹
        second first
    have hMetric :
        (regularFrameMetricMatrixMap period hPeriod metric point).transpose =
          regularFrameMetricMatrixMap period hPeriod metric point := by
      ext row column
      exact metric.metric.tensor.symmetric point _ _
    have hTranspose := Matrix.transpose_nonsing_inv
      (A := regularFrameMetricMatrixMap period hPeriod metric point)
    rw [hMetric] at hTranspose
    exact congrFun (congrFun hTranspose second) first
  rw [regularGeneralMetricC0InverseMetricVelocityAt_smooth]
  change tensorPairing (-((inverse * variation) * inverse)) _ = _
  rw [show einsteinTensorAt
        (regularFrameMetricMatrixMap period hPeriod metric point)
        (regularGeneralMetricC0InverseMetricMatrixAt period hPeriod metric 0
          point)
        (regularGeneralMetricC0RicciMatrixAt period hPeriod metric 0 point)
        cosmologicalConstant = coefficient by
    ext first second
    exact (regularGeneralMetricEinsteinCoefficientValue_eq_einsteinTensorAt
      period hPeriod metric cosmologicalConstant point first second).symm]
  rw [tensorPairing_neg_inverseVariation_eq_dualCoefficientSum inverse
    variation coefficient hInverse]
  apply congrArg Neg.neg
  rw [regularGeneralMetricSymmetricEinsteinTensor_pairing_eq_dualFrameSum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [dualFrameTensorPairing_expand_local]
  rfl

/-- Exact pointwise EH variation: invariant Einstein residual plus the smooth
Palatini divergence, with no hidden boundary hypothesis. -/
theorem regularGeneralMetricC0EinsteinHilbertDensityDerivative_smooth_invariantResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0EinsteinHilbertDensityDerivativeAtZero
        period hPeriod metric couplings
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)
        point =
      -(metric.volume point / (2 * couplings.gravitationalCoupling)) *
          generalMetricTensorPairingAt period hPeriod metric.metric
            (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
              couplings.cosmologicalConstant) tensor point +
        (metric.volume point / (2 * couplings.gravitationalCoupling)) *
          regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric
            tensor point := by
  rw [regularGeneralMetricC0EinsteinHilbertDensityDerivative_smooth_divergence]
  rw [regularGeneralMetricC0EinsteinInverseVelocity_pairing_invariant]
  rw [regularFrameSmoothPalatiniCovariantDivergence_apply]
  ring

/-- Integrated form of the invariant residual/Palatini split. -/
theorem regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_invariantResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
        period hPeriod metric measure couplings
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      ∫ point,
        (-(metric.volume point / (2 * couplings.gravitationalCoupling)) *
            generalMetricTensorPairingAt period hPeriod metric.metric
              (regularGeneralMetricSymmetricEinsteinTensor period hPeriod
                metric couplings.cosmologicalConstant) tensor point +
          (metric.volume point / (2 * couplings.gravitationalCoupling)) *
            regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric
              tensor point) ∂measure := by
  rw [regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_divergence]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point => by
    change
      (metric.volume point / (2 * couplings.gravitationalCoupling)) *
          (tensorPairing
              (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod
                metric
                (regularGeneralMetricC2SmoothDirection period hPeriod metric
                  tensor) point)
              (einsteinTensorAt
                (regularFrameMetricMatrixMap period hPeriod metric point)
                (regularGeneralMetricC0InverseMetricMatrixAt period hPeriod
                  metric 0 point)
                (regularGeneralMetricC0RicciMatrixAt period hPeriod metric 0
                  point) couplings.cosmologicalConstant) +
            regularFramePalatiniVectorCovariantDivergence
              (regularGeneralMetricC2MetricCompatiblePalatiniJetAt period
                hPeriod metric
                (regularGeneralMetricC2SmoothDirection period hPeriod metric
                  tensor) point)) = _
    dsimp only
    rw [regularGeneralMetricC0EinsteinInverseVelocity_pairing_invariant]
    rw [regularFrameSmoothPalatiniCovariantDivergence_apply]
    ring

/-- Gate marker for the fully invariant bulk metric residual with the sole
remaining EH obstruction exposed as the Palatini flux. -/
theorem regular_general_metric_c2_einstein_hilbert_invariant_residual_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
        period hPeriod metric measure couplings
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      ∫ point,
        (-(metric.volume point / (2 * couplings.gravitationalCoupling)) *
            generalMetricTensorPairingAt period hPeriod metric.metric
              (regularGeneralMetricSymmetricEinsteinTensor period hPeriod
                metric couplings.cosmologicalConstant) tensor point +
          (metric.volume point / (2 * couplings.gravitationalCoupling)) *
            regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric
              tensor point) ∂measure :=
  regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_invariantResidual
    period hPeriod metric measure couplings tensor

end
end P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertInvariantResidual4D
end JanusFormal
