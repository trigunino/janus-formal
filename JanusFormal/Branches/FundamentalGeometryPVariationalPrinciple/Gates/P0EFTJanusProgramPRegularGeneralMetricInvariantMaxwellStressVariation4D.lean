import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricMaxwellStressVariationBridge4D

/-! # Invariant Maxwell stress variation and integrated pairing -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricInvariantMaxwellStressVariation4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothMaxwellStressTensor4D
open P0EFTJanusProgramPRegularGeneralMetricMaxwellStressVariationBridge4D
open P0EFTJanusMappingTorusLocalMaxwellStressVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

/-- Vector metric-dual to one covector of the reconstructed regular coframe. -/
def regularFrameDualVectorAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    TangentSpace coverModelWithCorners point :=
  (metric.metric.musical point).symm
    (regularFrameDualCovector period hPeriod metric index point)

theorem regularFrameDualVectorAt_metric_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4)
    (vector : TangentSpace coverModelWithCorners point) :
    metric.metric.tensor.tensor point
        (regularFrameDualVectorAt period hPeriod metric point index) vector =
      regularFrameDualCovector period hPeriod metric index point vector := by
  rw [← DFunLike.congr_fun
    (DFunLike.congr_fun (metric.metric.musical_eq_tensor point)
      (regularFrameDualVectorAt period hPeriod metric point index)) vector]
  unfold regularFrameDualVectorAt
  exact DFunLike.congr_fun
    ((metric.metric.musical point).apply_symm_apply
      (regularFrameDualCovector period hPeriod metric index point)) vector

/-- The metric-dual coframe vectors have the inverse-Gram expansion. -/
theorem regularFrameDualVectorAt_eq_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    regularFrameDualVectorAt period hPeriod metric point index =
      ∑ column : Fin 4,
        regularFrameMetricInverseMatrixMap period hPeriod metric point
            index column • metric.frame column point := by
  unfold regularFrameDualVectorAt
  apply (metric.metric.musical point).injective
  rw [(metric.metric.musical point).apply_symm_apply]
  rw [map_sum]
  apply ContinuousLinearMap.ext
  intro vector
  simp only [sum_apply, map_smul, smul_apply, smul_eq_mul]
  rw [regularFrameDualCovector_apply]
  apply Finset.sum_congr rfl
  intro column _
  rw [← DFunLike.congr_fun
    (DFunLike.congr_fun (metric.metric.musical_eq_tensor point)
      (metric.frame column point)) vector]
  rfl

private theorem dualFrameTensorPairing_expand
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

/-- Invariant pairing with the reconstructed Maxwell stress is its coframe
coefficient sum. -/
theorem regularGeneralMetricMaxwellStressTensor_pairing_eq_dualFrameSum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric.metric
        (regularGeneralMetricMaxwellStressTensor period hPeriod metric
          potential) variation point =
      ∑ first : Fin 4, ∑ second : Fin 4,
        regularFrameMaxwellStressCoefficient period hPeriod metric potential
            first second point *
          variation.tensor point
            (regularFrameDualVectorAt period hPeriod metric point first)
            (regularFrameDualVectorAt period hPeriod metric point second) := by
  rw [generalMetricTensorPairingAt_symmetric]
  let pairing :
      SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] Real :=
    { toFun := fun tensor =>
        generalMetricTensorPairingAt period hPeriod metric.metric variation
          tensor point
      map_add' := by
        intro first second
        exact generalMetricTensorPairingAt_add_right period hPeriod
          metric.metric variation first second point
      map_smul' := by
        intro scalar tensor
        exact generalMetricTensorPairingAt_smul_right period hPeriod
          metric.metric scalar variation tensor point }
  change pairing
      (regularGeneralMetricMaxwellStressTensor period hPeriod metric
        potential) = _
  unfold regularGeneralMetricMaxwellStressTensor
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro second _
  let rankOne := smoothBulkCovectorSymmetricProduct period hPeriod
    (regularFrameDualCovector period hPeriod metric first)
    (regularFrameDualCovector period hPeriod metric second)
  have hCongr :
      pairing
          (smoothBulkScalarSMulTensor period hPeriod
            (regularFrameMaxwellStressCoefficient period hPeriod metric
              potential first second) rankOne) =
        pairing
          ((regularFrameMaxwellStressCoefficient period hPeriod metric
            potential first second point) • rankOne) := by
    apply generalMetricTensorPairingAt_congr_right_at
    apply ContinuousLinearMap.ext
    intro left
    apply ContinuousLinearMap.ext
    intro right
    rfl
  rw [hCongr, map_smul]
  apply congrArg
    (regularFrameMaxwellStressCoefficient period hPeriod metric potential
      first second point * ·)
  apply generalMetricTensorPairingAt_symmetricMetricRankOne
    (first := regularFrameDualVectorAt period hPeriod metric point first)
    (second := regularFrameDualVectorAt period hPeriod metric point second)
  intro left right
  change
    (1 / 2 : Real) *
          (regularFrameDualCovector period hPeriod metric first point left *
            regularFrameDualCovector period hPeriod metric second point right) +
        (1 / 2 : Real) *
          (regularFrameDualCovector period hPeriod metric second point left *
            regularFrameDualCovector period hPeriod metric first point right) =
      _
  rw [← regularFrameDualVectorAt_metric_pairing,
    ← regularFrameDualVectorAt_metric_pairing,
    ← regularFrameDualVectorAt_metric_pairing,
    ← regularFrameDualVectorAt_metric_pairing]

private theorem raisedCovariantMatrixPairing_eq_dualFrameSum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    raisedCovariantMatrixPairingAt
        (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (fun first second => tensor.tensor point
          (metric.frame first point) (metric.frame second point))
        (fun first second => variation.tensor point
          (metric.frame first point) (metric.frame second point)) =
      ∑ first : Fin 4, ∑ second : Fin 4,
        tensor.tensor point (metric.frame first point)
            (metric.frame second point) *
          variation.tensor point
            (regularFrameDualVectorAt period hPeriod metric point first)
            (regularFrameDualVectorAt period hPeriod metric point second) := by
  let inverse := regularFrameMetricInverseMatrixMap period hPeriod metric point
  let tensorMatrix : Matrix (Fin 4) (Fin 4) Real := fun first second =>
    tensor.tensor point (metric.frame first point) (metric.frame second point)
  let variationMatrix : Matrix (Fin 4) (Fin 4) Real := fun first second =>
    variation.tensor point (metric.frame first point) (metric.frame second point)
  have hInverse : ∀ first second,
      inverse first second = inverse second first := by
    intro first second
    change (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹
        first second =
      (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹ second first
    have hMetric :
        (regularFrameMetricMatrixMap period hPeriod metric point).transpose =
          regularFrameMetricMatrixMap period hPeriod metric point := by
      ext row column
      exact metric.metric.tensor.symmetric point _ _
    have hTranspose := Matrix.transpose_nonsing_inv
      (A := regularFrameMetricMatrixMap period hPeriod metric point)
    rw [hMetric] at hTranspose
    exact congrFun (congrFun hTranspose second) first
  have hReindex :
      (∑ frameFirst : Fin 4, ∑ frameSecond : Fin 4,
        ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
          inverse frameFirst lowerFirst * inverse frameSecond lowerSecond *
            tensorMatrix lowerFirst lowerSecond *
            variationMatrix frameFirst frameSecond) =
        ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
          ∑ frameFirst : Fin 4, ∑ frameSecond : Fin 4,
            tensorMatrix lowerFirst lowerSecond *
              (inverse lowerFirst frameFirst * inverse lowerSecond frameSecond *
                variationMatrix frameFirst frameSecond) := by
    let swap :
        (Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
          (Fin 4 × Fin 4 × Fin 4 × Fin 4) :=
      { toFun := fun ⟨frameFirst, frameSecond, lowerFirst, lowerSecond⟩ =>
          (lowerFirst, lowerSecond, frameFirst, frameSecond)
        invFun := fun ⟨lowerFirst, lowerSecond, frameFirst, frameSecond⟩ =>
          (frameFirst, frameSecond, lowerFirst, lowerSecond)
        left_inv := by rintro ⟨frameFirst, frameSecond, lowerFirst, lowerSecond⟩; rfl
        right_inv := by rintro ⟨lowerFirst, lowerSecond, frameFirst, frameSecond⟩; rfl }
    let source : (Fin 4 × Fin 4 × Fin 4 × Fin 4) → Real :=
      fun ⟨frameFirst, frameSecond, lowerFirst, lowerSecond⟩ =>
        inverse frameFirst lowerFirst * inverse frameSecond lowerSecond *
          tensorMatrix lowerFirst lowerSecond *
          variationMatrix frameFirst frameSecond
    let target : (Fin 4 × Fin 4 × Fin 4 × Fin 4) → Real :=
      fun ⟨lowerFirst, lowerSecond, frameFirst, frameSecond⟩ =>
        tensorMatrix lowerFirst lowerSecond *
          (inverse lowerFirst frameFirst * inverse lowerSecond frameSecond *
            variationMatrix frameFirst frameSecond)
    have h := Fintype.sum_equiv swap source target (by
      rintro ⟨frameFirst, frameSecond, lowerFirst, lowerSecond⟩
      dsimp [source, target, swap]
      rw [hInverse frameFirst lowerFirst,
        hInverse frameSecond lowerSecond]
      ring)
    simpa only [source, target, Fintype.sum_prod_type] using h
  unfold raisedCovariantMatrixPairingAt
  change
    (∑ frameFirst : Fin 4, ∑ frameSecond : Fin 4,
      (∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
        inverse frameFirst lowerFirst * inverse frameSecond lowerSecond *
          tensorMatrix lowerFirst lowerSecond) *
        variationMatrix frameFirst frameSecond) = _
  calc
    _ = ∑ frameFirst : Fin 4, ∑ frameSecond : Fin 4,
        ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
          inverse frameFirst lowerFirst * inverse frameSecond lowerSecond *
            tensorMatrix lowerFirst lowerSecond *
            variationMatrix frameFirst frameSecond := by
      apply Finset.sum_congr rfl
      intro frameFirst _
      apply Finset.sum_congr rfl
      intro frameSecond _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro lowerFirst _
      rw [Finset.sum_mul]
    _ = ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
        ∑ frameFirst : Fin 4, ∑ frameSecond : Fin 4,
          tensorMatrix lowerFirst lowerSecond *
            (inverse lowerFirst frameFirst * inverse lowerSecond frameSecond *
              variationMatrix frameFirst frameSecond) := hReindex
    _ = _ := by
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      rw [dualFrameTensorPairing_expand]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro frameFirst _
      rw [Finset.mul_sum]

/-- The frame formula of Gate466 is the invariant Lorentz tensor pairing. -/
theorem regularGeneralMetricMaxwellStress_variation_invariant
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    variationalMaxwellStressPairing
        (regularFrameMetricInverseMatrixMap period hPeriod metric point)
        (fun component first second =>
          regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
            component first second point)
        (fun first second => variation.tensor point
          (metric.frame first point) (metric.frame second point)) =
      generalMetricTensorPairingAt period hPeriod metric.metric
        (regularGeneralMetricMaxwellStressTensor period hPeriod metric
          potential) variation point := by
  rw [regularGeneralMetricMaxwellStress_variation_frame]
  rw [raisedCovariantMatrixPairing_eq_dualFrameSum]
  simpa only [regularGeneralMetricMaxwellStressTensor_frame] using
    (regularGeneralMetricMaxwellStressTensor_pairing_eq_dualFrameSum
      period hPeriod metric potential variation point).symm

/-- The pointwise identification transports through every measure integral. -/
theorem integral_regularGeneralMetricMaxwellStress_variation_invariant
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (∫ point,
      metric.volume point / 2 *
        variationalMaxwellStressPairing
          (regularFrameMetricInverseMatrixMap period hPeriod metric point)
          (fun component first second =>
            regularFrameGaugeCurvatureCoefficient period hPeriod metric
              potential component first second point)
          (fun first second => variation.tensor point
            (metric.frame first point) (metric.frame second point))
      ∂measure) =
      ∫ point,
        metric.volume point / 2 *
          generalMetricTensorPairingAt period hPeriod metric.metric
            (regularGeneralMetricMaxwellStressTensor period hPeriod metric
              potential) variation point
        ∂measure := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point => by
    apply congrArg (metric.volume point / 2 * ·)
    exact regularGeneralMetricMaxwellStress_variation_invariant period hPeriod
      metric potential variation point

/-- Gate marker for the invariant and integrated Maxwell stress variation. -/
theorem regular_general_metric_invariant_maxwell_stress_variation_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (∫ point,
      metric.volume point / 2 *
        variationalMaxwellStressPairing
          (regularFrameMetricInverseMatrixMap period hPeriod metric point)
          (fun component first second =>
            regularFrameGaugeCurvatureCoefficient period hPeriod metric
              potential component first second point)
          (fun first second => variation.tensor point
            (metric.frame first point) (metric.frame second point))
      ∂measure) =
      ∫ point,
        metric.volume point / 2 *
          generalMetricTensorPairingAt period hPeriod metric.metric
            (regularGeneralMetricMaxwellStressTensor period hPeriod metric
              potential) variation point
        ∂measure :=
  integral_regularGeneralMetricMaxwellStress_variation_invariant period hPeriod
    metric potential variation measure

end
end P0EFTJanusProgramPRegularGeneralMetricInvariantMaxwellStressVariation4D
end JanusFormal
