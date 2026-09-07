import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricInducedSmoothGaugeVelocity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalTestSeparation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricPositiveDualizer4D

/-! # Metric tensor representing the induced Maxwell gauge variation

Writing `J` for the canonical Maxwell Euler coefficients, the positive
transpose-root velocity gives `J · (Hᵀ A / 2)`, where `H = g⁻¹ h`.
The sixteen smooth coefficients below reconstruct its metric tensor. No
Maxwell equation or vanishing current is assumed, and no additional volume
factor is inserted into the already canonical Euler density.
-/

namespace JanusFormal
namespace P0EFTJanusMetricInducedMaxwellResidual4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusMetricInducedSmoothGaugeVelocity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- Coefficients acting directly on covariant metric components. -/
def metricInducedMaxwellResidualCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : Fin 4) : SmoothScalarField period hPeriod :=
  (1 / 2 : Real) • ∑ component : Fin 2, ∑ row : Fin 4,
    smoothScalarFieldMul period hPeriod
      (regularFrameCanonicalMaxwellVariationalResidualCoefficient period hPeriod
        metric potential second component)
      (smoothScalarFieldMul period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric row first)
        (regularFrameGaugeCoefficient period hPeriod
          (gaugePotentialFrameCoefficients period hPeriod metric potential) (row, component)))

theorem metricInducedMaxwellResidualCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : Fin 4) (point : EffectiveQuotient period hPeriod) :
    metricInducedMaxwellResidualCoefficient period hPeriod metric potential first second point =
      (1 / 2 : Real) * ∑ component : Fin 2, ∑ row : Fin 4,
        regularFrameCanonicalMaxwellVariationalResidualCoefficient period hPeriod
            metric potential second component point *
          (regularFrameMetricInverseMatrixMap period hPeriod metric point row first *
            potential.toFun component point (metric.frame row point)) := by
  simp only [metricInducedMaxwellResidualCoefficient, smoothQuotientField_smul_apply,
    smul_eq_mul, smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply]
  rfl

/-- The metric-dual frame products represent covectors on the components of `h`. -/
def metricInducedMaxwellResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric
  ∑ first : Fin 4, ∑ second : Fin 4,
    smoothBulkScalarSMulTensor period hPeriod
      (metricInducedMaxwellResidualCoefficient period hPeriod metric potential first second)
      (smoothBulkCovectorSymmetricProduct period hPeriod
        (generalMetricFrameCovector period hPeriod frame metric.metric.tensor first)
        (generalMetricFrameCovector period hPeriod frame metric.metric.tensor second))

theorem metricInducedMaxwellResidual_pairing_eq_coefficientSum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric.metric
        (metricInducedMaxwellResidual period hPeriod metric potential) tensor point =
      ∑ first : Fin 4, ∑ second : Fin 4,
        metricInducedMaxwellResidualCoefficient period hPeriod metric potential first second point *
          tensor.tensor point (metric.frame first point) (metric.frame second point) := by
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric
  rw [generalMetricTensorPairingAt_symmetric]
  let pairing : SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] Real :=
    { toFun := fun value => generalMetricTensorPairingAt period hPeriod metric.metric tensor value point
      map_add' := fun first second => generalMetricTensorPairingAt_add_right period hPeriod
        metric.metric tensor first second point
      map_smul' := fun scalar value => generalMetricTensorPairingAt_smul_right period hPeriod
        metric.metric scalar tensor value point }
  change pairing (metricInducedMaxwellResidual period hPeriod metric potential) = _
  unfold metricInducedMaxwellResidual
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro second _
  let coefficient := metricInducedMaxwellResidualCoefficient period hPeriod metric potential first second
  let rankOne := smoothBulkCovectorSymmetricProduct period hPeriod
    (generalMetricFrameCovector period hPeriod frame metric.metric.tensor first)
    (generalMetricFrameCovector period hPeriod frame metric.metric.tensor second)
  have hCongr : pairing (smoothBulkScalarSMulTensor period hPeriod coefficient rankOne) =
      pairing ((coefficient point) • rankOne) := by
    apply generalMetricTensorPairingAt_congr_right_at
    apply ContinuousLinearMap.ext
    intro left
    apply ContinuousLinearMap.ext
    intro right
    rfl
  rw [hCongr, map_smul]
  change coefficient point * pairing rankOne = coefficient point * _
  apply congrArg (coefficient point * ·)
  exact generalMetricSymmetricFrameProduct_pairing period hPeriod frame metric.metric
    tensor point first second

private theorem smoothRelativeEntry_eq_inverseVariation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (row column : Fin 4) :
    smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor row column point =
      ∑ first : Fin 4, regularFrameMetricInverseMatrixMap period hPeriod metric point row first *
        tensor.tensor point (metric.frame first point) (metric.frame column point) := by
  have hMatrix := regularGeneralMetricC2RelativeMatrixAt_smooth period hPeriod metric tensor point
  have hEntry := congrFun (congrFun hMatrix row) column
  change smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric tensor row column point =
    (regularFrameMetricInverseMatrixMap period hPeriod metric point *
      regularFrameCovariantVariationMatrixAt period hPeriod metric tensor point) row column at hEntry
  exact hEntry

private theorem transposeVelocity_contraction
    (current potential : Fin 4 → Fin 2 → Real)
    (inverse variation : Fin 4 → Fin 4 → Real) :
    (∑ upper : Fin 4, ∑ component : Fin 2,
      current upper component * ((1 / 2 : Real) * ∑ row : Fin 4,
        (∑ first : Fin 4, inverse row first * variation first upper) * potential row component)) =
      ∑ first : Fin 4, ∑ upper : Fin 4,
        ((1 / 2 : Real) * ∑ component : Fin 2, ∑ row : Fin 4,
          current upper component * (inverse row first * potential row component)) *
        variation first upper := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ upper : Fin 4, ∑ component : Fin 2, ∑ row : Fin 4, ∑ first : Fin 4,
      current upper component * ((1 / 2 : Real) *
        ((inverse row first * variation first upper) * potential row component))) =
        ∑ upper : Fin 4, ∑ component : Fin 2, ∑ first : Fin 4, ∑ row : Fin 4,
          current upper component * ((1 / 2 : Real) *
            ((inverse row first * variation first upper) * potential row component)) := by
      apply Finset.sum_congr rfl
      intro upper _
      apply Finset.sum_congr rfl
      intro component _
      exact Finset.sum_comm
    _ = ∑ upper : Fin 4, ∑ first : Fin 4, ∑ component : Fin 2, ∑ row : Fin 4,
          current upper component * ((1 / 2 : Real) *
            ((inverse row first * variation first upper) * potential row component)) := by
      apply Finset.sum_congr rfl
      intro upper _
      exact Finset.sum_comm
    _ = ∑ first : Fin 4, ∑ upper : Fin 4, ∑ component : Fin 2, ∑ row : Fin 4,
          current upper component * ((1 / 2 : Real) *
            ((inverse row first * variation first upper) * potential row component)) := Finset.sum_comm
    _ = _ := by
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro upper _
      apply Finset.sum_congr rfl
      intro component _
      apply Finset.sum_congr rfl
      intro row _
      ring

/-- The concrete smooth tensor represents the actual positive induced gauge density. -/
theorem metricInducedMaxwellResidual_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric.metric
        (metricInducedMaxwellResidual period hPeriod metric potential) tensor point =
      inner Real (regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric potential point)
        (gaugePotentialFrameCoefficients period hPeriod metric
          (metricInducedGaugePotential period hPeriod metric tensor potential) point) := by
  rw [metricInducedMaxwellResidual_pairing_eq_coefficientSum, PiLp.inner_apply,
    Fintype.sum_prod_type]
  simp only [Real.inner_apply, regularFrameCanonicalMaxwellVariationalResidual_apply,
    gaugePotentialFrameCoefficients_apply, metricInducedGaugePotential_frame,
    metricInducedGaugeCoefficientEntry, smoothQuotientField_smul_apply, smul_eq_mul,
    smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply,
    metricInducedMaxwellResidualCoefficient_apply]
  simp_rw [smoothRelativeEntry_eq_inverseVariation]
  change (∑ first : Fin 4, ∑ upper : Fin 4,
      ((1 / 2 : Real) * ∑ component : Fin 2, ∑ row : Fin 4,
        regularFrameCanonicalMaxwellVariationalResidualCoefficient period hPeriod metric potential
            upper component point *
          (regularFrameMetricInverseMatrixMap period hPeriod metric point row first *
            potential.toFun component point (metric.frame row point))) *
      tensor.tensor point (metric.frame first point) (metric.frame upper point)) = _
  exact (transposeVelocity_contraction
    (fun upper component => regularFrameCanonicalMaxwellVariationalResidualCoefficient
      period hPeriod metric potential upper component point)
    (fun row component => potential.toFun component point (metric.frame row point))
    (regularFrameMetricInverseMatrixMap period hPeriod metric point)
    (fun first upper => tensor.tensor point (metric.frame first point) (metric.frame upper point))).symm

/-- Canonical gauge residual on the induced velocity equals the metric residual integral. -/
theorem canonicalMaxwellResidualPairing_metricInducedGaugePotential_eq_metricIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod metric
        (regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric potential)
        (metricInducedGaugePotential period hPeriod metric tensor potential) =
      ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
        (metricInducedMaxwellResidual period hPeriod metric potential) tensor point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold canonicalRegularFrameIntrinsicGaugeResidualPairing
    regularFrameIntrinsicGaugeResidualPairing smoothGaugeResidualPairing
  apply congrArg (fun density : EffectiveQuotient period hPeriod → Real =>
    ∫ point, density point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  funext point
  exact (metricInducedMaxwellResidual_pairing period hPeriod metric potential tensor point).symm

end
end P0EFTJanusMetricInducedMaxwellResidual4D
end JanusFormal
