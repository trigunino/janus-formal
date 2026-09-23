import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2DeDonder4D

/-! Exact smooth finite-frame de Donder operator, including connection and trace terms. -/
namespace JanusFormal.P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D


open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorTrace4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D

variable (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)

abbrev TensorCoefficients := Fin frame.count → Fin frame.count → SmoothScalarField period hPeriod

def deDonderTrace (field : TensorCoefficients period hPeriod frame) : SmoothScalarField period hPeriod :=
  ∑ row, ∑ column, canonicalScalarMul period hPeriod
    (finiteFrameInverseMetricCoefficient period hPeriod frame metric metric row column) (field column row)

def deDonderCovariantRow (field : TensorCoefficients period hPeriod frame)
    (derivative first last : Fin frame.count) : SmoothScalarField period hPeriod :=
  canonicalFrameDerivativeSmooth period hPeriod frame derivative (field first last) -
    (∑ index, canonicalScalarMul period hPeriod
      (finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric index derivative first) (field index last)) -
    ∑ index, canonicalScalarMul period hPeriod
      (finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric index derivative last) (field first index)

def deDonderRow (field : TensorCoefficients period hPeriod frame) (last : Fin frame.count) : SmoothScalarField period hPeriod :=
  (∑ derivative, ∑ first, canonicalScalarMul period hPeriod
    (finiteFrameInverseMetricCoefficient period hPeriod frame metric metric derivative first)
    (deDonderCovariantRow period hPeriod frame metric field derivative first last)) -
    (1 / 2 : Real) • canonicalFrameDerivativeSmooth period hPeriod frame last
      (deDonderTrace period hPeriod frame metric field)

theorem deDonderTrace_actual (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    deDonderTrace period hPeriod frame metric (generalMetricFrameCoefficient period hPeriod frame tensor) =
      generalMetricTensorTrace period hPeriod metric tensor := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [generalMetricTensorTrace_eq_finiteFrameContraction period hPeriod frame metric]
  simp only [deDonderTrace, canonicalScalar_sum_apply]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  change _ * tensor.tensor point (frame.vectorAt point column) (frame.vectorAt point row) = _
  rw [tensor.symmetric point (frame.vectorAt point column) (frame.vectorAt point row)]

theorem deDonderRow_actual (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (last : Fin frame.count) :
    deDonderRow period hPeriod frame metric (generalMetricFrameCoefficient period hPeriod frame tensor) last point =
      globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor point (frame.vectorAt point last) := by
  have hMetric : metric.tensor = metric.tensor + (0 : SmoothSymmetricCovariantTwoTensor period hPeriod) := (add_zero _).symm
  have hZero : smoothToGeneralMetricRelativeC2Core period hPeriod frame metric 0 ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame metric := by
    rw [map_zero]
    exact zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame metric
  have h := finiteFrameC2DeDonderCoefficient_smooth period hPeriod frame metric 0 tensor metric hMetric hZero point last
  unfold finiteFrameC2DeDonderCoefficient at h
  simp only [ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.smul_apply, smul_eq_mul,
    finiteFrameInverseMetricC0Coefficient_smooth period hPeriod frame metric 0 metric hMetric hZero,
    finiteFrameTensorC0FirstDerivative_smooth, finiteFrameTensorC0Coefficient_smooth,
    finiteFrameChristoffelC0Coefficient_smooth period hPeriod frame metric 0 metric hMetric hZero,
    finiteFrameMetricTensorTraceGradientC0_smooth period hPeriod frame metric 0 tensor metric hMetric hZero] at h
  rw [deDonderRow, deDonderTrace_actual]
  have evalSub (a b : SmoothScalarField period hPeriod) : (a - b) point = a point - b point := rfl
  have evalSmul (a : Real) (b : SmoothScalarField period hPeriod) : (a • b) point = a * b point := rfl
  have evalMul (a b : SmoothScalarField period hPeriod) :
      canonicalScalarMul period hPeriod a b point = a point * b point := rfl
  simp only [evalSub, evalSmul, canonicalScalar_sum_apply, evalMul, deDonderCovariantRow]
  exact h

end
end JanusFormal.P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
