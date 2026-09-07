import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameMetricTensorTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameScalarC2Derivatives4D

/-! # Joint metric–tensor C² trace in a finite generating frame

The actual metric inverse and tensor readout give a C² scalar trace.
Its bounded directional derivative gives the intrinsic trace differential
on every admissible smooth metric lift, without a global basis.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2MetricTensorTrace4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Bounded diagonal extraction, for any finite coefficient matrix. -/
def finiteFrameC2MatrixTraceCLM (dimension : Nat) :
    C2FiniteMatrix period hPeriod dimension →L[Real] C2Scalar period hPeriod :=
  ∑ index : Fin dimension,
    (ContinuousLinearMap.proj index :
      (Fin dimension → C2Scalar period hPeriod) →L[Real] C2Scalar period hPeriod).comp
      (ContinuousLinearMap.proj index : C2FiniteMatrix period hPeriod dimension →L[Real]
        (Fin dimension → C2Scalar period hPeriod))

@[simp] theorem finiteFrameC2MatrixTraceCLM_apply (dimension : Nat)
    (matrix : C2FiniteMatrix period hPeriod dimension) :
    finiteFrameC2MatrixTraceCLM period hPeriod dimension matrix =
      ∑ index : Fin dimension, matrix index index := by
  simp [finiteFrameC2MatrixTraceCLM]

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Model" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric

/-- The true jointly varying trace, formed inside the completed C² algebra. -/
def finiteFrameMetricTensorTraceC2 (metricVariation tensorVariation : Model) :
    C2Scalar period hPeriod :=
  finiteFrameC2MatrixTraceCLM period hPeriod frame.count
    (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric metricVariation)
      (finiteFrameRelativeC2ToTensorCoefficients period hPeriod frame baseMetric tensorVariation))

theorem finiteFrameMetricTensorTraceC2_contDiffOn :
    ContDiffOn Real ∞
      (fun input : Model × Model =>
        finiteFrameMetricTensorTraceC2 period hPeriod frame baseMetric input.1 input.2)
      ((generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) ×ˢ Set.univ) := by
  have hInverse := (finiteFrameInverseMetricC2Coefficients_contDiffOn
    period hPeriod frame baseMetric).comp
      (contDiff_fst.contDiffOn : ContDiffOn Real ∞ (fun input : Model × Model => input.1)
        ((generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) ×ˢ Set.univ))
      (fun _ h => h.1)
  have hTensor := (finiteFrameRelativeC2ToTensorCoefficients
    period hPeriod frame baseMetric).contDiff.comp
      (contDiff_snd : ContDiff Real ∞ (fun input : Model × Model => input.2))
  have hProduct := ((c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod)
    frame.count).contDiff.comp_contDiffOn hInverse).clm_apply hTensor.contDiffOn
  have h := (finiteFrameC2MatrixTraceCLM period hPeriod frame.count).contDiff.comp_contDiffOn hProduct
  simp only [Function.comp_def] at h
  exact h

/-- Whole C² agreement, before taking any directional derivative. -/
theorem finiteFrameMetricTensorTraceC2_smooth
    (variation tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) :
    finiteFrameMetricTensorTraceC2 period hPeriod frame baseMetric
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation)
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor) =
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (generalMetricTensorTrace period hPeriod metric tensor) := by
  unfold finiteFrameMetricTensorTraceC2
  rw [finiteFrameInverseMetricC2Coefficients_smooth period hPeriod frame baseMetric
    variation metric hMetric hVariation, finiteFrameRelativeC2ToTensorCoefficients_smooth]
  change finiteFrameC2MatrixTraceCLM period hPeriod frame.count
    (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
      (smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric metric))
      (smoothFiniteMatrixToC2 period hPeriod frame.count
        (generalMetricFrameCoefficient period hPeriod frame tensor))) = _
  rw [c2FiniteMatrixProduct_smooth, finiteFrameC2MatrixTraceCLM_apply]
  change (∑ index : Fin frame.count, smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
    (smoothFiniteMatrixProduct period hPeriod frame.count
      (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric metric)
      (generalMetricFrameCoefficient period hPeriod frame tensor) index index)) = _
  rw [← map_sum]
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [generalMetricTensorTrace_eq_finiteFrameContraction period hPeriod frame baseMetric]
  simp only [smoothFiniteMatrixProduct, smoothFiniteFrameInverseMetricMatrix,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, generalMetricFrameCoefficient_apply]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  exact congrArg (fun value : Real =>
    finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric first second point * value)
      (tensor.symmetric point (frame.vectorAt point second) (frame.vectorAt point first))

/-- Covector coefficients of the trace differential, in the fixed generating frame. -/
def finiteFrameMetricTensorTraceGradientC0 (index : Fin frame.count)
    (metricVariation tensorVariation : Model) : C(EffectiveQuotient period hPeriod, Real) :=
  finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame index
    (finiteFrameMetricTensorTraceC2 period hPeriod frame baseMetric metricVariation tensorVariation)

theorem finiteFrameMetricTensorTraceGradientC0_contDiffOn (index : Fin frame.count) :
    ContDiffOn Real ∞
      (fun input : Model × Model =>
        finiteFrameMetricTensorTraceGradientC0 period hPeriod frame baseMetric index input.1 input.2)
      ((generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) ×ˢ Set.univ) := by
  have h := (finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame index).contDiff.comp_contDiffOn
    (finiteFrameMetricTensorTraceC2_contDiffOn period hPeriod frame baseMetric)
  simp only [Function.comp_def] at h
  exact h

theorem finiteFrameMetricTensorTraceGradientC0_smooth
    (variation tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (index : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    finiteFrameMetricTensorTraceGradientC0 period hPeriod frame baseMetric index
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation)
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor) point =
    generalMetricTensorTraceDifferential period hPeriod metric tensor point (frame.vectorAt point index) := by
  unfold finiteFrameMetricTensorTraceGradientC0
  rw [finiteFrameMetricTensorTraceC2_smooth period hPeriod frame baseMetric
    variation tensor metric hMetric hVariation, finiteFrameScalarC2FirstDerivative_smooth]
  rfl

end
end P0EFTJanusFiniteFrameC2MetricTensorTrace4D
end JanusFormal
