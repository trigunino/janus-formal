import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2MetricTensorTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2KoszulConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricDeDonderLinear4D

/-! # Joint completed de Donder operator without a global tangent basis

The metric, inverse metric, connection, tensor and trace gradient are all
read from the same two C² inputs. The resulting coefficients agree with the
actual global de Donder one-form at every smooth admissible input.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2DeDonder4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorTrace4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Model" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "Input" => Model × Model
local notation "Domain" => Set.prod (generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) Set.univ

def finiteFrameTensorC2Coefficient (row column : Fin frame.count) : Model →L[Real] C2Scalar period hPeriod :=
  (ContinuousLinearMap.proj column).comp ((ContinuousLinearMap.proj row).comp
    (finiteFrameRelativeC2ToTensorCoefficients period hPeriod frame baseMetric))

def finiteFrameTensorC0Coefficient (row column : Fin frame.count) : Model →L[Real] C0Scalar period hPeriod :=
  (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
    (finiteFrameTensorC2Coefficient period hPeriod frame baseMetric row column)

def finiteFrameTensorC0FirstDerivative (derivative row column : Fin frame.count) :
    Model →L[Real] C0Scalar period hPeriod :=
  (finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame derivative).comp
    (finiteFrameTensorC2Coefficient period hPeriod frame baseMetric row column)

theorem finiteFrameTensorC0Coefficient_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    finiteFrameTensorC0Coefficient period hPeriod frame baseMetric row column
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor) point =
    generalMetricFrameCoefficient period hPeriod frame tensor row column point := by
  change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (finiteFrameRelativeC2ToTensorCoefficients period hPeriod frame baseMetric
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor) row column) point = _
  rw [finiteFrameRelativeC2ToTensorCoefficients_smooth]
  exact congrArg (fun field : C0Scalar period hPeriod => field point)
    (canonicalPhysicalScalarC2JetCoreToContinuous_smooth period hPeriod _)

theorem finiteFrameTensorC0FirstDerivative_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative row column : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    finiteFrameTensorC0FirstDerivative period hPeriod frame baseMetric derivative row column
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor) point =
    frameDerivative period hPeriod Real frame
      (generalMetricFrameCoefficient period hPeriod frame tensor row column) point derivative := by
  change finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame derivative
    (finiteFrameRelativeC2ToTensorCoefficients period hPeriod frame baseMetric
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor) row column) point = _
  rw [finiteFrameRelativeC2ToTensorCoefficients_smooth]
  exact finiteFrameScalarC2FirstDerivative_smooth period hPeriod baseMetric frame derivative _ point

/-- The full de Donder coefficient, with both connection terms and the trace gradient. -/
def finiteFrameC2DeDonderCoefficient (last : Fin frame.count) (input : Input) : C0Scalar period hPeriod :=
  (∑ derivative : Fin frame.count, ∑ first : Fin frame.count,
    finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric derivative first input.1 *
      (finiteFrameTensorC0FirstDerivative period hPeriod frame baseMetric derivative first last input.2 -
        (∑ index : Fin frame.count,
          finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric index derivative first input.1 *
            finiteFrameTensorC0Coefficient period hPeriod frame baseMetric index last input.2) -
        ∑ index : Fin frame.count,
          finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric index derivative last input.1 *
            finiteFrameTensorC0Coefficient period hPeriod frame baseMetric first index input.2)) -
    (1 / 2 : Real) • finiteFrameMetricTensorTraceGradientC0 period hPeriod frame baseMetric last input.1 input.2

theorem finiteFrameC2DeDonderCoefficient_contDiffOn (last : Fin frame.count) :
    ContDiffOn Real ∞ (finiteFrameC2DeDonderCoefficient period hPeriod frame baseMetric last) Domain := by
  have hInverse (i j : Fin frame.count) : ContDiffOn Real ∞
      (fun input : Input => finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric i j input.1) Domain :=
    (finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame baseMetric i j).comp
      contDiff_fst.contDiffOn (fun _ h => h.1)
  have hGamma (k i j : Fin frame.count) : ContDiffOn Real ∞
      (fun input : Input => finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric k i j input.1) Domain :=
    (finiteFrameChristoffelC0Coefficient_contDiffOn period hPeriod frame baseMetric k i j).comp
      contDiff_fst.contDiffOn (fun _ h => h.1)
  have hTensor (i j : Fin frame.count) : ContDiffOn Real ∞
      (fun input : Input => finiteFrameTensorC0Coefficient period hPeriod frame baseMetric i j input.2) Domain :=
    ((finiteFrameTensorC0Coefficient period hPeriod frame baseMetric i j).contDiff.comp contDiff_snd).contDiffOn
  have hFirst (k i j : Fin frame.count) : ContDiffOn Real ∞
      (fun input : Input => finiteFrameTensorC0FirstDerivative period hPeriod frame baseMetric k i j input.2) Domain :=
    ((finiteFrameTensorC0FirstDerivative period hPeriod frame baseMetric k i j).contDiff.comp contDiff_snd).contDiffOn
  exact (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hInverse i j).mul
    (((hFirst i j last).sub (ContDiffOn.sum fun k _ => (hGamma k i j).mul (hTensor k last))).sub
      (ContDiffOn.sum fun k _ => (hGamma k i last).mul (hTensor j k)))).sub
    ((finiteFrameMetricTensorTraceGradientC0_contDiffOn period hPeriod frame baseMetric last).const_smul (1 / 2 : Real))

theorem finiteFrameC2DeDonderCoefficient_smooth_local
    (variation tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (last : Fin frame.count) :
    finiteFrameC2DeDonderCoefficient period hPeriod frame baseMetric last
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation,
       smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor)
        (patch.coordinateMap coordinate) =
    globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor
      (patch.coordinateMap coordinate) (frame.vectorAt (patch.coordinateMap coordinate) last) := by
  have hReadout (field : SmoothScalarField period hPeriod) :
      smoothToCanonicalPhysicalContinuousScalar period hPeriod field (patch.coordinateMap coordinate) =
        field (patch.coordinateMap coordinate) := rfl
  unfold finiteFrameC2DeDonderCoefficient
  simp only [ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.smul_apply, smul_eq_mul,
    finiteFrameInverseMetricC0Coefficient_smooth period hPeriod frame baseMetric variation metric hMetric hVariation,
    finiteFrameTensorC0FirstDerivative_smooth, finiteFrameTensorC0Coefficient_smooth,
    finiteFrameChristoffelC0Coefficient_eq_local period hPeriod frame baseMetric variation metric hMetric hVariation,
    finiteFrameMetricTensorTraceGradientC0_smooth period hPeriod frame baseMetric variation tensor metric hMetric hVariation,
    hReadout]
  rw [← globalGeneralMetricSymmetricTensorDivergence_eq_finiteFrameCovariantTrace
    period hPeriod frame baseMetric metric tensor patch coordinate last]
  change _ - (1 / 2 : Real) * _ = _ + (-1 / 2 : Real) * _
  ring_nf
  rfl

/-- Every quotient point is covered; agreement is with the genuine global one-form. -/
theorem finiteFrameC2DeDonderCoefficient_smooth
    (variation tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (point : EffectiveQuotient period hPeriod) (last : Fin frame.count) :
    finiteFrameC2DeDonderCoefficient period hPeriod frame baseMetric last
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation,
       smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor) point =
    globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor point (frame.vectorAt point last) := by
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with ⟨patch, coordinate, hPoint⟩
  rw [← hPoint]
  exact finiteFrameC2DeDonderCoefficient_smooth_local period hPeriod frame baseMetric variation tensor
    metric hMetric hVariation patch coordinate last

end
end P0EFTJanusFiniteFrameC2DeDonder4D
end JanusFormal
