import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2DeDonder4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2FirstJetLeibniz4D

/-! # Finite-frame de Donder factors through the tensor's first jet

The tensor input contains only continuous values and ordered first derivatives.
All metric coefficients, including the inverse derivative and connection, are
computed from the same admissible relative C² metric variation.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2DeDonderFirstJet4D

set_option autoImplicit false

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
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameC2FirstJetLeibniz4D

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

/-- Slots are `Hᵢⱼ` and `Eₐ Hᵢⱼ`, with the derivative index first. -/
abbrev FiniteFrameTensorC0FirstJet (frame : SmoothD8Frame period hPeriod) :=
  (Fin frame.count → Fin frame.count → C0Scalar period hPeriod) ×
    (Fin frame.count → Fin frame.count → Fin frame.count → C0Scalar period hPeriod)

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Model" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "FirstJet" => FiniteFrameTensorC0FirstJet period hPeriod frame
local notation "Input" => Model × FirstJet
local notation "Domain" => Set.prod (generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) Set.univ

/-- Bounded extraction of precisely the tensor slots needed by de Donder. -/
def finiteFrameTensorC0FirstJetCLM : Model →L[Real] FirstJet :=
  (ContinuousLinearMap.pi (fun row => ContinuousLinearMap.pi (fun column =>
    finiteFrameTensorC0Coefficient period hPeriod frame baseMetric row column))).prod
    (ContinuousLinearMap.pi (fun derivative => ContinuousLinearMap.pi (fun row =>
      ContinuousLinearMap.pi (fun column =>
        finiteFrameTensorC0FirstDerivative period hPeriod frame baseMetric derivative row column))))

@[simp] theorem finiteFrameTensorC0FirstJetCLM_apply (tensorVariation : Model) :
    finiteFrameTensorC0FirstJetCLM period hPeriod frame baseMetric tensorVariation =
      ((fun row column => finiteFrameTensorC0Coefficient period hPeriod frame baseMetric row column tensorVariation),
        (fun derivative row column =>
          finiteFrameTensorC0FirstDerivative period hPeriod frame baseMetric derivative row column tensorVariation)) := rfl

/-- The actual smooth tensor's value and first-derivative packet. -/
def smoothFiniteFrameTensorC0FirstJet (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : FirstJet :=
  ((fun row column => smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (generalMetricFrameCoefficient period hPeriod frame tensor row column)),
    (fun derivative row column => smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (frameDerivativeComponentField period hPeriod frame
        (generalMetricFrameCoefficient period hPeriod frame tensor row column) derivative)))

theorem finiteFrameTensorC0FirstJetCLM_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    finiteFrameTensorC0FirstJetCLM period hPeriod frame baseMetric
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor) =
    smoothFiniteFrameTensorC0FirstJet period hPeriod frame tensor := by
  apply Prod.ext
  · funext row column
    apply ContinuousMap.ext
    intro point
    exact finiteFrameTensorC0Coefficient_smooth period hPeriod frame baseMetric tensor row column point
  · funext derivative row column
    apply ContinuousMap.ext
    intro point
    exact finiteFrameTensorC0FirstDerivative_smooth period hPeriod frame baseMetric tensor derivative row column point

/-- The inverse metric's first spatial derivative, from its genuine C² lift. -/
def finiteFrameInverseMetricC0FirstDerivative (derivative row column : Fin frame.count)
    (variation : Model) : C0Scalar period hPeriod :=
  finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame derivative
    (finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric variation row column)

theorem finiteFrameInverseMetricC0FirstDerivative_contDiffOn (derivative row column : Fin frame.count) :
    ContDiffOn Real ∞
      (finiteFrameInverseMetricC0FirstDerivative period hPeriod frame baseMetric derivative row column)
      (generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) := by
  have h := (finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame derivative).contDiff.comp_contDiffOn
    ((contDiff_apply Real (C2Scalar period hPeriod) column).comp_contDiffOn
      ((contDiff_apply Real (Fin frame.count → C2Scalar period hPeriod) row).comp_contDiffOn
        (finiteFrameInverseMetricC2Coefficients_contDiffOn period hPeriod frame baseMetric)))
  exact h

/-- Both connection corrections and the complete differentiated trace. -/
def finiteFrameC2DeDonderFirstJetCoefficient (last : Fin frame.count) (input : Input) : C0Scalar period hPeriod :=
  (∑ derivative : Fin frame.count, ∑ first : Fin frame.count,
    finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric derivative first input.1 *
      (input.2.2 derivative first last -
        (∑ index : Fin frame.count,
          finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric index derivative first input.1 *
            input.2.1 index last) -
        ∑ index : Fin frame.count,
          finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric index derivative last input.1 *
            input.2.1 first index)) -
    (1 / 2 : Real) • (∑ row : Fin frame.count, ∑ column : Fin frame.count,
      (finiteFrameInverseMetricC0FirstDerivative period hPeriod frame baseMetric last row column input.1 *
          input.2.1 column row +
        finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric row column input.1 *
          input.2.2 last column row))

theorem finiteFrameC2DeDonderFirstJetCoefficient_contDiffOn (last : Fin frame.count) :
    ContDiffOn Real ∞ (finiteFrameC2DeDonderFirstJetCoefficient period hPeriod frame baseMetric last) Domain := by
  have hInverse (i j : Fin frame.count) : ContDiffOn Real ∞
      (fun input : Input => finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric i j input.1) Domain :=
    (finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame baseMetric i j).comp
      contDiff_fst.contDiffOn (fun _ h => h.1)
  have hInverseDerivative (i j : Fin frame.count) : ContDiffOn Real ∞
      (fun input : Input => finiteFrameInverseMetricC0FirstDerivative period hPeriod frame baseMetric last i j input.1) Domain :=
    (finiteFrameInverseMetricC0FirstDerivative_contDiffOn period hPeriod frame baseMetric last i j).comp
      contDiff_fst.contDiffOn (fun _ h => h.1)
  have hGamma (k i j : Fin frame.count) : ContDiffOn Real ∞
      (fun input : Input => finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric k i j input.1) Domain :=
    (finiteFrameChristoffelC0Coefficient_contDiffOn period hPeriod frame baseMetric k i j).comp
      contDiff_fst.contDiffOn (fun _ h => h.1)
  have hValues : ContDiff Real ∞ (fun input : Input => input.2.1) := contDiff_fst.comp contDiff_snd
  have hDerivatives : ContDiff Real ∞ (fun input : Input => input.2.2) := contDiff_snd.comp contDiff_snd
  have hValue (i j : Fin frame.count) := contDiff_pi.mp (contDiff_pi.mp hValues i) j
  have hDerivative (k i j : Fin frame.count) :=
    contDiff_pi.mp (contDiff_pi.mp (contDiff_pi.mp hDerivatives k) i) j
  exact (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hInverse i j).mul
    (((hDerivative i j last).contDiffOn.sub
      (ContDiffOn.sum fun k _ => (hGamma k i j).mul (hValue k last).contDiffOn)).sub
        (ContDiffOn.sum fun k _ => (hGamma k i last).mul (hValue j k).contDiffOn))).sub
    ((ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      ((hInverseDerivative i j).mul (hValue j i).contDiffOn).add
        ((hInverse i j).mul (hDerivative last j i).contDiffOn)).const_smul (1 / 2 : Real))

/-- Exact factorization on every completed tensor input, not only smooth lifts. -/
theorem finiteFrameC2DeDonderFirstJetCoefficient_factorization
    (last : Fin frame.count) (metricVariation tensorVariation : Model) :
    finiteFrameC2DeDonderFirstJetCoefficient period hPeriod frame baseMetric last
      (metricVariation, finiteFrameTensorC0FirstJetCLM period hPeriod frame baseMetric tensorVariation) =
    finiteFrameC2DeDonderCoefficient period hPeriod frame baseMetric last (metricVariation, tensorVariation) := by
  unfold finiteFrameC2DeDonderFirstJetCoefficient finiteFrameC2DeDonderCoefficient
  rw [finiteFrameMetricTensorTraceGradientC0_eq_sum_firstJets]
  rfl

/-- The smooth first jet gives the genuine global de Donder covector. -/
theorem finiteFrameC2DeDonderFirstJetCoefficient_smooth
    (variation tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (point : EffectiveQuotient period hPeriod) (last : Fin frame.count) :
    finiteFrameC2DeDonderFirstJetCoefficient period hPeriod frame baseMetric last
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation,
        smoothFiniteFrameTensorC0FirstJet period hPeriod frame tensor) point =
    globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor point (frame.vectorAt point last) := by
  rw [← finiteFrameTensorC0FirstJetCLM_smooth period hPeriod frame baseMetric tensor,
    finiteFrameC2DeDonderFirstJetCoefficient_factorization]
  exact finiteFrameC2DeDonderCoefficient_smooth period hPeriod frame baseMetric variation tensor metric
    hMetric hVariation point last

end
end P0EFTJanusFiniteFrameC2DeDonderFirstJet4D
end JanusFormal
