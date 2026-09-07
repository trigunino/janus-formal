import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2DeDonderFirstJet4D

/-! # Scalar curvature from the redundant finite-frame C² metric core

The spatial derivative of the connection is expanded before completion, so
only the two ordered metric jets already carried by the C² core are used.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2ScalarCurvature4D

set_option autoImplicit false
set_option maxHeartbeats 800000
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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2DeDonderFirstJet4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D

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
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Model" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "Domain" => generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric

def finiteFrameMetricC0SecondDerivative (outer inner row column : Fin frame.count)
    (variation : Model) : C0Scalar period hPeriod :=
  finiteFrameScalarC2SecondDerivative period hPeriod baseMetric frame outer inner
    (finiteFrameMetricC2Coefficients period hPeriod frame baseMetric variation row column)

theorem finiteFrameMetricC0SecondDerivative_contDiff (outer inner row column : Fin frame.count) :
    ContDiff Real ∞
      (finiteFrameMetricC0SecondDerivative period hPeriod frame baseMetric outer inner row column) :=
  (finiteFrameScalarC2SecondDerivative period hPeriod baseMetric frame outer inner).contDiff.comp
    ((contDiff_apply Real (C2Scalar period hPeriod) column).comp
      ((contDiff_apply Real (Fin frame.count → C2Scalar period hPeriod) row).comp
        (finiteFrameMetricC2Coefficients_contDiff period hPeriod frame baseMetric)))

def finiteFrameStructureC0Derivative
    (derivative first second upper : Fin frame.count) : C0Scalar period hPeriod :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod
    (frameDerivativeComponentField period hPeriod frame
      (finiteFrameStructureCoefficient period hPeriod frame baseMetric first second upper) derivative)

def finiteFrameStructureMetricC0DerivativeTerm
    (derivative bracketFirst bracketSecond contracted metricRow metricColumn : Fin frame.count)
    (variation : Model) : C0Scalar period hPeriod :=
  finiteFrameStructureC0Derivative period hPeriod frame baseMetric derivative
      bracketFirst bracketSecond contracted *
    finiteFrameMetricC0Coefficient period hPeriod frame baseMetric metricRow metricColumn variation +
  finiteFrameStructureC0Coefficient period hPeriod frame baseMetric bracketFirst bracketSecond contracted *
    finiteFrameMetricC0FirstDerivative period hPeriod frame baseMetric derivative
      metricRow metricColumn variation

theorem finiteFrameStructureMetricC0DerivativeTerm_contDiff
    (derivative bracketFirst bracketSecond contracted metricRow metricColumn : Fin frame.count) :
    ContDiff Real ∞ (finiteFrameStructureMetricC0DerivativeTerm period hPeriod frame baseMetric
      derivative bracketFirst bracketSecond contracted metricRow metricColumn) :=
  (contDiff_const.mul
    (finiteFrameMetricC0Coefficient_contDiff period hPeriod frame baseMetric metricRow metricColumn)).add
  (contDiff_const.mul
    (finiteFrameMetricC0FirstDerivative_contDiff period hPeriod frame baseMetric derivative
      metricRow metricColumn))

def finiteFrameKoszulLowerC0Derivative (derivative first second lower : Fin frame.count)
    (variation : Model) : C0Scalar period hPeriod :=
  (1 / 2 : Real) •
    (finiteFrameMetricC0SecondDerivative period hPeriod frame baseMetric derivative first
        second lower variation +
      finiteFrameMetricC0SecondDerivative period hPeriod frame baseMetric derivative second
        first lower variation -
      finiteFrameMetricC0SecondDerivative period hPeriod frame baseMetric derivative lower
        first second variation -
      (∑ contracted : Fin frame.count,
        finiteFrameStructureMetricC0DerivativeTerm period hPeriod frame baseMetric derivative
          second lower contracted first contracted variation) +
      (∑ contracted : Fin frame.count,
        finiteFrameStructureMetricC0DerivativeTerm period hPeriod frame baseMetric derivative
          lower first contracted second contracted variation) +
      ∑ contracted : Fin frame.count,
        finiteFrameStructureMetricC0DerivativeTerm period hPeriod frame baseMetric derivative
          first second contracted lower contracted variation)

theorem finiteFrameKoszulLowerC0Derivative_contDiff
    (derivative first second lower : Fin frame.count) :
    ContDiff Real ∞
      (finiteFrameKoszulLowerC0Derivative period hPeriod frame baseMetric derivative first second lower) := by
  have hSecond := finiteFrameMetricC0SecondDerivative_contDiff period hPeriod frame baseMetric
  have hTerm := finiteFrameStructureMetricC0DerivativeTerm_contDiff period hPeriod frame baseMetric
  have hSum (bracketFirst bracketSecond metricRow : Fin frame.count) : ContDiff Real ∞
      (fun variation : Model => ∑ contracted : Fin frame.count,
        finiteFrameStructureMetricC0DerivativeTerm period hPeriod frame baseMetric derivative
          bracketFirst bracketSecond contracted metricRow contracted variation) := by
    apply ContDiff.sum
    intro contracted _
    exact hTerm derivative bracketFirst bracketSecond contracted metricRow contracted
  have hBase := ((hSecond derivative first second lower).add
    (hSecond derivative second first lower)).sub (hSecond derivative lower first second)
  have hFirst := hBase.sub (hSum second lower first)
  have hSecondTerm := hFirst.add (hSum lower first second)
  have hResult := hSecondTerm.add (hSum first second lower)
  exact hResult.const_smul (1 / 2 : Real)

def finiteFrameChristoffelC0Derivative (derivative upper first second : Fin frame.count)
    (variation : Model) : C0Scalar period hPeriod :=
  ∑ lower : Fin frame.count,
    (finiteFrameInverseMetricC0FirstDerivative period hPeriod frame baseMetric derivative upper lower variation *
        finiteFrameKoszulLowerC0Coefficient period hPeriod frame baseMetric first second lower variation +
      finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric upper lower variation *
        finiteFrameKoszulLowerC0Derivative period hPeriod frame baseMetric derivative first second lower variation)

theorem finiteFrameChristoffelC0Derivative_contDiffOn
    (derivative upper first second : Fin frame.count) :
    ContDiffOn Real ∞
      (finiteFrameChristoffelC0Derivative period hPeriod frame baseMetric derivative upper first second)
      Domain := by
  apply ContDiffOn.sum
  intro lower _
  exact ((finiteFrameInverseMetricC0FirstDerivative_contDiffOn period hPeriod frame baseMetric
    derivative upper lower).mul
      (finiteFrameKoszulLowerC0Coefficient_contDiff period hPeriod frame baseMetric
        first second lower).contDiffOn).add
    ((finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame baseMetric upper lower).mul
      (finiteFrameKoszulLowerC0Derivative_contDiff period hPeriod frame baseMetric
        derivative first second lower).contDiffOn)

def finiteFrameRiemannC0Coefficient (upper lower first second : Fin frame.count)
    (variation : Model) : C0Scalar period hPeriod :=
  finiteFrameChristoffelC0Derivative period hPeriod frame baseMetric first upper second lower variation -
    finiteFrameChristoffelC0Derivative period hPeriod frame baseMetric second upper first lower variation +
    (∑ contracted : Fin frame.count,
      finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric contracted second lower variation *
        finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric upper first contracted variation) -
    (∑ contracted : Fin frame.count,
      finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric contracted first lower variation *
        finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric upper second contracted variation) -
    ∑ contracted : Fin frame.count,
      finiteFrameStructureC0Coefficient period hPeriod frame baseMetric first second contracted *
        finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric upper contracted lower variation

theorem finiteFrameRiemannC0Coefficient_contDiffOn
    (upper lower first second : Fin frame.count) :
    ContDiffOn Real ∞
      (finiteFrameRiemannC0Coefficient period hPeriod frame baseMetric upper lower first second) Domain := by
  have hGamma := finiteFrameChristoffelC0Coefficient_contDiffOn period hPeriod frame baseMetric
  exact ((((finiteFrameChristoffelC0Derivative_contDiffOn period hPeriod frame baseMetric
    first upper second lower).sub
      (finiteFrameChristoffelC0Derivative_contDiffOn period hPeriod frame baseMetric
        second upper first lower)).add
      (ContDiffOn.sum fun contracted _ => (hGamma contracted second lower).mul
        (hGamma upper first contracted))).sub
      (ContDiffOn.sum fun contracted _ => (hGamma contracted first lower).mul
        (hGamma upper second contracted))).sub
      (ContDiffOn.sum fun contracted _ => contDiffOn_const.mul (hGamma upper contracted lower))

def finiteFrameRicciC0Coefficient (first second : Fin frame.count)
    (variation : Model) : C0Scalar period hPeriod :=
  ∑ contracted : Fin frame.count,
    finiteFrameRiemannC0Coefficient period hPeriod frame baseMetric
      contracted first contracted second variation

theorem finiteFrameRicciC0Coefficient_contDiffOn (first second : Fin frame.count) :
    ContDiffOn Real ∞
      (finiteFrameRicciC0Coefficient period hPeriod frame baseMetric first second) Domain := by
  apply ContDiffOn.sum
  intro contracted _
  exact finiteFrameRiemannC0Coefficient_contDiffOn period hPeriod frame baseMetric
    contracted first contracted second

def finiteFrameScalarCurvatureC0 (variation : Model) : C0Scalar period hPeriod :=
  ∑ first : Fin frame.count, ∑ second : Fin frame.count,
    finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric first second variation *
      finiteFrameRicciC0Coefficient period hPeriod frame baseMetric first second variation

theorem finiteFrameScalarCurvatureC0_contDiffOn_two :
    ContDiffOn Real 2 (finiteFrameScalarCurvatureC0 period hPeriod frame baseMetric) Domain := by
  apply ContDiffOn.sum
  intro first _
  apply ContDiffOn.sum
  intro second _
  exact ((finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame baseMetric
    first second).of_le (WithTop.coe_le_coe.mpr le_top)).mul
    ((finiteFrameRicciC0Coefficient_contDiffOn period hPeriod frame baseMetric
      first second).of_le (WithTop.coe_le_coe.mpr le_top))

end
end P0EFTJanusFiniteFrameC2ScalarCurvature4D
end JanusFormal
