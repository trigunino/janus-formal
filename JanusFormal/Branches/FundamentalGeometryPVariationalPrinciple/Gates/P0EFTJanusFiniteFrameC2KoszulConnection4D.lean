import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameScalarC2Derivatives4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameKoszulCoefficients4D

/-! # The finite-frame connection as a function of the actual C² metric

Metric coefficients, their first spatial derivatives, and inverse coefficients
are read from the same relative metric core. The fixed bracket coefficients
give the nonholonomic Koszul terms. No independent metric jets are supplied.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2KoszulConnection4D

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
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D
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

private theorem metricCoefficient_contDiff (row column : Fin frame.count) :
    ContDiff Real ∞ (fun variation : Model =>
      finiteFrameMetricC2Coefficients period hPeriod frame baseMetric variation row column) :=
  (contDiff_apply Real (C2Scalar period hPeriod) column).comp
    ((contDiff_apply Real (Fin frame.count → C2Scalar period hPeriod) row).comp
      (finiteFrameMetricC2Coefficients_contDiff period hPeriod frame baseMetric))

def finiteFrameMetricC0Coefficient (row column : Fin frame.count) (variation : Model) :
    C0Scalar period hPeriod :=
  canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (finiteFrameMetricC2Coefficients period hPeriod frame baseMetric variation row column)

theorem finiteFrameMetricC0Coefficient_contDiff (row column : Fin frame.count) :
    ContDiff Real ∞ (finiteFrameMetricC0Coefficient period hPeriod frame baseMetric row column) :=
  (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff.comp
    (metricCoefficient_contDiff period hPeriod frame baseMetric row column)

def finiteFrameMetricC0FirstDerivative
    (derivative row column : Fin frame.count) (variation : Model) : C0Scalar period hPeriod :=
  finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame derivative
    (finiteFrameMetricC2Coefficients period hPeriod frame baseMetric variation row column)

theorem finiteFrameMetricC0FirstDerivative_contDiff (derivative row column : Fin frame.count) :
    ContDiff Real ∞
      (finiteFrameMetricC0FirstDerivative period hPeriod frame baseMetric derivative row column) :=
  (finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame derivative).contDiff.comp
    (metricCoefficient_contDiff period hPeriod frame baseMetric row column)

theorem finiteFrameMetricC0Coefficient_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation) (row column : Fin frame.count) :
    finiteFrameMetricC0Coefficient period hPeriod frame baseMetric row column
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (generalMetricFrameCoefficient period hPeriod frame metric.tensor row column) := by
  unfold finiteFrameMetricC0Coefficient
  rw [finiteFrameMetricC2Coefficients_smooth period hPeriod frame baseMetric variation metric hMetric]
  exact canonicalPhysicalScalarC2JetCoreToContinuous_smooth period hPeriod _

theorem finiteFrameMetricC0FirstDerivative_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (derivative row column : Fin frame.count) :
    finiteFrameMetricC0FirstDerivative period hPeriod frame baseMetric derivative row column
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (frameDerivativeComponentField period hPeriod frame
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor row column) derivative) := by
  apply ContinuousMap.ext
  intro point
  unfold finiteFrameMetricC0FirstDerivative
  rw [finiteFrameMetricC2Coefficients_smooth period hPeriod frame baseMetric variation metric hMetric]
  exact finiteFrameScalarC2FirstDerivative_smooth period hPeriod baseMetric frame derivative _ point

/-- Fixed smooth structure coefficients of the actual finite generating family. -/
def finiteFrameStructureC0Coefficient (first second upper : Fin frame.count) : C0Scalar period hPeriod :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod
    (finiteFrameStructureCoefficient period hPeriod frame baseMetric first second upper)

/-- All metric terms come from one C² variation. -/
def finiteFrameKoszulLowerC0Coefficient (first second lower : Fin frame.count)
    (variation : Model) : C0Scalar period hPeriod :=
  (1 / 2 : Real) •
    (finiteFrameMetricC0FirstDerivative period hPeriod frame baseMetric first second lower variation +
      finiteFrameMetricC0FirstDerivative period hPeriod frame baseMetric second first lower variation -
      finiteFrameMetricC0FirstDerivative period hPeriod frame baseMetric lower first second variation -
      (∑ index : Fin frame.count,
        finiteFrameStructureC0Coefficient period hPeriod frame baseMetric second lower index *
          finiteFrameMetricC0Coefficient period hPeriod frame baseMetric first index variation) +
      (∑ index : Fin frame.count,
        finiteFrameStructureC0Coefficient period hPeriod frame baseMetric lower first index *
          finiteFrameMetricC0Coefficient period hPeriod frame baseMetric second index variation) +
      ∑ index : Fin frame.count,
        finiteFrameStructureC0Coefficient period hPeriod frame baseMetric first second index *
          finiteFrameMetricC0Coefficient period hPeriod frame baseMetric lower index variation)

theorem finiteFrameKoszulLowerC0Coefficient_contDiff (first second lower : Fin frame.count) :
    ContDiff Real ∞ (finiteFrameKoszulLowerC0Coefficient period hPeriod frame baseMetric first second lower) := by
  have hMetric := finiteFrameMetricC0Coefficient_contDiff period hPeriod frame baseMetric
  have hDerivative := finiteFrameMetricC0FirstDerivative_contDiff period hPeriod frame baseMetric
  have hBracket (a b c : Fin frame.count) : ContDiff Real ∞ (fun variation : Model =>
      ∑ index : Fin frame.count, finiteFrameStructureC0Coefficient period hPeriod frame baseMetric a b index *
        finiteFrameMetricC0Coefficient period hPeriod frame baseMetric c index variation) := by
    apply ContDiff.sum
    intro index _
    exact contDiff_const.mul (hMetric c index)
  have hBase := ((hDerivative first second lower).add (hDerivative second first lower)).sub
    (hDerivative lower first second)
  have hResult := ((hBase.sub (hBracket second lower first)).add
    (hBracket lower first second)).add (hBracket first second lower)
  exact ContDiff.const_smul (1 / 2 : Real) hResult

/-- The actual inverse metric raises the last Koszul slot. -/
def finiteFrameChristoffelC0Coefficient (upper first second : Fin frame.count)
    (variation : Model) : C0Scalar period hPeriod :=
  ∑ lower : Fin frame.count,
    finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric upper lower variation *
      finiteFrameKoszulLowerC0Coefficient period hPeriod frame baseMetric first second lower variation

theorem finiteFrameChristoffelC0Coefficient_contDiffOn (upper first second : Fin frame.count) :
    ContDiffOn Real ∞ (finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric upper first second)
      (generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) := by
  apply ContDiffOn.sum
  intro lower _
  exact (finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame baseMetric upper lower).mul
    (finiteFrameKoszulLowerC0Coefficient_contDiff period hPeriod frame baseMetric first second lower).contDiffOn

theorem finiteFrameKoszulLowerC0Coefficient_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (first second lower : Fin frame.count) :
    finiteFrameKoszulLowerC0Coefficient period hPeriod frame baseMetric first second lower
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameKoszulLowerCoefficient period hPeriod frame baseMetric metric first second lower) := by
  apply ContinuousMap.ext
  intro point
  have hValue (row column : Fin frame.count) :
      finiteFrameMetricC0Coefficient period hPeriod frame baseMetric row column
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) point =
      generalMetricFrameCoefficient period hPeriod frame metric.tensor row column point :=
    congrArg (fun value : C0Scalar period hPeriod => value point)
      (finiteFrameMetricC0Coefficient_smooth period hPeriod frame baseMetric variation metric hMetric row column)
  have hDerivative (direction row column : Fin frame.count) :
      finiteFrameMetricC0FirstDerivative period hPeriod frame baseMetric direction row column
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) point =
      frameDerivative period hPeriod Real frame
        (generalMetricFrameCoefficient period hPeriod frame metric.tensor row column) point direction :=
    congrArg (fun value : C0Scalar period hPeriod => value point)
      (finiteFrameMetricC0FirstDerivative_smooth period hPeriod frame baseMetric variation metric hMetric
        direction row column)
  change finiteFrameKoszulLowerC0Coefficient period hPeriod frame baseMetric first second lower
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) point =
      finiteFrameKoszulLowerCoefficient period hPeriod frame baseMetric metric first second lower point
  rw [finiteFrameKoszulLowerCoefficient_apply]
  simp only [finiteFrameKoszulLowerC0Coefficient, ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply, hValue, hDerivative,
    finiteFrameStructureC0Coefficient, smul_eq_mul]
  rfl

/-- On affine smooth inputs, the completed connection is the genuine smooth Koszul connection. -/
theorem finiteFrameChristoffelC0Coefficient_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (upper first second : Fin frame.count) :
    finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric upper first second
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric upper first second) := by
  apply ContinuousMap.ext
  intro point
  change finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric upper first second
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) point =
      finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric upper first second point
  rw [finiteFrameKoszulChristoffelCoefficient_apply]
  simp only [finiteFrameChristoffelC0Coefficient, ContinuousMap.sum_apply, ContinuousMap.mul_apply]
  apply Finset.sum_congr rfl
  intro lower _
  simp only [finiteFrameInverseMetricC0Coefficient_smooth period hPeriod frame baseMetric variation metric
    hMetric hVariation upper lower,
    finiteFrameKoszulLowerC0Coefficient_smooth period hPeriod frame baseMetric variation metric hMetric
      first second lower]
  rfl

/-- SAME-CONNECTION with the already constructed local Levi-Civita derivative, in every chart. -/
theorem finiteFrameChristoffelC0Coefficient_eq_local
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (upper first second : Fin frame.count) :
    finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric upper first second
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation)
      (patch.coordinateMap coordinate) =
      finiteFrameTensorChristoffelCoefficient period hPeriod frame baseMetric metric patch coordinate
        upper first second := by
  have hSmooth := congrArg (fun value : C0Scalar period hPeriod => value (patch.coordinateMap coordinate))
    (finiteFrameChristoffelC0Coefficient_smooth period hPeriod frame baseMetric variation metric hMetric
      hVariation upper first second)
  exact hSmooth.trans (finiteFrameKoszulChristoffelCoefficient_eq_local period hPeriod frame baseMetric metric
    patch coordinate upper first second)

end
end P0EFTJanusFiniteFrameC2KoszulConnection4D
end JanusFormal
