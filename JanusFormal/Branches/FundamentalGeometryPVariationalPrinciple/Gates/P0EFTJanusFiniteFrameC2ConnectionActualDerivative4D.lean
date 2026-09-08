import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ScalarCurvatureSmoothCoefficients4D

/-! # Actual derivatives of the smooth finite-frame connection -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2ConnectionActualDerivative4D

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
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2CurvatureSmoothJets4D
open P0EFTJanusFiniteFrameC2ConnectionSmoothDerivative4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)

private theorem frameDerivativeComponentField_zero
    (derivative : Fin frame.count) :
    frameDerivativeComponentField period hPeriod frame
        (0 : SmoothScalarField period hPeriod) derivative = 0 := by
  simpa using frameDerivativeComponentField_smul period hPeriod frame
    (0 : Real) (0 : SmoothScalarField period hPeriod) derivative

private theorem frameDerivativeComponentField_sub
    (first second : SmoothScalarField period hPeriod)
    (derivative : Fin frame.count) :
    frameDerivativeComponentField period hPeriod frame (first - second) derivative =
      frameDerivativeComponentField period hPeriod frame first derivative -
        frameDerivativeComponentField period hPeriod frame second derivative := by
  rw [sub_eq_add_neg, sub_eq_add_neg,
    show -second = (-1 : Real) • second by simp,
    frameDerivativeComponentField_add,
    frameDerivativeComponentField_smul]
  simp

private theorem frameDerivativeComponentField_finset_sum
    {ι : Type*} (set : Finset ι)
    (fields : ι → SmoothScalarField period hPeriod)
    (derivative : Fin frame.count) :
    frameDerivativeComponentField period hPeriod frame
        (∑ index ∈ set, fields index) derivative =
      ∑ index ∈ set,
        frameDerivativeComponentField period hPeriod frame (fields index) derivative := by
  classical
  induction set using Finset.induction_on with
  | empty => simpa using frameDerivativeComponentField_zero period hPeriod frame derivative
  | @insert index set hIndex induction =>
      simp only [Finset.sum_insert hIndex]
      rw [frameDerivativeComponentField_add, induction]

private theorem frameDerivativeComponentField_univ_sum
    {ι : Type*} [Fintype ι]
    (fields : ι → SmoothScalarField period hPeriod)
    (derivative : Fin frame.count) :
    frameDerivativeComponentField period hPeriod frame
        (∑ index : ι, fields index) derivative =
      ∑ index : ι,
        frameDerivativeComponentField period hPeriod frame (fields index) derivative := by
  simpa using frameDerivativeComponentField_finset_sum period hPeriod frame
    (Finset.univ : Finset ι) fields derivative

/-- Public smooth expansion of the lowered Koszul formula. -/
def finiteFrameSmoothKoszulLowerExpanded
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second lower : Fin frame.count) : SmoothScalarField period hPeriod :=
  (1 / 2 : Real) •
    (frameDerivativeComponentField period hPeriod frame
        (generalMetricFrameCoefficient period hPeriod frame metric.tensor second lower) first +
      frameDerivativeComponentField period hPeriod frame
        (generalMetricFrameCoefficient period hPeriod frame metric.tensor first lower) second -
      frameDerivativeComponentField period hPeriod frame
        (generalMetricFrameCoefficient period hPeriod frame metric.tensor first second) lower -
      (∑ contracted : Fin frame.count,
        smoothScalarFieldMul period hPeriod
          (finiteFrameStructureCoefficient period hPeriod frame baseMetric second lower contracted)
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor first contracted)) +
      (∑ contracted : Fin frame.count,
        smoothScalarFieldMul period hPeriod
          (finiteFrameStructureCoefficient period hPeriod frame baseMetric lower first contracted)
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor second contracted)) +
      ∑ contracted : Fin frame.count,
        smoothScalarFieldMul period hPeriod
          (finiteFrameStructureCoefficient period hPeriod frame baseMetric first second contracted)
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor lower contracted))

/-- The public expansion is the intrinsic finite-frame lowered Koszul coefficient. -/
theorem finiteFrameSmoothKoszulLowerExpanded_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second lower : Fin frame.count) :
    finiteFrameSmoothKoszulLowerExpanded period hPeriod frame baseMetric metric first second lower =
      finiteFrameKoszulLowerCoefficient period hPeriod frame baseMetric metric first second lower := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [finiteFrameSmoothKoszulLowerExpanded,
    finiteFrameKoszulLowerCoefficient_apply, smoothScalarFieldSmul_toFun,
    smoothScalarFieldAdd_apply, smoothScalarFieldSub_apply,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply]
  rfl

private theorem frameDerivativeComponentField_structureMetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (derivative bracketFirst bracketSecond contracted metricRow metricColumn : Fin frame.count) :
    frameDerivativeComponentField period hPeriod frame
        (smoothScalarFieldMul period hPeriod
          (finiteFrameStructureCoefficient period hPeriod frame baseMetric
            bracketFirst bracketSecond contracted)
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor metricRow metricColumn))
        derivative =
      finiteFrameSmoothStructureMetricDerivativeTerm period hPeriod frame baseMetric metric
        derivative bracketFirst bracketSecond contracted metricRow metricColumn := by
  rw [frameDerivativeComponentField_mul]
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [finiteFrameSmoothStructureMetricDerivativeTerm,
    smoothScalarFieldAdd_apply, smoothScalarFieldMul_apply]
  ring

/-- The smooth lowered-Koszul jet is its genuine frame derivative. -/
theorem finiteFrameSmoothKoszulLowerDerivative_eq_frameDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (derivative first second lower : Fin frame.count) :
    finiteFrameSmoothKoszulLowerDerivative period hPeriod frame baseMetric metric
        derivative first second lower =
      frameDerivativeComponentField period hPeriod frame
        (finiteFrameKoszulLowerCoefficient period hPeriod frame baseMetric metric first second lower)
        derivative := by
  rw [← finiteFrameSmoothKoszulLowerExpanded_eq period hPeriod frame baseMetric metric first second lower]
  unfold finiteFrameSmoothKoszulLowerExpanded
  rw [frameDerivativeComponentField_smul]
  simp_rw [frameDerivativeComponentField_add period hPeriod frame]
  simp_rw [frameDerivativeComponentField_sub period hPeriod frame]
  simp_rw [frameDerivativeComponentField_add period hPeriod frame,
    frameDerivativeComponentField_univ_sum period hPeriod frame,
    frameDerivativeComponentField_structureMetric period hPeriod frame baseMetric metric]
  rfl

/-- Smooth sum expansion of the raised finite-frame connection coefficient. -/
theorem finiteFrameKoszulChristoffelCoefficient_eq_sum
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (upper first second : Fin frame.count) :
    finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric upper first second =
      ∑ lower : Fin frame.count,
        smoothScalarFieldMul period hPeriod
          (finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric upper lower)
          (finiteFrameKoszulLowerCoefficient period hPeriod frame baseMetric metric first second lower) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [finiteFrameKoszulChristoffelCoefficient_apply,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply]

/-- The smooth Christoffel jet is its genuine frame derivative. -/
theorem finiteFrameSmoothChristoffelDerivative_eq_frameDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (derivative upper first second : Fin frame.count) :
    finiteFrameSmoothChristoffelDerivative period hPeriod frame baseMetric metric
        derivative upper first second =
      frameDerivativeComponentField period hPeriod frame
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric upper first second)
        derivative := by
  rw [finiteFrameKoszulChristoffelCoefficient_eq_sum period hPeriod frame baseMetric metric]
  rw [frameDerivativeComponentField_univ_sum]
  simp_rw [frameDerivativeComponentField_mul,
    ← finiteFrameSmoothKoszulLowerDerivative_eq_frameDerivative period hPeriod frame baseMetric metric]
  unfold finiteFrameSmoothChristoffelDerivative
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldAdd_apply, smoothScalarFieldMul_apply]
  apply Finset.sum_congr rfl
  intro lower _
  ring

end
end P0EFTJanusFiniteFrameC2ConnectionActualDerivative4D
end JanusFormal
