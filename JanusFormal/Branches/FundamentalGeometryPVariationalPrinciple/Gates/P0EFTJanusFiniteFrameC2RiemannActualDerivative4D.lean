import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ConnectionActualDerivative4D

/-! # Riemann coefficients with actual frame derivatives -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2RiemannActualDerivative4D

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
open P0EFTJanusFiniteFrameC2ScalarCurvatureSmoothCoefficients4D
open P0EFTJanusFiniteFrameC2ConnectionActualDerivative4D

variable (period : Real) (hPeriod : period ≠ 0)
variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)

/-- Riemann's nonholonomic coefficient written with genuine frame derivatives. -/
def finiteFrameActualRiemannCoefficient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (upper lower first second : Fin frame.count) : SmoothScalarField period hPeriod :=
  frameDerivativeComponentField period hPeriod frame
      (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
        upper second lower) first -
    frameDerivativeComponentField period hPeriod frame
      (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
        upper first lower) second +
    (∑ contracted : Fin frame.count,
      smoothScalarFieldMul period hPeriod
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          contracted second lower)
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          upper first contracted)) -
    (∑ contracted : Fin frame.count,
      smoothScalarFieldMul period hPeriod
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          contracted first lower)
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          upper second contracted)) -
    ∑ contracted : Fin frame.count,
      smoothScalarFieldMul period hPeriod
        (finiteFrameStructureCoefficient period hPeriod frame baseMetric first second contracted)
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          upper contracted lower)

/-- The completed smooth Riemann coefficient uses actual frame derivatives. -/
theorem finiteFrameSmoothRiemannCoefficient_eq_actual
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (upper lower first second : Fin frame.count) :
    finiteFrameSmoothRiemannCoefficient period hPeriod frame baseMetric metric
        upper lower first second =
      finiteFrameActualRiemannCoefficient period hPeriod frame baseMetric metric
        upper lower first second := by
  unfold finiteFrameSmoothRiemannCoefficient finiteFrameActualRiemannCoefficient
  rw [finiteFrameSmoothChristoffelDerivative_eq_frameDerivative,
    finiteFrameSmoothChristoffelDerivative_eq_frameDerivative]

/-- Pointwise actual-derivative formula for the smooth Riemann coefficient. -/
theorem finiteFrameSmoothRiemannCoefficient_apply_actual
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (upper lower first second : Fin frame.count)
    (point : MappingTorus (reflectedSphereData period hPeriod)) :
    finiteFrameSmoothRiemannCoefficient period hPeriod frame baseMetric metric
        upper lower first second point =
      finiteFrameActualRiemannCoefficient period hPeriod frame baseMetric metric
        upper lower first second point := by
  rw [finiteFrameSmoothRiemannCoefficient_eq_actual]

end
end P0EFTJanusFiniteFrameC2RiemannActualDerivative4D
end JanusFormal
