import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameKoszulCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameMetricTensorTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D

/-! Native de Donder as scalar differential columns, without a regular frame. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDeDonderScalar4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusFiniteFrameMetricContraction4D P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local notation "frame" => finiteSmoothTangentFrame period hPeriod
private abbrev FrameIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "N" => FrameIndex period hPeriod
local notation "Tensor" => SmoothSymmetricCovariantTwoTensor period hPeriod
variable (metric : SmoothGeneralLorentzMetric period hPeriod)

theorem frameFreeDeDonder_trace_expression (tensor : Tensor) :
    generalMetricTensorTrace period hPeriod metric tensor =
      ∑ i : N, ∑ j : N, canonicalScalarMul period hPeriod
        (finiteFrameInverseMetricCoefficient period hPeriod frame metric metric i j)
        (generalMetricFrameCoefficient period hPeriod frame tensor i j) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [canonicalScalar_sum_apply]
  exact generalMetricTensorTrace_eq_finiteFrameContraction period hPeriod frame metric metric tensor point

/-- The two connection corrections and the differentiated trace are retained. -/
theorem frameFreeDeDonder_scalar_expression (tensor : Tensor) (last : N) :
    globalSmoothCovectorFrameCoefficient period hPeriod
      (globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor) last =
    (∑ i : N, ∑ j : N, canonicalScalarMul period hPeriod
      (finiteFrameInverseMetricCoefficient period hPeriod frame metric metric i j)
      (canonicalFrameDerivativeSmooth period hPeriod frame i
        (generalMetricFrameCoefficient period hPeriod frame tensor j last) -
        ∑ k : N, canonicalScalarMul period hPeriod
          (finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric k i j)
          (generalMetricFrameCoefficient period hPeriod frame tensor k last) -
        ∑ k : N, canonicalScalarMul period hPeriod
          (finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric k i last)
          (generalMetricFrameCoefficient period hPeriod frame tensor j k))) -
      (1 / 2 : Real) • canonicalFrameDerivativeSmooth period hPeriod frame last
        (∑ i : N, ∑ j : N, canonicalScalarMul period hPeriod
          (finiteFrameInverseMetricCoefficient period hPeriod frame metric metric i j)
          (generalMetricFrameCoefficient period hPeriod frame tensor i j)) := by
  rw [← frameFreeDeDonder_trace_expression period hPeriod metric tensor]
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with ⟨patch, coordinate, hPoint⟩
  rw [← hPoint]
  change globalGeneralMetricSymmetricTensorDivergence period hPeriod metric tensor.tensor
    (patch.coordinateMap coordinate) ((frame).vectorAt (patch.coordinateMap coordinate) last) +
    (-1 / 2 : Real) * (generalMetricTensorTraceDifferential period hPeriod metric tensor
      (patch.coordinateMap coordinate) ((frame).vectorAt (patch.coordinateMap coordinate) last)) = _
  rw [globalGeneralMetricSymmetricTensorDivergence_eq_finiteFrameCovariantTrace
    period hPeriod frame metric metric tensor patch coordinate last]
  have hDiv : (∑ i : N, ∑ j : N,
      finiteFrameInverseMetricCoefficient period hPeriod frame metric metric i j (patch.coordinateMap coordinate) *
      (P0EFTJanusMappingTorusH1GraphTrace4D.frameDerivative period hPeriod Real frame
        (generalMetricFrameCoefficient period hPeriod frame tensor j last) (patch.coordinateMap coordinate) i -
        (∑ k : N, P0EFTJanusFiniteFrameCovariantTensorDivergence4D.finiteFrameTensorChristoffelCoefficient
          period hPeriod frame metric metric patch coordinate k i j *
          generalMetricFrameCoefficient period hPeriod frame tensor k last (patch.coordinateMap coordinate)) -
        ∑ k : N, P0EFTJanusFiniteFrameCovariantTensorDivergence4D.finiteFrameTensorChristoffelCoefficient
          period hPeriod frame metric metric patch coordinate k i last *
          generalMetricFrameCoefficient period hPeriod frame tensor j k (patch.coordinateMap coordinate))) =
      (∑ i : N, ∑ j : N, canonicalScalarMul period hPeriod
        (finiteFrameInverseMetricCoefficient period hPeriod frame metric metric i j)
        (canonicalFrameDerivativeSmooth period hPeriod frame i
          (generalMetricFrameCoefficient period hPeriod frame tensor j last) -
          ∑ k : N, canonicalScalarMul period hPeriod
            (finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric k i j)
            (generalMetricFrameCoefficient period hPeriod frame tensor k last) -
          ∑ k : N, canonicalScalarMul period hPeriod
            (finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric k i last)
            (generalMetricFrameCoefficient period hPeriod frame tensor j k))) (patch.coordinateMap coordinate) := by
    simp only [canonicalScalar_sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change _ = _ * ((_ - (∑ k : N, canonicalScalarMul period hPeriod
      (finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric k i j)
      (generalMetricFrameCoefficient period hPeriod frame tensor k last)) (patch.coordinateMap coordinate)) -
      (∑ k : N, canonicalScalarMul period hPeriod
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric k i last)
        (generalMetricFrameCoefficient period hPeriod frame tensor j k)) (patch.coordinateMap coordinate))
    simp only [canonicalScalar_sum_apply]
    simp only [canonicalScalarMul, LinearMap.coe_mk, AddHom.coe_mk,
      P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D.smoothScalarFieldMul_apply,
      finiteFrameKoszulChristoffelCoefficient_eq_local]
    rfl
  rw [hDiv]
  change _ + (-1 / 2 : Real) * _ = _ - (1 / 2 : Real) * _
  ring_nf
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDeDonderScalar4D
