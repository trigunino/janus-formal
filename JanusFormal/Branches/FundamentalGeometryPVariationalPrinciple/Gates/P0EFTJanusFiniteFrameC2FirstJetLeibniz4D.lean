import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2MetricTensorTrace4D

/-! # Exact first-jet Leibniz law on the complete scalar C² core

Density and continuity extend the intrinsic smooth product rule to every
completed scalar jet. The metric trace differential consequently factors
through the values and first derivatives of its two actual coefficient matrices.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2FirstJetLeibniz4D

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
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorTrace4D

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

private abbrev SmoothTangentSection := ContMDiffSection coverModelWithCorners CoverCoordinates ∞
  (fun point : EffectiveQuotient period hPeriod => TangentSpace coverModelWithCorners point)

theorem smoothVectorScalarLieDerivative_mul
    (vector : SmoothTangentSection period hPeriod)
    (first second : SmoothScalarField period hPeriod) :
    smoothVectorScalarLieDerivative period hPeriod vector (smoothScalarFieldMul period hPeriod first second) =
      smoothScalarFieldMul period hPeriod (smoothVectorScalarLieDerivative period hPeriod vector first) second +
      smoothScalarFieldMul period hPeriod first (smoothVectorScalarLieDerivative period hPeriod vector second) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change mvfderiv coverModelWithCorners (first.toFun * second.toFun) point (vector point) =
    mvfderiv coverModelWithCorners first.toFun point (vector point) * second point +
      first point * mvfderiv coverModelWithCorners second.toFun point (vector point)
  rw [mvfderiv_mul
    (first.contMDiff_toFun.mdifferentiableAt (by simp))
    (second.contMDiff_toFun.mdifferentiableAt (by simp))]
  change first point * mvfderiv coverModelWithCorners second.toFun point (vector point) +
    second point * mvfderiv coverModelWithCorners first.toFun point (vector point) = _
  ring

/-- Leibniz holds on the whole complete C² core, for every fixed smooth section. -/
theorem smoothVectorScalarC2FirstDerivative_product
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentSection period hPeriod) (first second : C2Scalar period hPeriod) :
    smoothVectorScalarC2FirstDerivative period hPeriod reference vector
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod first second) =
    smoothVectorScalarC2FirstDerivative period hPeriod reference vector first *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod second +
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod first *
        smoothVectorScalarC2FirstDerivative period hPeriod reference vector second := by
  refine DenseRange.induction_on₂
    (smoothToCanonicalPhysicalScalarC2JetCore_denseRange period hPeriod) ?_ ?_ first second
  · apply isClosed_eq
    · exact (smoothVectorScalarC2FirstDerivative period hPeriod reference vector).continuous.comp
        (canonicalPhysicalScalarC2JetCoreProduct_contDiff period hPeriod).continuous
    · exact (((smoothVectorScalarC2FirstDerivative period hPeriod reference vector).continuous.comp
        continuous_fst).mul
          ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).continuous.comp continuous_snd)).add
        (((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).continuous.comp continuous_fst).mul
          ((smoothVectorScalarC2FirstDerivative period hPeriod reference vector).continuous.comp continuous_snd))
  · intro smoothFirst smoothSecond
    rw [canonicalPhysicalScalarC2JetCoreProduct_smooth]
    apply ContinuousMap.ext
    intro point
    simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply,
      smoothVectorScalarC2FirstDerivative_smooth, canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
    exact congrArg (fun field : SmoothScalarField period hPeriod => field point)
      (smoothVectorScalarLieDerivative_mul period hPeriod vector smoothFirst smoothSecond)

theorem finiteFrameScalarC2FirstDerivative_product
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (first second : C2Scalar period hPeriod) :
    finiteFrameScalarC2FirstDerivative period hPeriod reference frame index
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod first second) =
    finiteFrameScalarC2FirstDerivative period hPeriod reference frame index first *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod second +
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod first *
        finiteFrameScalarC2FirstDerivative period hPeriod reference frame index second :=
  smoothVectorScalarC2FirstDerivative_product period hPeriod reference
    (P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D.smoothFrameVectorSection
      period hPeriod frame index) first second

theorem finiteFrameC2MatrixTrace_product_derivative
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (index : Fin frame.count)
    (first second : C2FiniteMatrix period hPeriod frame.count) :
    finiteFrameScalarC2FirstDerivative period hPeriod reference frame index
      (finiteFrameC2MatrixTraceCLM period hPeriod frame.count
        (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count first second)) =
    ∑ row : Fin frame.count, ∑ column : Fin frame.count,
      (finiteFrameScalarC2FirstDerivative period hPeriod reference frame index (first row column) *
          canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (second column row) +
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (first row column) *
          finiteFrameScalarC2FirstDerivative period hPeriod reference frame index (second column row)) := by
  rw [finiteFrameC2MatrixTraceCLM_apply, map_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [c2FiniteMatrixProduct_apply, map_sum]
  apply Finset.sum_congr rfl
  intro column _
  exact finiteFrameScalarC2FirstDerivative_product period hPeriod reference frame index
    (first row column) (second column row)

/-- The completed metric trace gradient only uses the first jets of its actual factors. -/
theorem finiteFrameMetricTensorTraceGradientC0_eq_sum_firstJets
    (frame : SmoothD8Frame period hPeriod) (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin frame.count)
    (metricVariation tensorVariation : GeneralMetricRelativeC2Core period hPeriod frame baseMetric) :
    finiteFrameMetricTensorTraceGradientC0 period hPeriod frame baseMetric index metricVariation tensorVariation =
    ∑ row : Fin frame.count, ∑ column : Fin frame.count,
      (finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame index
          (finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric metricVariation row column) *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (finiteFrameRelativeC2ToTensorCoefficients period hPeriod frame baseMetric tensorVariation column row) +
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric metricVariation row column) *
        finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame index
          (finiteFrameRelativeC2ToTensorCoefficients period hPeriod frame baseMetric tensorVariation column row)) :=
  finiteFrameC2MatrixTrace_product_derivative period hPeriod baseMetric frame index
    (finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric metricVariation)
    (finiteFrameRelativeC2ToTensorCoefficients period hPeriod frame baseMetric tensorVariation)

end
end P0EFTJanusFiniteFrameC2FirstJetLeibniz4D
end JanusFormal
