import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D

/-! # Smooth covariant divergence of the Palatini current -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameAnholonomicPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2RicciConnectionVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2TorsionFreePalatiniJet4D
open P0EFTJanusProgramPRegularGeneralMetricC2MetricCompatiblePalatiniJet4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseSpatialVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelSpatialVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelSpatialCompatibility4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev Index4 := Fin 4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

private theorem frameDerivativeComponentField_sub
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothScalarField period hPeriod)
    (derivative : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (first - second) derivative =
      frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          first derivative -
        frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          second derivative := by
  rw [sub_eq_add_neg, sub_eq_add_neg,
    show -second = (-1 : Real) • second by simp,
    frameDerivativeComponentField_add,
    frameDerivativeComponentField_smul]
  simp

private theorem frameDerivativeComponentField_mul_regular
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothScalarField period hPeriod)
    (derivative : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (smoothScalarFieldMul period hPeriod first second) derivative =
      smoothScalarFieldMul period hPeriod first
          (frameDerivativeComponentField period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            second derivative) +
        smoothScalarFieldMul period hPeriod second
          (frameDerivativeComponentField period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            first derivative) :=
  frameDerivativeComponentField_mul period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) first second
      derivative

private theorem frameDerivativeComponentField_finset_sum
    {ι : Type*} (metric : RegularGeneralLorentzMetric period hPeriod)
    (set : Finset ι) (fields : ι → SmoothScalarField period hPeriod)
    (derivative : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (∑ index ∈ set, fields index) derivative =
      ∑ index ∈ set,
        frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (fields index) derivative := by
  classical
  induction set using Finset.induction_on with
  | empty =>
      simpa using frameDerivativeComponentField_smul period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (0 : Real) (0 : SmoothScalarField period hPeriod) derivative
  | @insert index set hIndex induction =>
      simp only [Finset.sum_insert hIndex]
      rw [frameDerivativeComponentField_add, induction]

private theorem frameDerivativeComponentField_univ_sum
    {ι : Type*} [Fintype ι]
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (fields : ι → SmoothScalarField period hPeriod)
    (derivative : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (∑ index : ι, fields index) derivative =
      ∑ index : ι,
        frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (fields index) derivative := by
  simpa using frameDerivativeComponentField_finset_sum period hPeriod metric
    (Finset.univ : Finset ι) fields derivative

private theorem double_sum_product_rule_comm
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (first firstDerivative second secondDerivative : ι → κ → Real) :
    (∑ i : ι, ∑ j : κ,
        (first i j * secondDerivative i j +
          second i j * firstDerivative i j)) =
      ∑ i : ι, ∑ j : κ,
        (firstDerivative i j * second i j +
          first i j * secondDerivative i j) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Explicit smooth frame derivative of a Palatini-current coefficient. -/
def regularFrameSmoothPalatiniDerivativeCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative vector : Index4) : SmoothScalarField period hPeriod :=
  (∑ first : Index4, ∑ second : Index4,
      (smoothScalarFieldMul period hPeriod
          (regularFrameSmoothInverseDerivativeCoefficient period hPeriod metric
            derivative first second)
          (regularFrameSmoothChristoffelVariationCoefficient period hPeriod
            metric tensor vector second first) +
        smoothScalarFieldMul period hPeriod
          (regularFrameMetricInverseMatrix period hPeriod metric first second)
          (regularFrameSmoothChristoffelSpatialVariationCoefficient period
            hPeriod metric tensor derivative vector second first))) -
    ∑ first : Index4, ∑ contracted : Index4,
      (smoothScalarFieldMul period hPeriod
          (regularFrameSmoothInverseDerivativeCoefficient period hPeriod metric
            derivative first vector)
          (regularFrameSmoothChristoffelVariationCoefficient period hPeriod
            metric tensor contracted contracted first) +
        smoothScalarFieldMul period hPeriod
          (regularFrameMetricInverseMatrix period hPeriod metric first vector)
          (regularFrameSmoothChristoffelSpatialVariationCoefficient period
            hPeriod metric tensor derivative contracted contracted first))

/-- The explicit coefficient is the actual frame derivative of the smooth
Palatini current coefficient. -/
theorem regularFrameSmoothPalatiniCoefficient_frameDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative vector : Index4) :
    frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
          vector) derivative =
      regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod metric
        tensor derivative vector := by
  classical
  unfold regularFrameSmoothPalatiniCoefficient
  rw [frameDerivativeComponentField_sub,
    frameDerivativeComponentField_univ_sum]
  simp_rw [frameDerivativeComponentField_univ_sum,
    frameDerivativeComponentField_mul_regular,
    regularFrameMetricInverseMatrix_frameDerivative,
    regularFrameSmoothChristoffelVariationCoefficient_frameDerivative]
  unfold regularFrameSmoothPalatiniDerivativeCoefficient
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [smoothScalarFieldSub_apply, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldAdd_apply, smoothScalarFieldMul_apply]
  have hFirst := double_sum_product_rule_comm
    (fun first second => regularFrameMetricInverseMatrix period hPeriod metric
      first second point)
    (fun first second => regularFrameSmoothInverseDerivativeCoefficient period
      hPeriod metric derivative first second point)
    (fun first second => regularFrameSmoothChristoffelVariationCoefficient
      period hPeriod metric tensor vector second first point)
    (fun first second =>
      regularFrameSmoothChristoffelSpatialVariationCoefficient period hPeriod
        metric tensor derivative vector second first point)
  have hSecond := double_sum_product_rule_comm
    (fun first contracted => regularFrameMetricInverseMatrix period hPeriod
      metric first vector point)
    (fun first contracted =>
      regularFrameSmoothInverseDerivativeCoefficient period hPeriod metric
        derivative first vector point)
    (fun first contracted => regularFrameSmoothChristoffelVariationCoefficient
      period hPeriod metric tensor contracted contracted first point)
    (fun first contracted =>
      regularFrameSmoothChristoffelSpatialVariationCoefficient period hPeriod
        metric tensor derivative contracted contracted first point)
  rw [hFirst, hSecond]

/-- Pointwise identification with the derivative stored by the concrete
metric-compatible Palatini jet. -/
theorem regularFrameSmoothPalatiniDerivativeCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (derivative vector : Index4) :
    regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod metric
        tensor derivative vector point =
      regularFramePalatiniVectorDerivative
        (regularGeneralMetricC2MetricCompatiblePalatiniJetAt period hPeriod
          metric (regularGeneralMetricC2SmoothDirection period hPeriod metric
            tensor) point) derivative vector := by
  let jet := regularGeneralMetricC2MetricCompatiblePalatiniJetAt period hPeriod
    metric (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)
      point
  have hInverse (first second : Index4) :
      regularFrameMetricInverseMatrix period hPeriod metric first second point =
        jet.inverse first second := by
    rfl
  have hInverseDerivative (currentDerivative first second : Index4) :
      regularFrameSmoothInverseDerivativeCoefficient period hPeriod metric
          currentDerivative first second point =
        jet.frameInverseDerivative currentDerivative first second := by
    change _ = regularGeneralMetricC0InverseMetricDerivative period hPeriod
      metric 0 currentDerivative first second point
    exact (congrArg (fun field : C0Scalar period hPeriod => field point)
      (regularGeneralMetricC0InverseMetricDerivative_zero_smooth period hPeriod
        metric currentDerivative first second)).symm
  have hVariation (upper first second : Index4) :
      regularFrameSmoothChristoffelVariationCoefficient period hPeriod metric
          tensor upper first second point =
        jet.variation upper first second := by
    change _ = regularGeneralMetricC0ChristoffelFDerivativeAtZero period hPeriod
      metric upper first second
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) point
    exact (congrArg (fun field : C0Scalar period hPeriod => field point)
      (regularGeneralMetricC0ChristoffelFDerivativeAtZero_smooth period hPeriod
        metric tensor upper first second)).symm
  have hVariationDerivative
      (currentDerivative upper first second : Index4) :
      regularFrameSmoothChristoffelSpatialVariationCoefficient period hPeriod
          metric tensor currentDerivative upper first second point =
        jet.frameVariationDerivative currentDerivative upper first second := by
    change _ = regularGeneralMetricC0ChristoffelSpatialFDerivativeAtZero period
      hPeriod metric currentDerivative upper first second
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) point
    exact (congrArg (fun field : C0Scalar period hPeriod => field point)
      (regularGeneralMetricC0ChristoffelDerivative_fderiv_smooth period hPeriod
        metric tensor currentDerivative upper first second)).symm
  unfold regularFrameSmoothPalatiniDerivativeCoefficient
    regularFramePalatiniVectorDerivative
  simp only [smoothScalarFieldSub_apply, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldAdd_apply, smoothScalarFieldMul_apply]
  simp_rw [hInverse, hInverseDerivative, hVariation, hVariationDerivative]
  rfl

/-- Smooth scalar field representing the covariant Palatini divergence. -/
def regularFrameSmoothPalatiniCovariantDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothScalarField period hPeriod :=
  ∑ derivative : Index4,
    (regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod metric
        tensor derivative derivative +
      ∑ auxiliary : Index4,
        smoothScalarFieldMul period hPeriod
          (regularFrameSmoothChristoffelCoefficient period hPeriod metric
            derivative derivative auxiliary)
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
            auxiliary))

theorem regularFrameSmoothChristoffelCoefficient_eq_connection
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (upper first second : Index4) :
    regularFrameSmoothChristoffelCoefficient period hPeriod metric upper first
        second point =
      (regularGeneralMetricC2MetricCompatiblePalatiniJetAt period hPeriod metric
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)
        point).connection upper first second := by
  change _ = regularGeneralMetricC0Christoffel period hPeriod metric 0 upper
    first second point
  exact (congrArg (fun field : C0Scalar period hPeriod => field point)
    (regularGeneralMetricC0Christoffel_zero_smooth period hPeriod metric upper
      first second)).symm

/-- The smooth scalar divergence is exactly the algebraic covariant
divergence of the concrete Palatini jet at every point. -/
theorem regularFrameSmoothPalatiniCovariantDivergence_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor
        point =
      regularFramePalatiniVectorCovariantDivergence
        (regularGeneralMetricC2MetricCompatiblePalatiniJetAt period hPeriod
          metric (regularGeneralMetricC2SmoothDirection period hPeriod metric
            tensor) point) := by
  unfold regularFrameSmoothPalatiniCovariantDivergence
    regularFramePalatiniVectorCovariantDivergence
  simp only [smoothScalarFieldFinsetSum_apply, smoothScalarFieldAdd_apply,
    smoothScalarFieldMul_apply]
  apply Finset.sum_congr rfl
  intro derivative _
  rw [regularFrameSmoothPalatiniDerivativeCoefficient_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro auxiliary _
  rw [regularFrameSmoothChristoffelCoefficient_eq_connection period hPeriod
      metric tensor point derivative derivative auxiliary,
    regularFrameSmoothPalatiniCoefficient_apply]
  rfl

/-- The Palatini scalar in the exact EH variation is the value of the smooth
covariant-divergence field. -/
theorem regularGeneralMetricC0PalatiniScalarVelocity_eq_smoothDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    palatiniScalarVelocity
        (regularGeneralMetricC0InverseMetricMatrixAt period hPeriod metric 0
          point)
        (regularGeneralMetricC0RicciVelocityAt period hPeriod metric
          (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)
          point) =
      regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric
        tensor point := by
  rw [regularGeneralMetricC0PalatiniScalarVelocity_eq_covariantDivergence]
  rw [regularFrameSmoothPalatiniCovariantDivergence_apply]

/-- Gate marker for the genuine smooth Palatini divergence. -/
theorem regular_general_metric_c2_smooth_palatini_divergence_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    palatiniScalarVelocity
        (regularGeneralMetricC0InverseMetricMatrixAt period hPeriod metric 0
          point)
        (regularGeneralMetricC0RicciVelocityAt period hPeriod metric
          (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)
          point) =
      regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric
        tensor point :=
  regularGeneralMetricC0PalatiniScalarVelocity_eq_smoothDivergence period
    hPeriod metric tensor point

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D
end JanusFormal
