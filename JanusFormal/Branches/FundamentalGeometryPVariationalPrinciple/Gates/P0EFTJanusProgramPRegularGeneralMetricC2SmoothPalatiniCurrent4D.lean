import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelSpatialCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PalatiniGlobalVector4D

/-! # Smooth Palatini current of the genuine metric variation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D

set_option autoImplicit false

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
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameAnholonomicPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2RicciConnectionVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2TorsionFreePalatiniJet4D
open P0EFTJanusProgramPRegularGeneralMetricC2MetricCompatiblePalatiniJet4D
open P0EFTJanusProgramPRegularGeneralMetricC2PalatiniGlobalVector4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelSpatialCompatibility4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

/-- Smooth regular-frame coefficient of
`Vᵃ = gᵇᶜ δΓᵃ_cb - gᵇᵃ δΓᶜ_cb`. -/
def regularFrameSmoothPalatiniCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (vector : Index4) : SmoothScalarField period hPeriod :=
  (∑ first : Index4, ∑ second : Index4,
      smoothScalarFieldMul period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric first second)
        (regularFrameSmoothChristoffelVariationCoefficient period hPeriod
          metric tensor vector second first)) -
    ∑ first : Index4, ∑ contracted : Index4,
      smoothScalarFieldMul period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric first vector)
        (regularFrameSmoothChristoffelVariationCoefficient period hPeriod
          metric tensor contracted contracted first)

/-- The smooth coefficient is exactly the coefficient of the concrete
metric-compatible Palatini jet. -/
theorem regularFrameSmoothPalatiniCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (vector : Index4) :
    regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector
        point =
      regularGeneralMetricC2PalatiniFrameCoefficient period hPeriod metric
        tensor point vector := by
  unfold regularFrameSmoothPalatiniCoefficient
    regularGeneralMetricC2PalatiniFrameCoefficient regularFramePalatiniVector
  simp only [regularGeneralMetricC2MetricCompatiblePalatiniJetAt,
    regularGeneralMetricC2TorsionFreeConnectionVariationJetAt,
    regularGeneralMetricC2ConnectionVariationJetAt,
    smoothScalarFieldSub_apply, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply]
  simp_rw [regularGeneralMetricC0ChristoffelFDerivativeAtZero_smooth]
  rfl

/-- The Palatini current as a genuine smooth tangent-vector field. -/
def regularGeneralMetricC2SmoothPalatiniVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothTangentField period hPeriod where
  toFun := fun point =>
    ∑ vector : Index4,
      regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector
          point • metric.frame vector point
  contMDiff_toFun := by
    apply ContMDiff.sum_section
    intro vector _
    exact
      (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
        vector).contMDiff_toFun.smul_section
          (metric.frame vector).contMDiff_toFun

@[simp]
theorem regularGeneralMetricC2SmoothPalatiniVector_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric tensor
        point =
      regularGeneralMetricC2PalatiniVectorAt period hPeriod metric tensor
        point := by
  unfold regularGeneralMetricC2SmoothPalatiniVector
    regularGeneralMetricC2PalatiniVectorAt
  change (∑ vector : Index4,
      regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector
          point • metric.frame vector point) = _
  apply Finset.sum_congr rfl
  intro vector _
  rw [regularFrameSmoothPalatiniCoefficient_apply]

/-- Gate marker: the concrete Palatini current is globally smooth. -/
theorem regular_general_metric_c2_smooth_palatini_current_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric tensor
        point =
      regularGeneralMetricC2PalatiniVectorAt period hPeriod metric tensor
        point :=
  regularGeneralMetricC2SmoothPalatiniVector_apply period hPeriod metric tensor
    point

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D
end JanusFormal
