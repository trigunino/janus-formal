import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceCalculus4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D

/-!
# Reduction of the Palatini divergence defect to the regular frame

The metric-volume divergence is expanded in the four vectors of the regular
frame.  The derivative terms agree exactly with the explicit Palatini-current
derivatives, so the entire discrepancy is a contraction against four scalar
frame-compatibility residuals.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFramePalatiniCanonicalDivergenceReduction4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceCalculus4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Trace `Γᵃ_ab` of the regular-frame Levi--Civita connection. -/
def regularFrameLeviCivitaTrace
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : Index4) : SmoothScalarField period hPeriod :=
  ∑ derivative : Index4,
    regularFrameSmoothChristoffelCoefficient period hPeriod metric derivative
      derivative vector

/-- The only frame-level obstruction to identifying covariant and canonical
metric-volume divergence. -/
def regularFrameCanonicalDivergenceCompatibilityResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : Index4) : SmoothScalarField period hPeriod :=
  regularFrameLeviCivitaTrace period hPeriod metric vector -
    canonicalMetricVolumeDivergence period hPeriod metric
      (metric.frame vector)

private theorem smoothPalatiniVector_eq_frame_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric tensor =
      ∑ vector : Index4,
        smoothScalarSMulTangentField period hPeriod
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
            vector)
          (metric.frame vector) := by
  apply ContMDiffSection.ext
  intro point
  change
    (∑ vector : Index4,
      regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector
          point • metric.frame vector point) =
      (∑ vector : Index4,
        smoothScalarSMulTangentField period hPeriod
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
            vector) (metric.frame vector)) point
  rfl

private theorem palatiniCoefficient_directionalDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (vector : Index4) (point : EffectiveQuotient period hPeriod) :
    mvfderiv coverModelWithCorners
        (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
          vector).toFun point (metric.frame vector point) =
      regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod metric
        tensor vector vector point := by
  have hField := congrArg
    (fun field : SmoothScalarField period hPeriod => field point)
    (regularFrameSmoothPalatiniCoefficient_frameDerivative period hPeriod
      metric tensor vector vector)
  change
    frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
          vector) point vector = _ at hField
  rw [frameDerivative_eq_mfderiv] at hField
  exact hField

/-- Canonical divergence of the Palatini current expanded in the regular
frame. -/
theorem canonicalMetricVolumeDivergence_palatini_frame_expansion
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalMetricVolumeDivergence period hPeriod metric
        (regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric
          tensor) point =
      ∑ vector : Index4,
        (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
              vector point *
            canonicalMetricVolumeDivergence period hPeriod metric
              (metric.frame vector) point +
          regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod
            metric tensor vector vector point) := by
  rw [smoothPalatiniVector_eq_frame_sum period hPeriod metric tensor]
  have hSum := congrArg
    (fun field : SmoothScalarField period hPeriod => field point)
    (map_sum
      (canonicalMetricVolumeDivergenceAddMonoidHom period hPeriod metric)
      (fun vector : Index4 =>
        smoothScalarSMulTangentField period hPeriod
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
            vector) (metric.frame vector)) Finset.univ)
  change
    canonicalMetricVolumeDivergence period hPeriod metric
        (∑ vector : Index4,
          smoothScalarSMulTangentField period hPeriod
            (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
              vector) (metric.frame vector)) point = _ at hSum
  rw [hSum]
  change
    (∑ vector : Index4,
      canonicalMetricVolumeDivergence period hPeriod metric
        (smoothScalarSMulTangentField period hPeriod
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
            vector) (metric.frame vector)) point) = _
  apply Finset.sum_congr rfl
  intro vector _
  rw [canonicalMetricVolumeDivergence_smul_apply period hPeriod metric]
  rw [palatiniCoefficient_directionalDerivative period hPeriod metric tensor]

/-- Exact reduction of the Palatini/canonical discrepancy to four scalar
compatibility residuals, independent of the metric variation. -/
theorem regularFrameSmoothPalatiniCovariantDivergence_eq_canonical_add_frameResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor
        point =
      canonicalMetricVolumeDivergence period hPeriod metric
          (regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric
            tensor) point +
        ∑ vector : Index4,
          regularFrameCanonicalDivergenceCompatibilityResidual period hPeriod
              metric vector point *
            regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
              vector point := by
  rw [canonicalMetricVolumeDivergence_palatini_frame_expansion period hPeriod
    metric tensor point]
  unfold regularFrameSmoothPalatiniCovariantDivergence
    regularFrameCanonicalDivergenceCompatibilityResidual
    regularFrameLeviCivitaTrace
  change
    (∑ derivative : Index4,
        (regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod metric
            tensor derivative derivative point +
          ∑ auxiliary : Index4,
            regularFrameSmoothChristoffelCoefficient period hPeriod metric
                derivative derivative auxiliary point *
              regularFrameSmoothPalatiniCoefficient period hPeriod metric
                tensor auxiliary point)) =
      (∑ vector : Index4,
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
                vector point *
              canonicalMetricVolumeDivergence period hPeriod metric
                (metric.frame vector) point +
            regularFrameSmoothPalatiniDerivativeCoefficient period hPeriod
              metric tensor vector vector point)) +
        ∑ vector : Index4,
          ((∑ derivative : Index4,
              regularFrameSmoothChristoffelCoefficient period hPeriod metric
                derivative derivative vector point) -
              canonicalMetricVolumeDivergence period hPeriod metric
                (metric.frame vector) point) *
            regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
              vector point
  have hConnection :
      (∑ derivative : Index4, ∑ auxiliary : Index4,
          regularFrameSmoothChristoffelCoefficient period hPeriod metric
              derivative derivative auxiliary point *
            regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
              auxiliary point) =
        ∑ vector : Index4,
          (∑ derivative : Index4,
              regularFrameSmoothChristoffelCoefficient period hPeriod metric
                derivative derivative vector point) *
            regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
              vector point := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro vector _
    rw [Finset.sum_mul]
  have hResidual :
      (∑ vector : Index4,
          ((∑ derivative : Index4,
              regularFrameSmoothChristoffelCoefficient period hPeriod metric
                derivative derivative vector point) -
              canonicalMetricVolumeDivergence period hPeriod metric
                (metric.frame vector) point) *
            regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
              vector point) =
        (∑ vector : Index4,
          (∑ derivative : Index4,
              regularFrameSmoothChristoffelCoefficient period hPeriod metric
                derivative derivative vector point) *
            regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
              vector point) -
        ∑ vector : Index4,
          regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
              vector point *
            canonicalMetricVolumeDivergence period hPeriod metric
              (metric.frame vector) point := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro vector _
    ring
  rw [Finset.sum_add_distrib, hConnection, Finset.sum_add_distrib, hResidual]
  ring

/-- Vanishing of the four frame residuals removes the Palatini defect for
every smooth metric variation. -/
theorem regularFrameSmoothPalatiniCovariantDivergence_eq_canonical_of_frameCompatible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hCompatible : ∀ vector : Index4,
      regularFrameCanonicalDivergenceCompatibilityResidual period hPeriod
        metric vector = 0) :
    regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor =
      canonicalMetricVolumeDivergence period hPeriod metric
        (regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric
          tensor) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [regularFrameSmoothPalatiniCovariantDivergence_eq_canonical_add_frameResidual
    period hPeriod metric tensor point]
  have hPoint (vector : Index4) :
      regularFrameCanonicalDivergenceCompatibilityResidual period hPeriod
          metric vector point = 0 := by
    rw [hCompatible vector]
    rfl
  simp_rw [hPoint]
  simp

/-- Gate marker: the former unrestricted scalar defect is now exactly a
four-component geometric frame compatibility problem. -/
theorem regular_frame_palatini_canonical_divergence_reduction_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor
        point =
      canonicalMetricVolumeDivergence period hPeriod metric
          (regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric
            tensor) point +
        ∑ vector : Index4,
          regularFrameCanonicalDivergenceCompatibilityResidual period hPeriod
              metric vector point *
            regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor
              vector point :=
  regularFrameSmoothPalatiniCovariantDivergence_eq_canonical_add_frameResidual
    period hPeriod metric tensor point

end
end P0EFTJanusProgramPRegularFramePalatiniCanonicalDivergenceReduction4D
end JanusFormal
