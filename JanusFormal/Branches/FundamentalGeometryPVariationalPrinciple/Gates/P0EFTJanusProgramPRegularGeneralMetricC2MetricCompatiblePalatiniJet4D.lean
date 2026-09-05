import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameAnholonomicPalatiniDivergence4D

/-! # Metric-compatible Palatini jet for the genuine C² metric chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2MetricCompatiblePalatiniJet4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2RicciConnectionVelocity4D
open P0EFTJanusProgramPRegularFrameAnholonomicPalatini4D
open P0EFTJanusProgramPRegularGeneralMetricC2TorsionFreePalatiniJet4D
open P0EFTJanusProgramPRegularFrameAnholonomicPalatiniDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4
private abbrev Matrix4 := Matrix Index4 Index4 Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Component form of base Levi--Civita metric compatibility in the global
regular frame. -/
theorem regularGeneralMetricC0MetricFirstDerivative_zero_metricCompatible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (derivative first second : Index4) :
    regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
        derivative first second point =
      (∑ upper : Index4,
        regularGeneralMetricC0Christoffel period hPeriod metric 0
            upper derivative first point *
          regularFrameMetricMatrix period hPeriod metric upper second point) +
      ∑ upper : Index4,
        regularGeneralMetricC0Christoffel period hPeriod metric 0
            upper derivative second point *
          regularFrameMetricMatrix period hPeriod metric first upper point := by
  rcases canonicalTotalHolonomicAtlasCover_covers period hPeriod point with
    ⟨patch, _hPatch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let firstConnection := regularFrameLocalCovariantDerivativeVector
    period hPeriod metric patch derivative first coordinate
  let secondConnection := regularFrameLocalCovariantDerivativeVector
    period hPeriod metric patch derivative second coordinate
  have hFirstPairing :
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          firstConnection
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate) =
        ∑ upper : Index4,
          regularGeneralMetricC0Christoffel period hPeriod metric 0
              upper derivative first (patch.coordinateMap coordinate) *
            regularFrameMetricMatrix period hPeriod metric upper second
              (patch.coordinateMap coordinate) := by
    calc
      _ = localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          (∑ upper : Index4, basis.repr firstConnection upper • basis upper)
          (pulledRegularFrameVector period hPeriod metric patch second
            coordinate) := by rw [basis.sum_repr]
      _ = ∑ upper : Index4,
          basis.repr firstConnection upper *
            regularFrameMetricMatrix period hPeriod metric upper second
              (patch.coordinateMap coordinate) := by
        rw [map_sum, LinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro upper _
        rw [map_smul]
        simp only [LinearMap.smul_apply, smul_eq_mul]
        rw [show basis upper = pulledRegularFrameVector period hPeriod metric
            patch upper coordinate by
          exact pulledRegularFrameBasis_apply period hPeriod metric patch
            coordinate upper]
        rw [localMetricCoordinateForm_pulledRegularFrameVector]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro upper _
        rw [regularGeneralMetricC0Christoffel_zero_apply period hPeriod metric
          patch coordinate upper derivative first]
  have hSecondPairing :
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          (pulledRegularFrameVector period hPeriod metric patch first coordinate)
          secondConnection =
        ∑ upper : Index4,
          regularGeneralMetricC0Christoffel period hPeriod metric 0
              upper derivative second (patch.coordinateMap coordinate) *
            regularFrameMetricMatrix period hPeriod metric first upper
              (patch.coordinateMap coordinate) := by
    calc
      _ = localMetricCoordinateForm period hPeriod metric.metric patch coordinate
          (pulledRegularFrameVector period hPeriod metric patch first coordinate)
          (∑ upper : Index4, basis.repr secondConnection upper • basis upper) := by
            rw [basis.sum_repr]
      _ = ∑ upper : Index4,
          basis.repr secondConnection upper *
            regularFrameMetricMatrix period hPeriod metric first upper
              (patch.coordinateMap coordinate) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro upper _
        rw [map_smul]
        simp only [smul_eq_mul]
        rw [show basis upper = pulledRegularFrameVector period hPeriod metric
            patch upper coordinate by
          exact pulledRegularFrameBasis_apply period hPeriod metric patch
            coordinate upper]
        rw [localMetricCoordinateForm_pulledRegularFrameVector]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro upper _
        rw [regularGeneralMetricC0Christoffel_zero_apply period hPeriod metric
          patch coordinate upper derivative second]
  rw [regularGeneralMetricC0MetricFirstDerivative_zero_apply]
  rw [regularFrameLocalCovariantDerivative_metricCompatible period hPeriod
    metric patch coordinate derivative first second]
  change
    localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        firstConnection
        (pulledRegularFrameVector period hPeriod metric patch second coordinate) +
      localMetricCoordinateForm period hPeriod metric.metric patch coordinate
        (pulledRegularFrameVector period hPeriod metric patch first coordinate)
        secondConnection = _
  rw [hFirstPairing, hSecondPairing]

/-- The stored inverse-metric frame derivative is metric compatible with the
reconstructed base connection. -/
theorem regularGeneralMetricC0InverseMetricDerivative_zero_metricCompatible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (derivative first second : Index4) :
    regularGeneralMetricC0InverseMetricDerivative period hPeriod metric 0
          derivative first second point +
        (∑ auxiliary : Index4,
          regularGeneralMetricC0Christoffel period hPeriod metric 0
              first derivative auxiliary point *
            regularFrameMetricInverseMatrixMap period hPeriod metric point
              auxiliary second) +
        ∑ auxiliary : Index4,
          regularGeneralMetricC0Christoffel period hPeriod metric 0
              second derivative auxiliary point *
            regularFrameMetricInverseMatrixMap period hPeriod metric point
              first auxiliary = 0 := by
  let base : Matrix4 := regularFrameMetricMatrixMap period hPeriod metric point
  let inverse : Matrix4 :=
    regularFrameMetricInverseMatrixMap period hPeriod metric point
  let connection : Matrix4 := fun upper lower =>
    regularGeneralMetricC0Christoffel period hPeriod metric 0
      upper derivative lower point
  let metricDerivative : Matrix4 := fun row column =>
    regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
      derivative row column point
  let inverseDerivative : Matrix4 := fun row column =>
    regularGeneralMetricC0InverseMetricDerivative period hPeriod metric 0
      derivative row column point
  have hMetricDerivative :
      metricDerivative = connection.transpose * base + base * connection := by
    ext row column
    simp only [metricDerivative, connection, base, Matrix.add_apply,
      Matrix.mul_apply, Matrix.transpose_apply]
    rw [regularGeneralMetricC0MetricFirstDerivative_zero_metricCompatible
      period hPeriod metric point derivative row column]
    simp only [regularFrameMetricMatrixMap]
    congr 1
    apply Finset.sum_congr rfl
    intro upper _
    ring
  have hInverseDerivative :
      inverseDerivative = -(inverse * metricDerivative * inverse) := by
    ext row column
    simp only [inverseDerivative,
      regularGeneralMetricC0InverseMetricDerivative,
      regularGeneralMetricC0InverseMetricCoefficient_zero_apply,
      regularGeneralMetricC0MetricFirstDerivative_zero_apply,
      regularFrameMetricInverseMatrix, inverse, metricDerivative,
      Matrix.neg_apply, Matrix.mul_apply,
      ContinuousMap.neg_apply, ContinuousMap.sum_apply,
      ContinuousMap.mul_apply]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hLeft : inverse * base = 1 := by
    exact Matrix.nonsing_inv_mul base
      (isUnit_iff_ne_zero.mpr
        (regularFrameMetricMatrix_det_ne_zero period hPeriod metric point))
  have hRight : base * inverse = 1 := by
    exact Matrix.mul_nonsing_inv base
      (isUnit_iff_ne_zero.mpr
        (regularFrameMetricMatrix_det_ne_zero period hPeriod metric point))
  have hMatrix :
      inverseDerivative + connection * inverse +
          inverse * connection.transpose = 0 := by
    rw [hInverseDerivative, hMetricDerivative]
    calc
      -(inverse * (connection.transpose * base + base * connection) * inverse) +
            connection * inverse + inverse * connection.transpose =
          -(inverse * connection.transpose * (base * inverse) +
              (inverse * base) * connection * inverse) +
            connection * inverse + inverse * connection.transpose := by
              noncomm_ring
      _ = -(inverse * connection.transpose + connection * inverse) +
            connection * inverse + inverse * connection.transpose := by
              rw [hRight, hLeft, mul_one, one_mul]
      _ = 0 := by abel
  have hEntry := congrFun (congrFun hMatrix first) second
  simp only [inverseDerivative, connection, inverse, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at hEntry
  calc
    _ = regularGeneralMetricC0InverseMetricDerivative period hPeriod metric 0
          derivative first second point +
        (∑ auxiliary : Index4,
          regularGeneralMetricC0Christoffel period hPeriod metric 0
              first derivative auxiliary point *
            regularFrameMetricInverseMatrixMap period hPeriod metric point
              auxiliary second) +
        ∑ auxiliary : Index4,
          regularFrameMetricInverseMatrixMap period hPeriod metric point
              first auxiliary *
            regularGeneralMetricC0Christoffel period hPeriod metric 0
              second derivative auxiliary point := by
          congr 1
          apply Finset.sum_congr rfl
          intro auxiliary _
          ring
    _ = 0 := hEntry

/-- The actual inverse matrix at the chart center is the regular-frame
nonsingular inverse. -/
theorem regularGeneralMetricC0InverseMetricMatrixAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0InverseMetricMatrixAt period hPeriod metric 0 point =
      regularFrameMetricInverseMatrixMap period hPeriod metric point := by
  ext row column
  exact regularGeneralMetricC0InverseMetricCoefficient_zero_apply
    period hPeriod metric row column point

/-- The fully concrete metric-compatible Palatini jet at a quotient point. -/
def regularGeneralMetricC2MetricCompatiblePalatiniJetAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    MetricCompatibleRegularFramePalatiniJet4 where
  toTorsionFreeRegularFrameConnectionVariationJet4 :=
    regularGeneralMetricC2TorsionFreeConnectionVariationJetAt
      period hPeriod metric direction point
  inverse := regularFrameMetricInverseMatrixMap period hPeriod metric point
  frameInverseDerivative := fun derivative first second =>
    regularGeneralMetricC0InverseMetricDerivative period hPeriod metric 0
      derivative first second point
  inverse_symmetric := by
    intro first second
    change (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹
        first second =
      (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹
        second first
    have hMetric :
        (regularFrameMetricMatrixMap period hPeriod metric point).transpose =
          regularFrameMetricMatrixMap period hPeriod metric point := by
      ext row column
      exact metric.metric.tensor.symmetric point _ _
    have hInverse := Matrix.transpose_nonsing_inv
      (A := regularFrameMetricMatrixMap period hPeriod metric point)
    rw [hMetric] at hInverse
    exact congrFun (congrFun hInverse second) first
  inverse_metric_compatible := by
    intro derivative first second
    exact regularGeneralMetricC0InverseMetricDerivative_zero_metricCompatible
      period hPeriod metric point derivative first second

/-- The Palatini scalar in the exact EH density is the covariant divergence
of the concrete regular-frame Palatini vector. -/
theorem regularGeneralMetricC0PalatiniScalarVelocity_eq_covariantDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    palatiniScalarVelocity
        (regularGeneralMetricC0InverseMetricMatrixAt
          period hPeriod metric 0 point)
        (regularGeneralMetricC0RicciVelocityAt
          period hPeriod metric direction point) =
      regularFramePalatiniVectorCovariantDivergence
        (regularGeneralMetricC2MetricCompatiblePalatiniJetAt
          period hPeriod metric direction point) := by
  rw [regularGeneralMetricC0InverseMetricMatrixAt_zero]
  unfold palatiniScalarVelocity tensorPairing
  simp_rw [regularGeneralMetricC0RicciVelocityAt_eq_palatini]
  change regularFrameContractedPalatiniDerivative
      (regularGeneralMetricC2MetricCompatiblePalatiniJetAt
        period hPeriod metric direction point) = _
  exact regularFrameContractedPalatiniDerivative_eq_covariantDivergence _

/-- Gate marker for the concrete metric-compatible C² Palatini jet. -/
theorem regular_general_metric_c2_metric_compatible_palatini_jet_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    palatiniScalarVelocity
        (regularGeneralMetricC0InverseMetricMatrixAt
          period hPeriod metric 0 point)
        (regularGeneralMetricC0RicciVelocityAt
          period hPeriod metric direction point) =
      regularFramePalatiniVectorCovariantDivergence
        (regularGeneralMetricC2MetricCompatiblePalatiniJetAt
          period hPeriod metric direction point) :=
  regularGeneralMetricC0PalatiniScalarVelocity_eq_covariantDivergence
    period hPeriod metric direction point

end
end P0EFTJanusProgramPRegularGeneralMetricC2MetricCompatiblePalatiniJet4D
end JanusFormal
