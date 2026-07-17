import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusScalarStressCoordinateConnectionJet4D

/-!
# Local Levi--Civita realization of the scalar-stress connection jet

This gate realizes the pointwise coordinate-connection interface from a
symmetric nondegenerate metric and a metric first jet.  It is finite-index
algebra only: no global connection or smoothness statement is made.
-/

namespace JanusFormal
namespace P0EFTJanusScalarStressLeviCivitaConnectionJet4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4
abbrev MetricDerivative4 := Index4 → Index4 → Index4 → Real

def metricDerivativeMatrix
    (dMetric : MetricDerivative4) (derivative : Index4) : Matrix4 :=
  fun first second => dMetric derivative first second

/-- The local Levi--Civita formula
`Γ^ρ_{μν} = 1/2 g^{ρσ}(∂μg_{νσ}+∂νg_{μσ}-∂σg_{μν})`. -/
def leviCivitaChristoffel
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (upper first second : Index4) : Real :=
  ∑ contracted : Index4,
    metric.metric⁻¹ upper contracted *
      ((1 / 2 : Real) *
        (dMetric first second contracted +
          dMetric second first contracted -
          dMetric contracted first second))

theorem leviCivitaChristoffel_eq_formula
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (upper first second : Index4) :
    leviCivitaChristoffel metric dMetric upper first second =
      (1 / 2 : Real) * ∑ contracted : Index4,
        metric.metric⁻¹ upper contracted *
          (dMetric first second contracted +
            dMetric second first contracted -
            dMetric contracted first second) := by
  rw [leviCivitaChristoffel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro contracted _
  ring

/-- Exact differentiated-inverse formula `∂g⁻¹ = -g⁻¹(∂g)g⁻¹`. -/
def leviCivitaInverseMetricDerivative
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (derivative first second : Index4) : Real :=
  (-(metric.metric⁻¹ * metricDerivativeMatrix dMetric derivative *
      metric.metric⁻¹)) first second

theorem leviCivitaInverseMetricDerivative_eq_sum
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (derivative first second : Index4) :
    leviCivitaInverseMetricDerivative metric dMetric derivative first second =
      -∑ right : Index4, ∑ left : Index4,
        metric.metric⁻¹ first left * dMetric derivative left right *
          metric.metric⁻¹ right second := by
  simp [leviCivitaInverseMetricDerivative, metricDerivativeMatrix,
    Matrix.mul_apply, Finset.sum_mul]

theorem metric_entry_symmetric
    (metric : FixedSignMetric4) (first second : Index4) :
    metric.metric first second = metric.metric second first := by
  have hEntry := congrFun (congrFun metric.metric_symmetric first) second
  simpa [Matrix.transpose_apply] using hEntry.symm

theorem inverseMetric_entry_symmetric
    (metric : FixedSignMetric4) (first second : Index4) :
    metric.metric⁻¹ first second = metric.metric⁻¹ second first := by
  have hEntry := congrFun (congrFun metric.inverse_symmetric first) second
  simpa [Matrix.transpose_apply] using hEntry.symm

/-- Raising and then lowering a covector with the supplied inverse is exact. -/
theorem inverseMetric_contract_metric
    (metric : FixedSignMetric4) (covector : Vector4) (second : Index4) :
    (∑ upper : Index4,
        (∑ lower : Index4,
          metric.metric⁻¹ upper lower * covector lower) *
          metric.metric upper second) = covector second := by
  have hDet : IsUnit (Matrix.det metric.metric) :=
    (Matrix.isUnit_iff_isUnit_det _).mp metric.metric_isUnit
  have hProduct := Matrix.nonsing_inv_mul metric.metric hDet
  calc
    (∑ upper : Index4,
        (∑ lower : Index4,
          metric.metric⁻¹ upper lower * covector lower) *
          metric.metric upper second) =
        ∑ lower : Index4, covector lower *
          (∑ upper : Index4,
            metric.metric⁻¹ lower upper * metric.metric upper second) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro lower _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro upper _
      rw [inverseMetric_entry_symmetric metric upper lower]
      ring
    _ = ∑ lower : Index4,
        covector lower * (1 : Matrix4) lower second := by
      apply Finset.sum_congr rfl
      intro lower _
      have hEntry := congrArg (fun matrix : Matrix4 => matrix lower second)
        hProduct
      rw [show (∑ upper : Index4,
          metric.metric⁻¹ lower upper * metric.metric upper second) =
          (1 : Matrix4) lower second by
        simpa [Matrix.mul_apply] using hEntry]
    _ = covector second := by
      simp only [Matrix.one_apply]
      simp

theorem leviCivitaChristoffel_torsionFree
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (hMetricDerivative : ∀ derivative first second,
      dMetric derivative first second = dMetric derivative second first)
    (upper first second : Index4) :
    leviCivitaChristoffel metric dMetric upper first second =
      leviCivitaChristoffel metric dMetric upper second first := by
  unfold leviCivitaChristoffel
  apply Finset.sum_congr rfl
  intro contracted _
  rw [hMetricDerivative contracted first second]
  ring

theorem leviCivitaChristoffel_contract_metric
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (derivative first second : Index4) :
    (∑ upper : Index4,
        leviCivitaChristoffel metric dMetric upper derivative first *
          metric.metric upper second) =
      (1 / 2 : Real) *
        (dMetric derivative first second +
          dMetric first derivative second -
          dMetric second derivative first) := by
  simpa [leviCivitaChristoffel] using
    inverseMetric_contract_metric metric
      (fun contracted =>
        (1 / 2 : Real) *
          (dMetric derivative first contracted +
            dMetric first derivative contracted -
            dMetric contracted derivative first))
      second

theorem leviCivitaChristoffel_metricCompatible
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (hMetricDerivative : ∀ derivative first second,
      dMetric derivative first second = dMetric derivative second first)
    (derivative first second : Index4) :
    dMetric derivative first second =
      (∑ upper : Index4,
        leviCivitaChristoffel metric dMetric upper derivative first *
          metric.metric upper second) +
      ∑ upper : Index4,
        leviCivitaChristoffel metric dMetric upper derivative second *
          metric.metric first upper := by
  rw [leviCivitaChristoffel_contract_metric]
  have hSecond :
      (∑ upper : Index4,
        leviCivitaChristoffel metric dMetric upper derivative second *
          metric.metric first upper) =
        (1 / 2 : Real) *
          (dMetric derivative second first +
            dMetric second derivative first -
            dMetric first derivative second) := by
    calc
      (∑ upper : Index4,
        leviCivitaChristoffel metric dMetric upper derivative second *
          metric.metric first upper) =
          ∑ upper : Index4,
            leviCivitaChristoffel metric dMetric upper derivative second *
              metric.metric upper first := by
        apply Finset.sum_congr rfl
        intro upper _
        rw [metric_entry_symmetric metric first upper]
      _ = _ := leviCivitaChristoffel_contract_metric metric dMetric
        derivative second first
  rw [hSecond, hMetricDerivative derivative second first]
  ring

def leviCivitaConnectionMatrix
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (derivative : Index4) : Matrix4 :=
  fun lower upper => leviCivitaChristoffel metric dMetric upper derivative lower

theorem metricDerivativeMatrix_eq_connection
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (hMetricDerivative : ∀ derivative first second,
      dMetric derivative first second = dMetric derivative second first)
    (derivative : Index4) :
    metricDerivativeMatrix dMetric derivative =
      leviCivitaConnectionMatrix metric dMetric derivative * metric.metric +
        metric.metric *
          (leviCivitaConnectionMatrix metric dMetric derivative).transpose := by
  ext first second
  simpa [metricDerivativeMatrix, leviCivitaConnectionMatrix,
    Matrix.mul_apply, Matrix.transpose_apply, mul_comm] using
    leviCivitaChristoffel_metricCompatible metric dMetric hMetricDerivative
      derivative first second

theorem leviCivitaInverseMetric_matrixCompatible
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (hMetricDerivative : ∀ derivative first second,
      dMetric derivative first second = dMetric derivative second first)
    (derivative : Index4) :
    -(metric.metric⁻¹ * metricDerivativeMatrix dMetric derivative *
        metric.metric⁻¹) +
        (leviCivitaConnectionMatrix metric dMetric derivative).transpose *
          metric.metric⁻¹ +
      metric.metric⁻¹ * leviCivitaConnectionMatrix metric dMetric derivative =
      0 := by
  have hDet : IsUnit (Matrix.det metric.metric) :=
    (Matrix.isUnit_iff_isUnit_det _).mp metric.metric_isUnit
  have hLeft := Matrix.nonsing_inv_mul metric.metric hDet
  have hRight := Matrix.mul_nonsing_inv metric.metric hDet
  rw [metricDerivativeMatrix_eq_connection metric dMetric hMetricDerivative]
  have hCore :
      metric.metric⁻¹ *
          (leviCivitaConnectionMatrix metric dMetric derivative * metric.metric +
            metric.metric *
              (leviCivitaConnectionMatrix metric dMetric derivative).transpose) *
          metric.metric⁻¹ =
        metric.metric⁻¹ * leviCivitaConnectionMatrix metric dMetric derivative +
          (leviCivitaConnectionMatrix metric dMetric derivative).transpose *
            metric.metric⁻¹ := by
    calc
      _ = (metric.metric⁻¹ *
              leviCivitaConnectionMatrix metric dMetric derivative) *
            (metric.metric * metric.metric⁻¹) +
          (metric.metric⁻¹ * metric.metric) *
            ((leviCivitaConnectionMatrix metric dMetric derivative).transpose *
              metric.metric⁻¹) := by noncomm_ring
      _ = _ := by rw [hLeft, hRight]; simp
  rw [hCore]
  abel

theorem leviCivitaInverseMetric_compatible
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (hMetricDerivative : ∀ derivative first second,
      dMetric derivative first second = dMetric derivative second first)
    (derivative first second : Index4) :
    leviCivitaInverseMetricDerivative metric dMetric derivative first second +
        (∑ lower : Index4,
          leviCivitaChristoffel metric dMetric first derivative lower *
            metric.metric⁻¹ lower second) +
      (∑ lower : Index4,
        leviCivitaChristoffel metric dMetric second derivative lower *
          metric.metric⁻¹ first lower) = 0 := by
  have hMatrix := leviCivitaInverseMetric_matrixCompatible metric dMetric
    hMetricDerivative derivative
  have hEntry := congrArg (fun matrix : Matrix4 => matrix first second) hMatrix
  simpa [leviCivitaInverseMetricDerivative, leviCivitaConnectionMatrix,
    Matrix.mul_apply, Matrix.transpose_apply, mul_comm] using hEntry

/-- The complete pointwise coordinate connection jet realized by the local
Levi--Civita formulas. -/
def leviCivitaConnectionJet
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (hMetricDerivative : ∀ derivative first second,
      dMetric derivative first second = dMetric derivative second first) :
    MetricCompatibleTorsionFreeConnectionJet4 where
  metric := metric
  christoffel := leviCivitaChristoffel metric dMetric
  metricDerivative := dMetric
  inverseMetricDerivative :=
    leviCivitaInverseMetricDerivative metric dMetric
  metricDerivative_symmetric := hMetricDerivative
  torsionFree :=
    leviCivitaChristoffel_torsionFree metric dMetric hMetricDerivative
  metricCompatible :=
    leviCivitaChristoffel_metricCompatible metric dMetric hMetricDerivative
  inverseMetricCompatible :=
    leviCivitaInverseMetric_compatible metric dMetric hMetricDerivative

/-- Canonical coordinate stress-derivative realization for the local
Levi--Civita connection jet. -/
def leviCivitaCoordinateStressDerivativeRealization
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (hMetricDerivative : ∀ derivative first second,
      dMetric derivative first second = dMetric derivative second first)
    (potentialValue potentialSlope : Real) (jet : CoordinateScalarJet2) :
    CoordinateStressDerivativeRealization
      (leviCivitaConnectionJet metric dMetric hMetricDerivative)
      potentialValue potentialSlope jet :=
  canonicalCoordinateStressDerivativeRealization
    (leviCivitaConnectionJet metric dMetric hMetricDerivative)
      potentialValue potentialSlope jet

/-- Pointwise local stress conservation for the realized Levi--Civita jet. -/
theorem leviCivitaCoordinateStressDivergence_eq_zero_of_euler
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (hMetricDerivative : ∀ derivative first second,
      dMetric derivative first second = dMetric derivative second first)
    (potentialValue potentialSlope : Real) (jet : CoordinateScalarJet2)
    (hEuler : covariantScalarStressEulerResidual metric potentialSlope
      (coordinateScalarJetNormalForm
        (leviCivitaConnectionJet metric dMetric hMetricDerivative) jet) = 0) :
    coordinateCovariantStressDivergence
      (leviCivitaCoordinateStressDerivativeRealization metric dMetric
        hMetricDerivative potentialValue potentialSlope jet) = 0 := by
  exact coordinateCovariantStressDivergence_eq_zero_of_euler
    (leviCivitaCoordinateStressDerivativeRealization metric dMetric
      hMetricDerivative potentialValue potentialSlope jet) hEuler

end

end P0EFTJanusScalarStressLeviCivitaConnectionJet4D
end JanusFormal
