import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D

/-!
# Coordinate-to-covariant scalar divergence
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D

set_option autoImplicit false
noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalInverseDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarRaisedGradientDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenDivergence4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- Raw partial derivative of a raised scalar gradient reconstructed from a
coordinate metric/scalar jet. -/
def coordinateRaisedScalarPartialDerivative
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (jet : CoordinateScalarJet2) (derivative upper : Index4) : Real :=
  ∑ lower : Index4,
    (connection.inverseMetricDerivative derivative upper lower * jet.gradient lower +
      connection.metric.metric⁻¹ upper lower * jet.partialGradient derivative lower)

/-- Coordinate covariant derivative of the raised scalar gradient. -/
def coordinateRaisedScalarCovariantDerivative
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (jet : CoordinateScalarJet2) (derivative upper : Index4) : Real :=
  coordinateRaisedScalarPartialDerivative connection jet derivative upper +
    ∑ lower : Index4,
      connection.christoffel upper derivative lower *
        covariantScalarJetRaisedGradient connection.metric
          (coordinateScalarJetNormalForm connection jet) lower

private theorem firstChristoffelCorrection_reindex
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (jet : CoordinateScalarJet2) (derivative upper : Index4) :
    (∑ lower : Index4,
        connection.christoffel upper derivative lower *
          (∑ index : Index4,
            connection.metric.metric⁻¹ lower index * jet.gradient index)) =
      ∑ index : Index4,
        (∑ lower : Index4,
          connection.christoffel upper derivative lower *
            connection.metric.metric⁻¹ lower index) * jet.gradient index := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro lower _
  ring

private theorem secondChristoffelCorrection_reindex
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (jet : CoordinateScalarJet2) (derivative upper : Index4) :
    (∑ index : Index4,
        (∑ lower : Index4,
          connection.christoffel index derivative lower *
            connection.metric.metric⁻¹ upper lower) * jet.gradient index) =
      ∑ lower : Index4,
        connection.metric.metric⁻¹ upper lower *
          (∑ index : Index4,
            connection.christoffel index derivative lower * jet.gradient index) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro lower _
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- Metric compatibility converts the raw coordinate law into the covariant
Hessian contraction, component by component. -/
theorem coordinateRaisedScalarCovariantDerivative_eq_hessian
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (jet : CoordinateScalarJet2) (derivative upper : Index4) :
    coordinateRaisedScalarCovariantDerivative connection jet derivative upper =
      ∑ lower : Index4,
        connection.metric.metric⁻¹ upper lower *
          coordinateCovariantHessian connection jet derivative lower := by
  have hCompatibility :
      (∑ index : Index4,
          (connection.inverseMetricDerivative derivative upper index +
              (∑ lower : Index4,
                connection.christoffel upper derivative lower *
                  connection.metric.metric⁻¹ lower index) +
            ∑ lower : Index4,
              connection.christoffel index derivative lower *
                connection.metric.metric⁻¹ upper lower) * jet.gradient index) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    rw [connection.inverseMetricCompatible derivative upper index]
    ring
  unfold coordinateRaisedScalarCovariantDerivative
    coordinateRaisedScalarPartialDerivative covariantScalarJetRaisedGradient
    coordinateScalarJetNormalForm Matrix.mulVec dotProduct
  rw [firstChristoffelCorrection_reindex]
  unfold coordinateCovariantHessian
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← secondChristoffelCorrection_reindex]
  simp_rw [add_mul, Finset.sum_add_distrib] at hCompatibility ⊢
  linear_combination hCompatibility

variable (period : Real) (hPeriod : period ≠ 0)

/-- Genuine local coordinate divergence of the raised scalar gradient. -/
def localActualScalarRaisedGradientDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ derivative : Index4,
    (fderiv Real
        (fun current =>
          localActualScalarRaisedGradient period hPeriod metric patch field
            current derivative)
        coordinate (Pi.single derivative 1) +
      ∑ lower : Index4,
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
            derivative derivative lower *
          localActualScalarRaisedGradient period hPeriod metric patch field
            coordinate lower)

theorem localActualScalarRaisedGradientCovariantDerivative_eq_coordinate
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (coordinate : Vector4) (derivative upper : Index4) :
    fderiv Real
        (fun current =>
          localActualScalarRaisedGradient period hPeriod metric patch field current upper)
        coordinate (Pi.single derivative 1) +
        (∑ lower : Index4,
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
              upper derivative lower *
            localActualScalarRaisedGradient period hPeriod metric patch field
              coordinate lower) =
      coordinateRaisedScalarCovariantDerivative
        (localLeviCivitaConnectionJet period hPeriod metric patch coordinate)
        (localCoordinateScalarJet period hPeriod field patch coordinate)
        derivative upper := by
  unfold coordinateRaisedScalarCovariantDerivative
    coordinateRaisedScalarPartialDerivative
  apply congrArg₂ (fun left right : Real => left + right)
  · rw [localActualScalarRaisedGradient_fderiv_basis]
    apply Finset.sum_congr rfl
    intro lower _
    rw [localActualInverseMetricDerivative_apply]
    change _ = _ * _ +
      (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ upper lower * _
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  · apply Finset.sum_congr rfl
    intro lower _
    rw [localActualScalarRaisedGradient_eq_localSmooth]
    rfl

/-- The genuine coordinate divergence of the raised gradient is the local
covariant wave operator. -/
theorem localActualScalarRaisedGradientDivergence_eq_wave
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    localActualScalarRaisedGradientDivergence period hPeriod metric patch field coordinate =
      covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch field coordinate) := by
  unfold localActualScalarRaisedGradientDivergence covariantScalarJetWave
    localCovariantScalarJet coordinateScalarJetNormalForm
  calc
    _ = ∑ derivative : Index4,
        coordinateRaisedScalarCovariantDerivative
          (localLeviCivitaConnectionJet period hPeriod metric patch coordinate)
          (localCoordinateScalarJet period hPeriod field patch coordinate)
          derivative derivative := by
      apply Finset.sum_congr rfl
      intro derivative _
      exact localActualScalarRaisedGradientCovariantDerivative_eq_coordinate
        period hPeriod metric patch field coordinate derivative derivative
    _ = _ := by
      apply Finset.sum_congr rfl
      intro derivative _
      exact coordinateRaisedScalarCovariantDerivative_eq_hessian
        (localLeviCivitaConnectionJet period hPeriod metric patch coordinate)
        (localCoordinateScalarJet period hPeriod field patch coordinate)
        derivative derivative

private theorem localGreenCrossTerms_commute
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    (∑ derivative : Index4,
        localScalarGradient period hPeriod field patch coordinate derivative *
          localActualScalarRaisedGradient period hPeriod metric patch test coordinate
            derivative) =
      ∑ derivative : Index4,
        localScalarGradient period hPeriod test patch coordinate derivative *
          localActualScalarRaisedGradient period hPeriod metric patch field coordinate
            derivative := by
  unfold localActualScalarRaisedGradient
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro first _
  have hSymmetric := congrArg
    (fun matrix : P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4 =>
      matrix second first)
    (localFixedSignMetric period hPeriod metric patch coordinate).inverse_symmetric
  simp only [Matrix.transpose_apply, localFixedSignMetric,
    Matrix.nonsing_inv_eq_ringInverse] at hSymmetric
  rw [hSymmetric]
  ring

/-- The genuine coordinate divergence of the genuine Green current equals the
antisymmetrized local wave pairing. -/
theorem localActualScalarGreenCoordinateDivergence_eq_waveDifference
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    localActualScalarGreenCoordinateDivergence period hPeriod metric patch field test
        coordinate =
      localScalarRepresentative period hPeriod field patch coordinate *
          covariantScalarJetWave
            (localFixedSignMetric period hPeriod metric patch coordinate)
            (localCovariantScalarJet period hPeriod metric patch test coordinate) -
        localScalarRepresentative period hPeriod test patch coordinate *
          covariantScalarJetWave
            (localFixedSignMetric period hPeriod metric patch coordinate)
            (localCovariantScalarJet period hPeriod metric patch field coordinate) := by
  rw [← localActualScalarRaisedGradientDivergence_eq_wave
      period hPeriod metric patch test coordinate,
    ← localActualScalarRaisedGradientDivergence_eq_wave
      period hPeriod metric patch field coordinate]
  unfold localActualScalarGreenCoordinateDivergence
    localActualScalarRaisedGradientDivergence
  simp_rw [localActualScalarGreenCurrent_fderiv_basis_leibniz]
  unfold localActualScalarGreenCurrent
  simp_rw [mul_sub]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [localGreenCrossTerms_commute period hPeriod metric patch field test coordinate]
  have hFactor (scalar : Real) (value : Index4 → Real) :
      (∑ index : Index4, scalar * value index) =
        scalar * ∑ index : Index4, value index := by
    rw [Finset.mul_sum]
  have hDoubleFactor (scalar : Real) (value : Index4 → Index4 → Real) :
      (∑ first : Index4, ∑ second : Index4,
          scalar * value first second) =
        scalar * ∑ first : Index4, ∑ second : Index4,
          value first second := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.mul_sum]
  have hCorrectionCommute (scalar : Real) (currentField : SmoothScalarField period hPeriod) :
      (∑ derivative : Index4, ∑ lower : Index4,
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
                derivative derivative lower *
            (scalar * localActualScalarRaisedGradient period hPeriod metric patch currentField
              coordinate lower)) =
        ∑ derivative : Index4, ∑ lower : Index4,
          scalar * localLeviCivitaChristoffel period hPeriod metric patch coordinate
                derivative derivative lower *
            localActualScalarRaisedGradient period hPeriod metric patch currentField
              coordinate lower := by
    apply Finset.sum_congr rfl
    intro derivative _
    apply Finset.sum_congr rfl
    intro lower _
    ring
  have hCorrectionFactor (scalar : Real) (currentField : SmoothScalarField period hPeriod) :
      (∑ derivative : Index4, ∑ lower : Index4,
          scalar * localLeviCivitaChristoffel period hPeriod metric patch coordinate
                derivative derivative lower *
            localActualScalarRaisedGradient period hPeriod metric patch currentField
              coordinate lower) =
        scalar * ∑ derivative : Index4, ∑ lower : Index4,
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
                derivative derivative lower *
            localActualScalarRaisedGradient period hPeriod metric patch currentField
              coordinate lower := by
    calc
      _ = ∑ derivative : Index4, ∑ lower : Index4,
          scalar *
            (localLeviCivitaChristoffel period hPeriod metric patch coordinate
                derivative derivative lower *
              localActualScalarRaisedGradient period hPeriod metric patch currentField
                coordinate lower) := by
          apply Finset.sum_congr rfl
          intro derivative _
          apply Finset.sum_congr rfl
          intro lower _
          ring
      _ = _ := hDoubleFactor scalar (fun derivative lower =>
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
            derivative derivative lower *
          localActualScalarRaisedGradient period hPeriod metric patch currentField
            coordinate lower)
  rw [hCorrectionCommute
      (localScalarRepresentative period hPeriod field patch coordinate) test,
    hCorrectionCommute
      (localScalarRepresentative period hPeriod test patch coordinate) field]
  rw [hFactor (localScalarRepresentative period hPeriod field patch coordinate)
      (fun derivative =>
        fderiv Real
          (fun current =>
            localActualScalarRaisedGradient period hPeriod metric patch test
              current derivative)
          coordinate (Pi.single derivative 1)),
    hFactor (localScalarRepresentative period hPeriod test patch coordinate)
      (fun derivative =>
        fderiv Real
          (fun current =>
            localActualScalarRaisedGradient period hPeriod metric patch field
              current derivative)
          coordinate (Pi.single derivative 1)),
    hCorrectionFactor
      (localScalarRepresentative period hPeriod field patch coordinate) test,
    hCorrectionFactor
      (localScalarRepresentative period hPeriod test patch coordinate) field]
  ring

/-- The raw coordinate divergence is exactly the already tensorial jet
divergence; hence the earlier Green identity is now an actual derivative law. -/
theorem localActualScalarGreenCoordinateDivergence_eq_localSmooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    localActualScalarGreenCoordinateDivergence period hPeriod metric patch field test
        coordinate =
      localSmoothScalarGreenDivergence period hPeriod metric patch field test coordinate := by
  rw [localActualScalarGreenCoordinateDivergence_eq_waveDifference,
    localSmoothScalarGreenDivergence_eq_waveDifference]

end
end P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D
end JanusFormal
