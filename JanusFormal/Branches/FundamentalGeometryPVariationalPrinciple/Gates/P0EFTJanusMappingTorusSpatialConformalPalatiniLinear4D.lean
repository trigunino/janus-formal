import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSpatialConformalCurvatureJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D

/-!
# Linear Palatini part of the spatial conformal Ricci correction

This gate separates the terms linear in the conformal Christoffel correction
from its quadratic contribution to the local Ricci transformation.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSpatialConformalPalatiniLinear4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarRaisedGradientDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalInverseDerivative4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusMappingTorusSpatialConformalMetricJet4D
open P0EFTJanusMappingTorusSpatialConformalCurvatureJet4D
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusScalarStressLeviCivitaConnectionJet4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev Index4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4

private def coordinateBasisVector (index : Index4) : Vector4 :=
  Pi.single index 1

/-- Local logarithmic conformal potential `log(q) / 2`. -/
def localConformalLogPotential
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  (1 / 2 : Real) *
    Real.log (localScalarRepresentative period hPeriod scale patch coordinate)

/-- Coordinate derivative of the conformal logarithmic one-form. -/
def localConformalLogGradientDerivative
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative index : Index4) : Real :=
  fderiv Real
      (fun current =>
        localConformalLogGradient period hPeriod scale patch current index)
      coordinate (coordinateBasisVector derivative)

/-- Coordinate derivative of the raised conformal logarithmic gradient. -/
def localConformalRaisedLogGradientDerivative
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative upper : Index4) : Real :=
  fderiv Real
      (fun current =>
        localConformalRaisedLogGradient
          period hPeriod scale patch current upper)
      coordinate (coordinateBasisVector derivative)

/-- Coordinate divergence of the raised logarithmic gradient. -/
def localConformalRaisedLogGradientDivergence
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ derivative : Index4,
    (localConformalRaisedLogGradientDerivative
        period hPeriod scale patch coordinate derivative derivative +
      ∑ auxiliary : Index4,
        localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate derivative derivative auxiliary *
          localConformalRaisedLogGradient
            period hPeriod scale patch coordinate auxiliary)

/-- Intrinsic covariant derivative of the conformal logarithmic one-form. -/
def localConformalLogGradientCovariantDerivative
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative index : Index4) : Real :=
  localConformalLogGradientDerivative
      period hPeriod scale patch coordinate derivative index -
    ∑ auxiliary : Index4,
      localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate auxiliary derivative index *
        localConformalLogGradient period hPeriod scale patch coordinate auxiliary

theorem localConformalLogPotential_contDiff
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localConformalLogPotential period hPeriod scale patch) := by
  unfold localConformalLogPotential
  exact contDiff_const.mul
    ((localScalarRepresentative_contDiff period hPeriod scale patch).log
      (fun coordinate =>
        ne_of_gt (hScale (patch.coordinateMap coordinate))))

theorem localConformalLogGradient_contDiff
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (index : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localConformalLogGradient period hPeriod scale patch coordinate index) := by
  unfold localConformalLogGradient
  have hDenominator :
      ContDiff Real ∞ (fun coordinate =>
        2 * localScalarRepresentative period hPeriod scale patch coordinate) :=
    contDiff_const.mul
      (localScalarRepresentative_contDiff period hPeriod scale patch)
  have hDenominatorNe : ∀ coordinate : Vector4,
      2 * localScalarRepresentative period hPeriod scale patch coordinate ≠ 0 := by
    intro coordinate
    exact mul_ne_zero (by norm_num)
      (ne_of_gt (hScale (patch.coordinateMap coordinate)))
  exact
    (contDiff_const.div hDenominator hDenominatorNe).mul
      (localScalarGradient_component_contDiff
        period hPeriod scale patch index)

theorem localConformalRaisedLogGradient_contDiff
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (upper : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localConformalRaisedLogGradient
        period hPeriod scale patch coordinate upper) := by
  rw [show
    (fun coordinate =>
      localConformalRaisedLogGradient
        period hPeriod scale patch coordinate upper) =
      fun coordinate =>
        (1 / (2 * localScalarRepresentative
          period hPeriod scale patch coordinate)) *
          localSmoothScalarRaisedGradient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale coordinate upper by
    funext coordinate
    exact localConformalRaisedLogGradient_eq
      period hPeriod scale patch coordinate upper]
  have hDenominator :
      ContDiff Real ∞ (fun coordinate =>
        2 * localScalarRepresentative period hPeriod scale patch coordinate) :=
    contDiff_const.mul
      (localScalarRepresentative_contDiff period hPeriod scale patch)
  have hDenominatorNe : ∀ coordinate : Vector4,
      2 * localScalarRepresentative period hPeriod scale patch coordinate ≠ 0 := by
    intro coordinate
    exact mul_ne_zero (by norm_num)
      (ne_of_gt (hScale (patch.coordinateMap coordinate)))
  exact
    (contDiff_const.div hDenominator hDenominatorNe).mul
      (localSmoothScalarRaisedGradient_component_contDiff
        period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch scale upper)

private theorem localConformalLogFactor_fderiv_basis
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative : Index4) :
    fderiv Real
        (fun current =>
          1 / (2 * localScalarRepresentative
            period hPeriod scale patch current))
        coordinate (coordinateBasisVector derivative) =
      -2 *
        (1 / (2 * localScalarRepresentative
          period hPeriod scale patch coordinate)) ^ 2 *
        localScalarGradient period hPeriod scale patch coordinate derivative := by
  have hRepresentative :
      DifferentiableAt Real
        (localScalarRepresentative period hPeriod scale patch) coordinate :=
    ((localScalarRepresentative_contDiff period hPeriod scale patch).differentiable
      (by simp)).differentiableAt
  have hRepresentativeNe :
      localScalarRepresentative period hPeriod scale patch coordinate ≠ 0 :=
    ne_of_gt (hScale (patch.coordinateMap coordinate))
  have hInverse :=
    (hasFDerivAt_inv hRepresentativeNe).comp
      coordinate hRepresentative.hasFDerivAt
  have hHalfInverse := hInverse.const_mul (1 / 2 : Real)
  have hFunction :
      (fun current =>
        1 / (2 * localScalarRepresentative
          period hPeriod scale patch current)) =
        fun current =>
          (1 / 2 : Real) *
            (localScalarRepresentative
              period hPeriod scale patch current)⁻¹ := by
    funext current
    field_simp [ne_of_gt (hScale (patch.coordinateMap current))]
  rw [hFunction]
  have hApply := congrArg
    (fun map => map (coordinateBasisVector derivative)) hHalfInverse.fderiv
  have hApply' :
      (fderiv Real
          (fun current =>
            (1 / 2 : Real) *
              (localScalarRepresentative
                period hPeriod scale patch current)⁻¹)
          coordinate) (coordinateBasisVector derivative) =
        ((1 / 2 : Real) •
          (ContinuousLinearMap.toSpanSingleton Real
              (-(localScalarRepresentative
                period hPeriod scale patch coordinate ^ 2)⁻¹)).comp
            (fderiv Real
              (localScalarRepresentative period hPeriod scale patch)
              coordinate)) (coordinateBasisVector derivative) := by
    simpa only [Function.comp_apply] using hApply
  rw [hApply']
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  rw [show
    (fderiv Real (localScalarRepresentative period hPeriod scale patch) coordinate)
        (coordinateBasisVector derivative) =
      localScalarGradient period hPeriod scale patch coordinate derivative by
    rfl]
  field_simp

theorem localConformalLogGradientDerivative_normal_form
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative index : Index4) :
    localConformalLogGradientDerivative
        period hPeriod scale patch coordinate derivative index =
      (1 / (2 * localScalarRepresentative
          period hPeriod scale patch coordinate)) *
        localScalarPartialGradient
          period hPeriod scale patch coordinate derivative index -
      2 *
        (1 / (2 * localScalarRepresentative
          period hPeriod scale patch coordinate)) ^ 2 *
        localScalarGradient period hPeriod scale patch coordinate derivative *
        localScalarGradient period hPeriod scale patch coordinate index := by
  have hFactor :
      DifferentiableAt Real
        (fun current =>
          1 / (2 * localScalarRepresentative
            period hPeriod scale patch current)) coordinate := by
    have hRepresentative :
        DifferentiableAt Real
          (localScalarRepresentative period hPeriod scale patch) coordinate :=
      ((localScalarRepresentative_contDiff
        period hPeriod scale patch).differentiable
          (by simp)).differentiableAt
    have hFunction :
        (fun current =>
          1 / (2 * localScalarRepresentative
            period hPeriod scale patch current)) =
          fun current =>
            (1 / 2 : Real) *
              (localScalarRepresentative
                period hPeriod scale patch current)⁻¹ := by
      funext current
      field_simp [ne_of_gt (hScale (patch.coordinateMap current))]
    rw [hFunction]
    exact (hRepresentative.inv
      (ne_of_gt (hScale (patch.coordinateMap coordinate)))).const_mul _
  have hGradient :
      DifferentiableAt Real
        (fun current =>
          localScalarGradient period hPeriod scale patch current index)
        coordinate :=
    ((localScalarGradient_component_contDiff
      period hPeriod scale patch index).differentiable
        (by simp)).differentiableAt
  unfold localConformalLogGradientDerivative localConformalLogGradient
  rw [show
    (fun current =>
      1 / (2 * localScalarRepresentative
          period hPeriod scale patch current) *
        localScalarGradient period hPeriod scale patch current index) =
      (fun current =>
        1 / (2 * localScalarRepresentative
          period hPeriod scale patch current)) *
      (fun current =>
        localScalarGradient period hPeriod scale patch current index) by
    rfl]
  rw [fderiv_mul hFactor hGradient]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [localConformalLogFactor_fderiv_basis
    period hPeriod scale hScale patch coordinate derivative]
  have hGradientDerivative :
      fderiv Real
          (fun current =>
            localScalarGradient period hPeriod scale patch current index)
          coordinate (coordinateBasisVector derivative) =
        localScalarPartialGradient
          period hPeriod scale patch coordinate derivative index := by
    change
      fderiv Real
          (fun current =>
            localScalarGradient period hPeriod scale patch current index)
          coordinate (Pi.single derivative 1) =
        localScalarPartialGradient
          period hPeriod scale patch coordinate derivative index
    exact localScalarGradient_fderiv_basis
      period hPeriod scale patch coordinate derivative index
  rw [hGradientDerivative]
  ring

theorem localConformalRaisedLogGradientDerivative_normal_form
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative upper : Index4) :
    localConformalRaisedLogGradientDerivative
        period hPeriod scale patch coordinate derivative upper =
      -2 *
          (1 / (2 * localScalarRepresentative
            period hPeriod scale patch coordinate)) ^ 2 *
          localScalarGradient
            period hPeriod scale patch coordinate derivative *
          localActualScalarRaisedGradient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale coordinate upper +
        (1 / (2 * localScalarRepresentative
          period hPeriod scale patch coordinate)) *
          fderiv Real
            (fun current =>
              localActualScalarRaisedGradient period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch scale current upper)
            coordinate (coordinateBasisVector derivative) := by
  have hFactor :
      DifferentiableAt Real
        (fun current =>
          1 / (2 * localScalarRepresentative
            period hPeriod scale patch current)) coordinate := by
    have hRepresentative :
        DifferentiableAt Real
          (localScalarRepresentative period hPeriod scale patch) coordinate :=
      ((localScalarRepresentative_contDiff
        period hPeriod scale patch).differentiable
          (by simp)).differentiableAt
    have hFunction :
        (fun current =>
          1 / (2 * localScalarRepresentative
            period hPeriod scale patch current)) =
          fun current =>
            (1 / 2 : Real) *
              (localScalarRepresentative
                period hPeriod scale patch current)⁻¹ := by
      funext current
      field_simp [ne_of_gt (hScale (patch.coordinateMap current))]
    rw [hFunction]
    exact (hRepresentative.inv
      (ne_of_gt (hScale (patch.coordinateMap coordinate)))).const_mul _
  have hRaised :
      DifferentiableAt Real
        (fun current =>
          localActualScalarRaisedGradient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale current upper) coordinate := by
    rw [show
      (fun current =>
        localActualScalarRaisedGradient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch scale current upper) =
        fun current =>
          localSmoothScalarRaisedGradient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale current upper by
      funext current
      exact localActualScalarRaisedGradient_eq_localSmooth
        period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch scale current upper]
    exact
      ((localSmoothScalarRaisedGradient_component_contDiff
        period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch scale upper).differentiable (by simp)).differentiableAt
  have hFunction :
      (fun current =>
        localConformalRaisedLogGradient
          period hPeriod scale patch current upper) =
        fun current =>
          (1 / (2 * localScalarRepresentative
            period hPeriod scale patch current)) *
            localActualScalarRaisedGradient period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch scale current upper := by
    funext current
    rw [localConformalRaisedLogGradient_eq,
      localActualScalarRaisedGradient_eq_localSmooth]
  unfold localConformalRaisedLogGradientDerivative
  rw [hFunction]
  rw [show
    (fun current =>
      1 / (2 * localScalarRepresentative
          period hPeriod scale patch current) *
        localActualScalarRaisedGradient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch scale current upper) =
      (fun current =>
        1 / (2 * localScalarRepresentative
          period hPeriod scale patch current)) *
      (fun current =>
        localActualScalarRaisedGradient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch scale current upper) by
    rfl]
  rw [fderiv_mul hFactor hRaised]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [localConformalLogFactor_fderiv_basis
    period hPeriod scale hScale patch coordinate derivative]
  ring

theorem localConformalRaisedLogGradientDivergence_normal_form
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localConformalRaisedLogGradientDivergence
        period hPeriod scale patch coordinate =
      (1 / (2 * localScalarRepresentative
          period hPeriod scale patch coordinate)) *
        covariantScalarJetWave
          (localFixedSignMetric period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale coordinate) -
      2 *
          (1 / (2 * localScalarRepresentative
            period hPeriod scale patch coordinate)) ^ 2 *
        covariantScalarGradientPairing
          (localFixedSignMetric period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale coordinate) := by
  let factor :=
    1 / (2 * localScalarRepresentative
      period hPeriod scale patch coordinate)
  let metric :=
    intrinsicSmoothGeneralLorentzMetric period hPeriod
  have hConnection (derivative : Index4) :
      (∑ auxiliary : Index4,
        localLeviCivitaChristoffel period hPeriod metric
            patch coordinate derivative derivative auxiliary *
          (factor *
            localActualScalarRaisedGradient period hPeriod metric
              patch scale coordinate auxiliary)) =
        factor * ∑ auxiliary : Index4,
          localLeviCivitaChristoffel period hPeriod metric
              patch coordinate derivative derivative auxiliary *
            localActualScalarRaisedGradient period hPeriod metric
              patch scale coordinate auxiliary := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro auxiliary _
    ring
  have hDerivativeFactor :
      (∑ derivative : Index4,
        factor *
          fderiv Real
            (fun current =>
              localActualScalarRaisedGradient period hPeriod metric
                patch scale current derivative)
            coordinate (coordinateBasisVector derivative)) =
        factor * ∑ derivative : Index4,
          fderiv Real
            (fun current =>
              localActualScalarRaisedGradient period hPeriod metric
                patch scale current derivative)
            coordinate (coordinateBasisVector derivative) := by
    rw [Finset.mul_sum]
  have hConnectionFactor :
      (∑ derivative : Index4,
        factor *
          (∑ auxiliary : Index4,
            localLeviCivitaChristoffel period hPeriod metric
                patch coordinate derivative derivative auxiliary *
              localActualScalarRaisedGradient period hPeriod metric
                patch scale coordinate auxiliary)) =
        factor * ∑ derivative : Index4, ∑ auxiliary : Index4,
          localLeviCivitaChristoffel period hPeriod metric
              patch coordinate derivative derivative auxiliary *
            localActualScalarRaisedGradient period hPeriod metric
              patch scale coordinate auxiliary := by
    rw [Finset.mul_sum]
  have hGradientFactor :
      (∑ derivative : Index4,
        -2 * factor ^ 2 *
          localScalarGradient
              period hPeriod scale patch coordinate derivative *
            localActualScalarRaisedGradient period hPeriod metric
              patch scale coordinate derivative) =
        -2 * factor ^ 2 *
          (∑ derivative : Index4,
            localScalarGradient
                period hPeriod scale patch coordinate derivative *
              localActualScalarRaisedGradient period hPeriod metric
                patch scale coordinate derivative) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro derivative _
    ring
  unfold localConformalRaisedLogGradientDivergence
  simp_rw [localConformalRaisedLogGradientDerivative_normal_form
    period hPeriod scale hScale patch coordinate]
  simp_rw [localConformalRaisedLogGradient_eq,
    ← localActualScalarRaisedGradient_eq_localSmooth]
  change
    (∑ derivative : Index4,
      (-2 * factor ^ 2 *
            localScalarGradient
              period hPeriod scale patch coordinate derivative *
            localActualScalarRaisedGradient period hPeriod metric
              patch scale coordinate derivative +
          factor *
            fderiv Real
              (fun current =>
                localActualScalarRaisedGradient period hPeriod metric
                  patch scale current derivative)
              coordinate (coordinateBasisVector derivative) +
        ∑ auxiliary : Index4,
          localLeviCivitaChristoffel period hPeriod metric
              patch coordinate derivative derivative auxiliary *
            (factor *
              localActualScalarRaisedGradient period hPeriod metric
                patch scale coordinate auxiliary))) = _
  simp_rw [hConnection]
  calc
    _ = factor *
          localActualScalarRaisedGradientDivergence
            period hPeriod metric patch scale coordinate -
        2 * factor ^ 2 *
          (∑ derivative : Index4,
            localScalarGradient
                period hPeriod scale patch coordinate derivative *
              localActualScalarRaisedGradient period hPeriod metric
                patch scale coordinate derivative) := by
      unfold localActualScalarRaisedGradientDivergence
      unfold coordinateBasisVector
      unfold coordinateBasisVector at hDerivativeFactor
      simp only [Finset.sum_add_distrib]
      rw [hDerivativeFactor, hConnectionFactor, hGradientFactor]
      ring
    _ = factor *
          covariantScalarJetWave
            (localFixedSignMetric period hPeriod metric patch coordinate)
            (localCovariantScalarJet period hPeriod metric
              patch scale coordinate) -
        2 * factor ^ 2 *
          (∑ derivative : Index4,
            localScalarGradient
                period hPeriod scale patch coordinate derivative *
              localActualScalarRaisedGradient period hPeriod metric
                patch scale coordinate derivative) := by
      rw [localActualScalarRaisedGradientDivergence_eq_wave]
    _ = _ := by
      simp_rw [localActualScalarRaisedGradient_eq_localSmooth]
      rw [localScalarGradient_dot_raised_eq_pairing]

theorem localConformalLogPotential_fderiv_basis
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (index : Index4) :
    fderiv Real
        (localConformalLogPotential period hPeriod scale patch)
        coordinate (coordinateBasisVector index) =
      localConformalLogGradient period hPeriod scale patch coordinate index := by
  have hRepresentative :
      DifferentiableAt Real
        (localScalarRepresentative period hPeriod scale patch) coordinate :=
    ((localScalarRepresentative_contDiff period hPeriod scale patch).differentiable
      (by simp)).differentiableAt
  have hRepresentativeNe :
      localScalarRepresentative period hPeriod scale patch coordinate ≠ 0 :=
    ne_of_gt (hScale (patch.coordinateMap coordinate))
  have hLog :
      DifferentiableAt Real
        (fun current =>
          Real.log
            (localScalarRepresentative period hPeriod scale patch current))
        coordinate :=
    hRepresentative.log hRepresentativeNe
  unfold localConformalLogPotential localConformalLogGradient
  rw [fderiv_const_mul hLog (1 / 2 : Real)]
  rw [fderiv.log hRepresentative hRepresentativeNe]
  simp only [smul_apply, smul_eq_mul]
  rw [show
    (fderiv Real (localScalarRepresentative period hPeriod scale patch) coordinate)
        (coordinateBasisVector index) =
      localScalarGradient period hPeriod scale patch coordinate index by
    rfl]
  field_simp

theorem localConformalLogGradientDerivative_symmetric
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) :
    localConformalLogGradientDerivative
        period hPeriod scale patch coordinate first second =
      localConformalLogGradientDerivative
        period hPeriod scale patch coordinate second first := by
  unfold localConformalLogGradientDerivative
  rw [show
    (fun current =>
      localConformalLogGradient period hPeriod scale patch current second) =
      fun current =>
        fderiv Real
          (localConformalLogPotential period hPeriod scale patch)
          current (coordinateBasisVector second) by
    funext current
    exact (localConformalLogPotential_fderiv_basis
      period hPeriod scale hScale patch current second).symm]
  rw [show
    (fun current =>
      localConformalLogGradient period hPeriod scale patch current first) =
      fun current =>
        fderiv Real
          (localConformalLogPotential period hPeriod scale patch)
          current (coordinateBasisVector first) by
    funext current
    exact (localConformalLogPotential_fderiv_basis
      period hPeriod scale hScale patch current first).symm]
  have hPotentialDerivative :
      DifferentiableAt Real
        (fderiv Real
          (localConformalLogPotential period hPeriod scale patch)) coordinate :=
    (((localConformalLogPotential_contDiff
      period hPeriod scale hScale patch).fderiv_right
        (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hEvaluation (direction applied : Index4) :
      fderiv Real
          (fun current =>
            fderiv Real
              (localConformalLogPotential period hPeriod scale patch)
              current (coordinateBasisVector applied))
          coordinate (coordinateBasisVector direction) =
        fderiv Real
            (fderiv Real
              (localConformalLogPotential period hPeriod scale patch))
            coordinate (coordinateBasisVector direction)
              (coordinateBasisVector applied) := by
    have hDirection : DifferentiableAt Real
        (fun _ : Vector4 => coordinateBasisVector applied) coordinate :=
      differentiableAt_const (c := coordinateBasisVector applied)
    have hProduct := fderiv_clm_apply hPotentialDerivative hDirection
    have hApply := congrArg
      (fun map => map (coordinateBasisVector direction)) hProduct
    simpa using hApply
  rw [hEvaluation first second, hEvaluation second first]
  have hSmooth : minSmoothness Real 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hSymmetric :
      IsSymmSndFDerivAt Real
        (localConformalLogPotential period hPeriod scale patch) coordinate :=
    ContDiffAt.isSymmSndFDerivAt
      (localConformalLogPotential_contDiff
        period hPeriod scale hScale patch).contDiffAt
      hSmooth
  exact hSymmetric
    (coordinateBasisVector first) (coordinateBasisVector second)

theorem localConformalChristoffelCorrectionDerivative_trace
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative second : Index4) :
    (∑ contracted : Index4,
      localConformalChristoffelCorrectionDerivative
        period hPeriod scale patch coordinate
        derivative contracted contracted second) =
      4 * localConformalLogGradientDerivative
        period hPeriod scale patch coordinate derivative second := by
  have hCorrection (contracted : Index4) :
      DifferentiableAt Real
        (fun current =>
          localConformalChristoffelCorrection
            period hPeriod scale patch current contracted contracted second)
        coordinate :=
    ((localConformalChristoffelCorrection_contDiff
      period hPeriod scale hScale patch contracted contracted second).differentiable
        (by simp)).differentiableAt
  have hSum := fderiv_fun_sum (u := Finset.univ)
    (fun contracted _ => hCorrection contracted)
  have hApply := congrArg
    (fun map => map (coordinateBasisVector derivative)) hSum
  have hTrace :
      (fun current =>
        ∑ contracted : Index4,
          localConformalChristoffelCorrection
            period hPeriod scale patch current contracted contracted second) =
        fun current =>
          4 * localConformalLogGradient
            period hPeriod scale patch current second := by
    funext current
    exact localConformalChristoffelCorrection_trace
      period hPeriod scale patch current second
  have hLog :
      DifferentiableAt Real
        (fun current =>
          localConformalLogGradient period hPeriod scale patch current second)
        coordinate :=
    ((localConformalLogGradient_contDiff
      period hPeriod scale hScale patch second).differentiable
        (by simp)).differentiableAt
  change
    (∑ contracted : Index4,
      fderiv Real
          (fun current =>
            localConformalChristoffelCorrection
              period hPeriod scale patch current contracted contracted second)
          coordinate (Pi.single derivative 1)) =
      4 * fderiv Real
          (fun current =>
            localConformalLogGradient period hPeriod scale patch current second)
          coordinate (Pi.single derivative 1)
  calc
    _ = fderiv Real
        (fun current =>
          ∑ contracted : Index4,
            localConformalChristoffelCorrection
              period hPeriod scale patch current contracted contracted second)
        coordinate (Pi.single derivative 1) := by
      simpa only [coordinateBasisVector, sum_apply,
        Finset.sum_apply] using hApply.symm
    _ = fderiv Real
        (fun current =>
          4 * localConformalLogGradient
            period hPeriod scale patch current second)
        coordinate (Pi.single derivative 1) := by rw [hTrace]
    _ = _ := by
      rw [fderiv_const_mul hLog 4]
      simp only [smul_apply, smul_eq_mul]

theorem localConformalChristoffelCorrection_inverse_trace_derivative
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative upper : Index4) :
    (∑ first : Index4, ∑ second : Index4,
      (localActualInverseMetricDerivative period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate derivative first second *
          localConformalChristoffelCorrection
            period hPeriod scale patch coordinate upper second first +
        (localMetricMatrix period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate)⁻¹ first second *
          localConformalChristoffelCorrectionDerivative
            period hPeriod scale patch coordinate
            derivative upper second first)) =
      -2 * localConformalRaisedLogGradientDerivative
        period hPeriod scale patch coordinate derivative upper := by
  have hInverse (first second : Index4) :
      DifferentiableAt Real
        (fun current =>
          (localMetricMatrix period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch current)⁻¹ first second) coordinate :=
    ((localMetricInverseEntry_contDiff period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch first second).differentiable (by simp)).differentiableAt
  have hCorrection (first second : Index4) :
      DifferentiableAt Real
        (fun current =>
          localConformalChristoffelCorrection
            period hPeriod scale patch current upper second first) coordinate :=
    ((localConformalChristoffelCorrection_contDiff
      period hPeriod scale hScale patch upper second first).differentiable
        (by simp)).differentiableAt
  have hInverseBasis (first second : Index4) :
      fderiv Real
          (fun current =>
            (localMetricMatrix period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch current)⁻¹ first second)
          coordinate (coordinateBasisVector derivative) =
        localActualInverseMetricDerivative period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate derivative first second := by
    rw [show
      (fun current =>
        (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch current)⁻¹ first second) =
        fun current =>
          Ring.inverse
            (localMetricMatrix period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch current) first second by
      funext current
      exact congrArg (fun matrix => matrix first second)
        (Matrix.nonsing_inv_eq_ringInverse
          (A := localMetricMatrix period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch current))]
    change
      fderiv Real
          (fun current =>
            Ring.inverse
              (localMetricMatrix period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch current) first second)
          coordinate (Pi.single derivative 1) =
        localActualInverseMetricDerivative period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate derivative first second
    exact localMetricInverseEntry_fderiv_basis
      period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch coordinate derivative first second
  have hCorrectionBasis (first second : Index4) :
      fderiv Real
          (fun current =>
            localConformalChristoffelCorrection
              period hPeriod scale patch current upper second first)
          coordinate (coordinateBasisVector derivative) =
        localConformalChristoffelCorrectionDerivative
          period hPeriod scale patch coordinate
          derivative upper second first := by
    rfl
  have hTerm (first second : Index4) :=
    (hInverse first second).hasFDerivAt.mul
      (hCorrection first second).hasFDerivAt
  have hDoubleSum :=
    HasFDerivAt.fun_sum (u := Finset.univ) fun first _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) fun second _ =>
        hTerm first second
  have hApply := congrArg
    (fun map => map (coordinateBasisVector derivative)) hDoubleSum.fderiv
  have hProductDerivative :
      fderiv Real
          (fun current =>
            ∑ first : Index4, ∑ second : Index4,
              (localMetricMatrix period hPeriod
                  (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                  patch current)⁻¹ first second *
                localConformalChristoffelCorrection
                  period hPeriod scale patch current upper second first)
          coordinate (coordinateBasisVector derivative) =
        ∑ first : Index4, ∑ second : Index4,
          (localActualInverseMetricDerivative period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch coordinate derivative first second *
              localConformalChristoffelCorrection
                period hPeriod scale patch coordinate upper second first +
            (localMetricMatrix period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch coordinate)⁻¹ first second *
              localConformalChristoffelCorrectionDerivative
                period hPeriod scale patch coordinate
                derivative upper second first) := by
    simp only [Pi.mul_apply, sum_apply, add_apply, smul_apply, smul_eq_mul,
      hInverseBasis, hCorrectionBasis] at hApply
    calc
      _ = ∑ first : Index4, ∑ second : Index4,
          ((localMetricMatrix period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch coordinate)⁻¹ first second *
              localConformalChristoffelCorrectionDerivative
                period hPeriod scale patch coordinate
                derivative upper second first +
            localConformalChristoffelCorrection
                period hPeriod scale patch coordinate upper second first *
              localActualInverseMetricDerivative period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch coordinate derivative first second) := hApply
      _ = _ := by
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro second _
        ring
  have hTrace :
      (fun current =>
        ∑ first : Index4, ∑ second : Index4,
          (localMetricMatrix period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch current)⁻¹ first second *
            localConformalChristoffelCorrection
              period hPeriod scale patch current upper second first) =
        fun current =>
          -2 * localConformalRaisedLogGradient
            period hPeriod scale patch current upper := by
    funext current
    exact localConformalChristoffelCorrection_inverse_trace
      period hPeriod scale patch current upper
  have hRaised :
      DifferentiableAt Real
        (fun current =>
          localConformalRaisedLogGradient
            period hPeriod scale patch current upper) coordinate :=
    ((localConformalRaisedLogGradient_contDiff
      period hPeriod scale hScale patch upper).differentiable
        (by simp)).differentiableAt
  calc
    _ = fderiv Real
        (fun current =>
          ∑ first : Index4, ∑ second : Index4,
            (localMetricMatrix period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch current)⁻¹ first second *
              localConformalChristoffelCorrection
                period hPeriod scale patch current upper second first)
        coordinate (coordinateBasisVector derivative) :=
      hProductDerivative.symm
    _ = fderiv Real
        (fun current =>
          -2 * localConformalRaisedLogGradient
            period hPeriod scale patch current upper)
        coordinate (coordinateBasisVector derivative) := by rw [hTrace]
    _ = _ := by
      rw [fderiv_const_mul hRaised (-2)]
      simp only [smul_apply, smul_eq_mul]
      rfl

/-- Intrinsic covariant derivative of the conformal connection difference. -/
def localConformalChristoffelCorrectionCovariantDerivative
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative upper first second : Index4) : Real :=
  localConformalChristoffelCorrectionDerivative
      period hPeriod scale patch coordinate derivative upper first second +
    ∑ auxiliary : Index4,
      (localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate upper derivative auxiliary *
        localConformalChristoffelCorrection
          period hPeriod scale patch coordinate auxiliary first second -
        localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate auxiliary derivative first *
        localConformalChristoffelCorrection
          period hPeriod scale patch coordinate upper auxiliary second -
        localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate auxiliary derivative second *
        localConformalChristoffelCorrection
          period hPeriod scale patch coordinate upper first auxiliary)

private theorem doubleSum_swap
    (term : Index4 → Index4 → Real) :
    (∑ first : Index4, ∑ second : Index4, term first second) =
      ∑ first : Index4, ∑ second : Index4, term second first := by
  rw [Finset.sum_comm]

private theorem tripleSum_swap_first_third
    (term : Index4 → Index4 → Index4 → Real) :
    (∑ first : Index4, ∑ second : Index4, ∑ third : Index4,
      term first second third) =
      ∑ first : Index4, ∑ second : Index4, ∑ third : Index4,
        term third second first := by
  calc
    _ = ∑ first : Index4, ∑ third : Index4, ∑ second : Index4,
        term first second third := by
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.sum_comm]
    _ = ∑ third : Index4, ∑ first : Index4, ∑ second : Index4,
        term first second third := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro third _
      rw [Finset.sum_comm]

private theorem contractedCovariantCorrection_eq
    (connection inverse inverseDerivative : Index4 → Index4 → Real)
    (correction : Index4 → Index4 → Index4 → Real)
    (partialCorrection : Index4 → Index4 → Real)
    (raised : Index4 → Real)
    (raisedDerivative : Real)
    (upper : Index4)
    (hCompatibility : ∀ first second,
      inverseDerivative first second +
          (∑ auxiliary : Index4,
            connection first auxiliary * inverse auxiliary second) +
        (∑ auxiliary : Index4,
          connection second auxiliary * inverse first auxiliary) = 0)
    (hTrace : ∀ currentUpper,
      (∑ first : Index4, ∑ second : Index4,
        inverse first second * correction currentUpper second first) =
        -2 * raised currentUpper)
    (hDerivative :
      (∑ first : Index4, ∑ second : Index4,
        (inverseDerivative first second *
            correction upper second first +
          inverse first second * partialCorrection second first)) =
        -2 * raisedDerivative) :
    (∑ first : Index4, ∑ second : Index4,
      inverse first second *
        (partialCorrection second first +
          ∑ auxiliary : Index4,
            (connection upper auxiliary * correction auxiliary second first -
              connection auxiliary second * correction upper auxiliary first -
              connection auxiliary first * correction upper second auxiliary))) =
      -2 *
        (raisedDerivative +
          ∑ auxiliary : Index4,
            connection upper auxiliary * raised auxiliary) := by
  have hCompatibilityContracted :
      (∑ first : Index4, ∑ second : Index4,
        (inverseDerivative first second +
            (∑ auxiliary : Index4,
              connection first auxiliary * inverse auxiliary second) +
          (∑ auxiliary : Index4,
            connection second auxiliary * inverse first auxiliary)) *
          correction upper second first) = 0 := by
    apply Finset.sum_eq_zero
    intro first _
    apply Finset.sum_eq_zero
    intro second _
    rw [hCompatibility first second]
    ring
  have hFirstReindex :
      (∑ first : Index4, ∑ second : Index4,
        (∑ auxiliary : Index4,
          connection first auxiliary * inverse auxiliary second) *
            correction upper second first) =
        ∑ first : Index4, ∑ second : Index4,
          inverse first second *
            (∑ auxiliary : Index4,
              connection auxiliary first * correction upper second auxiliary) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [tripleSum_swap_first_third]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    apply Finset.sum_congr rfl
    intro auxiliary _
    ring
  have hSecondReindex :
      (∑ first : Index4, ∑ second : Index4,
        (∑ auxiliary : Index4,
          connection second auxiliary * inverse first auxiliary) *
            correction upper second first) =
        ∑ first : Index4, ∑ second : Index4,
          inverse first second *
            (∑ auxiliary : Index4,
              connection auxiliary second * correction upper auxiliary first) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro second _
    apply Finset.sum_congr rfl
    intro auxiliary _
    ring
  have hUpperTrace :
      (∑ first : Index4, ∑ second : Index4,
        inverse first second *
          (∑ auxiliary : Index4,
            connection upper auxiliary * correction auxiliary second first)) =
        -2 * ∑ auxiliary : Index4,
          connection upper auxiliary * raised auxiliary := by
    calc
      _ = ∑ first : Index4, ∑ second : Index4, ∑ auxiliary : Index4,
          inverse first second *
            (connection upper auxiliary * correction auxiliary second first) := by
        simp_rw [Finset.mul_sum]
      _ = ∑ auxiliary : Index4, ∑ second : Index4, ∑ first : Index4,
          inverse first second *
            (connection upper auxiliary * correction auxiliary second first) := by
        rw [tripleSum_swap_first_third]
      _ = ∑ auxiliary : Index4,
          connection upper auxiliary *
            (∑ first : Index4, ∑ second : Index4,
              inverse first second * correction auxiliary second first) := by
        apply Finset.sum_congr rfl
        intro auxiliary _
        rw [Finset.sum_comm]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro first _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro second _
        ring
      _ = ∑ auxiliary : Index4,
          connection upper auxiliary * (-2 * raised auxiliary) := by
        apply Finset.sum_congr rfl
        intro auxiliary _
        rw [hTrace auxiliary]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro auxiliary _
        ring
  simp only [add_mul, Finset.sum_add_distrib] at hCompatibilityContracted
  rw [hFirstReindex, hSecondReindex] at hCompatibilityContracted
  simp only [Finset.mul_sum] at hCompatibilityContracted
  simp only [Finset.mul_sum] at hUpperTrace
  simp only [Finset.sum_add_distrib] at hDerivative
  simp only [mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]
  linear_combination hDerivative - hCompatibilityContracted + hUpperTrace

theorem localConformalChristoffelCorrectionCovariantDerivative_trace
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative second : Index4) :
    (∑ contracted : Index4,
      localConformalChristoffelCorrectionCovariantDerivative
        period hPeriod scale patch coordinate
        derivative contracted contracted second) =
      4 * localConformalLogGradientCovariantDerivative
        period hPeriod scale patch coordinate derivative second := by
  have hSwap :
      (∑ contracted : Index4, ∑ auxiliary : Index4,
        localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate contracted derivative auxiliary *
          localConformalChristoffelCorrection
            period hPeriod scale patch coordinate auxiliary contracted second) =
        ∑ contracted : Index4, ∑ auxiliary : Index4,
          localLeviCivitaChristoffel period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate auxiliary derivative contracted *
            localConformalChristoffelCorrection
              period hPeriod scale patch coordinate contracted auxiliary second :=
    doubleSum_swap
      (fun contracted auxiliary =>
        localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate contracted derivative auxiliary *
          localConformalChristoffelCorrection
            period hPeriod scale patch coordinate auxiliary contracted second)
  have hTraceConnection :
      (∑ contracted : Index4, ∑ auxiliary : Index4,
        localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate auxiliary derivative second *
          localConformalChristoffelCorrection
            period hPeriod scale patch coordinate contracted contracted auxiliary) =
        4 * ∑ auxiliary : Index4,
          localLeviCivitaChristoffel period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate auxiliary derivative second *
            localConformalLogGradient
              period hPeriod scale patch coordinate auxiliary := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ auxiliary : Index4,
          localLeviCivitaChristoffel period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate auxiliary derivative second *
            (∑ contracted : Index4,
              localConformalChristoffelCorrection
                period hPeriod scale patch coordinate
                contracted contracted auxiliary) := by
          apply Finset.sum_congr rfl
          intro auxiliary _
          rw [Finset.mul_sum]
      _ = ∑ auxiliary : Index4,
          localLeviCivitaChristoffel period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate auxiliary derivative second *
            (4 * localConformalLogGradient
              period hPeriod scale patch coordinate auxiliary) := by
          apply Finset.sum_congr rfl
          intro auxiliary _
          rw [localConformalChristoffelCorrection_trace]
      _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro auxiliary _
          ring
  unfold localConformalChristoffelCorrectionCovariantDerivative
    localConformalLogGradientCovariantDerivative
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [localConformalChristoffelCorrectionDerivative_trace
    period hPeriod scale hScale patch coordinate derivative second]
  rw [hSwap, hTraceConnection]
  ring

theorem localConformalChristoffelCorrectionCovariantDerivative_inverse_trace
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative upper : Index4) :
    (∑ first : Index4, ∑ second : Index4,
      (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ first second *
        localConformalChristoffelCorrectionCovariantDerivative
          period hPeriod scale patch coordinate
          derivative upper second first) =
      -2 *
        (localConformalRaisedLogGradientDerivative
            period hPeriod scale patch coordinate derivative upper +
          ∑ auxiliary : Index4,
            localLeviCivitaChristoffel period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch coordinate upper derivative auxiliary *
              localConformalRaisedLogGradient
                period hPeriod scale patch coordinate auxiliary) := by
  apply contractedCovariantCorrection_eq
    (connection := fun first auxiliary =>
      localLeviCivitaChristoffel period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate first derivative auxiliary)
    (inverse := fun first second =>
      (localMetricMatrix period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate)⁻¹ first second)
    (inverseDerivative := fun first second =>
      localActualInverseMetricDerivative period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate derivative first second)
    (correction := fun currentUpper first second =>
      localConformalChristoffelCorrection
        period hPeriod scale patch coordinate currentUpper first second)
    (partialCorrection := fun first second =>
      localConformalChristoffelCorrectionDerivative
        period hPeriod scale patch coordinate derivative upper first second)
    (raised := fun currentUpper =>
      localConformalRaisedLogGradient
        period hPeriod scale patch coordinate currentUpper)
    (raisedDerivative :=
      localConformalRaisedLogGradientDerivative
        period hPeriod scale patch coordinate derivative upper)
    (upper := upper)
  · intro first second
    rw [localActualInverseMetricDerivative_apply]
    exact
      (localLeviCivitaConnectionJet period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate).inverseMetricCompatible derivative first second
  · intro currentUpper
    exact localConformalChristoffelCorrection_inverse_trace
      period hPeriod scale patch coordinate currentUpper
  · exact localConformalChristoffelCorrection_inverse_trace_derivative
      period hPeriod scale hScale patch coordinate derivative upper

/-- Contracted Palatini operator `∇ C - ∇ tr C`. -/
def localConformalRicciPalatiniCovariant
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) : Real :=
  ∑ contracted : Index4,
    (localConformalChristoffelCorrectionCovariantDerivative
        period hPeriod scale patch coordinate
        contracted contracted second first -
      localConformalChristoffelCorrectionCovariantDerivative
        period hPeriod scale patch coordinate
        second contracted contracted first)

/-- Terms in the conformal Ricci correction that are linear in the
Christoffel correction. -/
def localConformalRicciPalatiniLinear
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) : Real :=
  ∑ contracted : Index4,
    (localConformalChristoffelCorrectionDerivative
        period hPeriod scale patch coordinate
        contracted contracted second first -
      localConformalChristoffelCorrectionDerivative
        period hPeriod scale patch coordinate
        second contracted contracted first +
      ∑ auxiliary : Index4,
        (localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate contracted contracted auxiliary *
          localConformalChristoffelCorrection
            period hPeriod scale patch coordinate auxiliary second first +
        localConformalChristoffelCorrection
            period hPeriod scale patch coordinate contracted contracted auxiliary *
          localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate auxiliary second first) -
      ∑ auxiliary : Index4,
        (localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate contracted second auxiliary *
          localConformalChristoffelCorrection
            period hPeriod scale patch coordinate auxiliary contracted first +
        localConformalChristoffelCorrection
            period hPeriod scale patch coordinate contracted second auxiliary *
          localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate auxiliary contracted first))

private theorem intrinsicChristoffel_lower_symmetric
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper first second : Index4) :
    localLeviCivitaChristoffel period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate upper first second =
      localLeviCivitaChristoffel period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate upper second first := by
  unfold localLeviCivitaChristoffel
  exact leviCivitaChristoffel_torsionFree
    (localFixedSignMetric period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)
    (localMetricDerivative period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)
    (localMetricDerivative_symmetric period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)
    upper first second

theorem localConformalLogGradientCovariantDerivative_symmetric
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) :
    localConformalLogGradientCovariantDerivative
        period hPeriod scale patch coordinate first second =
      localConformalLogGradientCovariantDerivative
        period hPeriod scale patch coordinate second first := by
  unfold localConformalLogGradientCovariantDerivative
  rw [localConformalLogGradientDerivative_symmetric
    period hPeriod scale hScale patch coordinate first second]
  congr 1
  apply Finset.sum_congr rfl
  intro auxiliary _
  rw [intrinsicChristoffel_lower_symmetric]

theorem localConformalRicciPalatiniLinear_eq_covariant
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) :
    localConformalRicciPalatiniLinear
        period hPeriod scale patch coordinate first second =
      localConformalRicciPalatiniCovariant
        period hPeriod scale patch coordinate first second := by
  unfold localConformalRicciPalatiniLinear
    localConformalRicciPalatiniCovariant
    localConformalChristoffelCorrectionCovariantDerivative
  apply Finset.sum_congr rfl
  intro contracted _
  have hCancel :
      (∑ auxiliary : Index4,
        localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate auxiliary contracted second *
          localConformalChristoffelCorrection
            period hPeriod scale patch coordinate contracted auxiliary first) =
        ∑ auxiliary : Index4,
          localLeviCivitaChristoffel period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate auxiliary second contracted *
            localConformalChristoffelCorrection
              period hPeriod scale patch coordinate contracted auxiliary first := by
    apply Finset.sum_congr rfl
    intro auxiliary _
    rw [intrinsicChristoffel_lower_symmetric]
  have hFirstComm :
      (∑ auxiliary : Index4,
        localConformalChristoffelCorrection
            period hPeriod scale patch coordinate contracted contracted auxiliary *
          localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate auxiliary second first) =
        ∑ auxiliary : Index4,
          localLeviCivitaChristoffel period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate auxiliary second first *
            localConformalChristoffelCorrection
              period hPeriod scale patch coordinate contracted contracted auxiliary := by
    apply Finset.sum_congr rfl
    intro auxiliary _
    ring
  have hSecondComm :
      (∑ auxiliary : Index4,
        localConformalChristoffelCorrection
            period hPeriod scale patch coordinate contracted second auxiliary *
          localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate auxiliary contracted first) =
        ∑ auxiliary : Index4,
          localLeviCivitaChristoffel period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate auxiliary contracted first *
            localConformalChristoffelCorrection
              period hPeriod scale patch coordinate contracted second auxiliary := by
    apply Finset.sum_congr rfl
    intro auxiliary _
    ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hCancel, hFirstComm, hSecondComm]
  ring

/-- Terms in the conformal Ricci correction quadratic in the Christoffel
correction. -/
def localConformalRicciQuadratic
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) : Real :=
  ∑ contracted : Index4,
    ((∑ auxiliary : Index4,
        localConformalChristoffelCorrection
            period hPeriod scale patch coordinate contracted contracted auxiliary *
          localConformalChristoffelCorrection
            period hPeriod scale patch coordinate auxiliary second first) -
      ∑ auxiliary : Index4,
        localConformalChristoffelCorrection
            period hPeriod scale patch coordinate contracted second auxiliary *
          localConformalChristoffelCorrection
            period hPeriod scale patch coordinate auxiliary contracted first)

theorem localConformalRicciCorrection_eq_palatiniLinear_add_quadratic
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) :
    localConformalRicciCorrection period hPeriod scale patch coordinate first second =
      localConformalRicciPalatiniLinear
          period hPeriod scale patch coordinate first second +
        localConformalRicciQuadratic
          period hPeriod scale patch coordinate first second := by
  unfold localConformalRicciCorrection localConformalRiemannCorrection
    localConformalRicciPalatiniLinear localConformalRicciQuadratic
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

theorem localConformalLogGradientCovariantDerivative_trace_normal_form
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (∑ first : Index4, ∑ second : Index4,
      (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ first second *
        localConformalLogGradientCovariantDerivative
          period hPeriod scale patch coordinate first second) =
      (1 / (2 * localScalarRepresentative
          period hPeriod scale patch coordinate)) *
        covariantScalarJetWave
          (localFixedSignMetric period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale coordinate) -
      2 *
          (1 / (2 * localScalarRepresentative
            period hPeriod scale patch coordinate)) ^ 2 *
        covariantScalarGradientPairing
          (localFixedSignMetric period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale coordinate) := by
  let factor :=
    1 / (2 * localScalarRepresentative
      period hPeriod scale patch coordinate)
  let metric :=
    intrinsicSmoothGeneralLorentzMetric period hPeriod
  have hConnection (first second : Index4) :
      (∑ auxiliary : Index4,
        localLeviCivitaChristoffel period hPeriod metric
            patch coordinate auxiliary first second *
          (factor *
            localScalarGradient
              period hPeriod scale patch coordinate auxiliary)) =
        factor * ∑ auxiliary : Index4,
          localLeviCivitaChristoffel period hPeriod metric
              patch coordinate auxiliary first second *
            localScalarGradient
              period hPeriod scale patch coordinate auxiliary := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro auxiliary _
    ring
  unfold localConformalLogGradientCovariantDerivative
  simp_rw [localConformalLogGradientDerivative_normal_form
    period hPeriod scale hScale patch coordinate]
  unfold localConformalLogGradient
  change
    (∑ first : Index4, ∑ second : Index4,
      (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ first second *
        (factor *
            localScalarPartialGradient
              period hPeriod scale patch coordinate first second -
          2 * factor ^ 2 *
              localScalarGradient
                period hPeriod scale patch coordinate first *
            localScalarGradient
              period hPeriod scale patch coordinate second -
          ∑ auxiliary : Index4,
            localLeviCivitaChristoffel period hPeriod metric
                patch coordinate auxiliary first second *
              (factor *
                localScalarGradient
                  period hPeriod scale patch coordinate auxiliary))) = _
  simp_rw [hConnection]
  have hWave :
      covariantScalarJetWave
          (localFixedSignMetric period hPeriod metric patch coordinate)
          (localCovariantScalarJet period hPeriod metric
            patch scale coordinate) =
        ∑ first : Index4, ∑ second : Index4,
          (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
              first second *
            (localScalarPartialGradient
                period hPeriod scale patch coordinate first second -
              ∑ auxiliary : Index4,
                localLeviCivitaChristoffel period hPeriod metric
                    patch coordinate auxiliary first second *
                  localScalarGradient
                    period hPeriod scale patch coordinate auxiliary) := by
    rfl
  have hPairing :
      covariantScalarGradientPairing
          (localFixedSignMetric period hPeriod metric patch coordinate)
          (localCovariantScalarJet period hPeriod metric
            patch scale coordinate)
          (localCovariantScalarJet period hPeriod metric
            patch scale coordinate) =
        ∑ first : Index4, ∑ second : Index4,
          (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
              first second *
            localScalarGradient
                period hPeriod scale patch coordinate first *
              localScalarGradient
                period hPeriod scale patch coordinate second := by
    rfl
  have hPartialFactor :
      (∑ first : Index4, ∑ second : Index4,
        (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
            first second *
          (factor *
            localScalarPartialGradient
              period hPeriod scale patch coordinate first second)) =
        factor * ∑ first : Index4, ∑ second : Index4,
          (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
              first second *
            localScalarPartialGradient
              period hPeriod scale patch coordinate first second := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro second _
    ring
  have hQuadraticFactor :
      (∑ first : Index4, ∑ second : Index4,
        (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
            first second *
          (2 * factor ^ 2 *
              localScalarGradient
                period hPeriod scale patch coordinate first *
            localScalarGradient
              period hPeriod scale patch coordinate second)) =
        2 * factor ^ 2 *
          (∑ first : Index4, ∑ second : Index4,
            (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
                first second *
              localScalarGradient
                  period hPeriod scale patch coordinate first *
                localScalarGradient
                  period hPeriod scale patch coordinate second) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro second _
    ring
  have hConnectionFactor :
      (∑ first : Index4, ∑ second : Index4,
        (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
            first second *
          (factor * ∑ auxiliary : Index4,
            localLeviCivitaChristoffel period hPeriod metric
                patch coordinate auxiliary first second *
              localScalarGradient
                period hPeriod scale patch coordinate auxiliary)) =
        factor * ∑ first : Index4, ∑ second : Index4,
          (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
              first second *
            (∑ auxiliary : Index4,
              localLeviCivitaChristoffel period hPeriod metric
                  patch coordinate auxiliary first second *
                localScalarGradient
                  period hPeriod scale patch coordinate auxiliary) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro second _
    ring
  rw [show
    covariantScalarJetWave
        (localFixedSignMetric period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)
        (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch scale coordinate) =
      covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric
          patch scale coordinate) by rfl]
  rw [hWave]
  rw [show
    covariantScalarGradientPairing
        (localFixedSignMetric period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)
        (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch scale coordinate)
        (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch scale coordinate) =
      covariantScalarGradientPairing
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric
          patch scale coordinate)
        (localCovariantScalarJet period hPeriod metric
          patch scale coordinate) by rfl]
  rw [hPairing]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hPartialFactor, hQuadraticFactor, hConnectionFactor]
  dsimp [factor]
  ring

theorem localConformalLogGradientCovariantDerivative_trace_eq_divergence
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (∑ first : Index4, ∑ second : Index4,
      (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ first second *
        localConformalLogGradientCovariantDerivative
          period hPeriod scale patch coordinate first second) =
      localConformalRaisedLogGradientDivergence
        period hPeriod scale patch coordinate := by
  rw [localConformalLogGradientCovariantDerivative_trace_normal_form
    period hPeriod scale hScale patch coordinate]
  exact
    (localConformalRaisedLogGradientDivergence_normal_form
      period hPeriod scale hScale patch coordinate).symm

/-- Scalar contraction of the linear Palatini Ricci contribution. -/
def localConformalPalatiniLinearScalarCorrection
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ first : Index4, ∑ second : Index4,
    (localMetricMatrix period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate)⁻¹ first second *
      localConformalRicciPalatiniLinear
        period hPeriod scale patch coordinate first second

theorem localConformalPalatiniLinearScalarCorrection_eq_neg_six_divergence
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localConformalPalatiniLinearScalarCorrection
        period hPeriod scale patch coordinate =
      -6 * localConformalRaisedLogGradientDivergence
        period hPeriod scale patch coordinate := by
  let inverse := fun first second : Index4 =>
    (localMetricMatrix period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch coordinate)⁻¹ first second
  have hFirst :
      (∑ first : Index4, ∑ second : Index4,
        inverse first second *
          (∑ contracted : Index4,
            localConformalChristoffelCorrectionCovariantDerivative
              period hPeriod scale patch coordinate
              contracted contracted second first)) =
        -2 * localConformalRaisedLogGradientDivergence
          period hPeriod scale patch coordinate := by
    calc
      _ = ∑ first : Index4, ∑ second : Index4, ∑ contracted : Index4,
          inverse first second *
            localConformalChristoffelCorrectionCovariantDerivative
              period hPeriod scale patch coordinate
              contracted contracted second first := by
        simp_rw [Finset.mul_sum]
      _ = ∑ contracted : Index4, ∑ second : Index4, ∑ first : Index4,
          inverse first second *
            localConformalChristoffelCorrectionCovariantDerivative
              period hPeriod scale patch coordinate
              contracted contracted second first := by
        rw [tripleSum_swap_first_third]
      _ = ∑ contracted : Index4, ∑ first : Index4, ∑ second : Index4,
          inverse first second *
            localConformalChristoffelCorrectionCovariantDerivative
              period hPeriod scale patch coordinate
              contracted contracted second first := by
        apply Finset.sum_congr rfl
        intro contracted _
        rw [Finset.sum_comm]
      _ = ∑ contracted : Index4,
          -2 *
            (localConformalRaisedLogGradientDerivative
                period hPeriod scale patch coordinate contracted contracted +
              ∑ auxiliary : Index4,
                localLeviCivitaChristoffel period hPeriod
                    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                    patch coordinate contracted contracted auxiliary *
                  localConformalRaisedLogGradient
                    period hPeriod scale patch coordinate auxiliary) := by
        apply Finset.sum_congr rfl
        intro contracted _
        exact
          localConformalChristoffelCorrectionCovariantDerivative_inverse_trace
            period hPeriod scale hScale patch coordinate contracted contracted
      _ = _ := by
        unfold localConformalRaisedLogGradientDivergence
        rw [Finset.mul_sum]
  have hSecond :
      (∑ first : Index4, ∑ second : Index4,
        inverse first second *
          (∑ contracted : Index4,
            localConformalChristoffelCorrectionCovariantDerivative
              period hPeriod scale patch coordinate
              second contracted contracted first)) =
        4 * localConformalRaisedLogGradientDivergence
          period hPeriod scale patch coordinate := by
    calc
      _ = ∑ first : Index4, ∑ second : Index4,
          inverse first second *
            (4 * localConformalLogGradientCovariantDerivative
              period hPeriod scale patch coordinate second first) := by
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro second _
        rw [localConformalChristoffelCorrectionCovariantDerivative_trace
          period hPeriod scale hScale patch coordinate second first]
      _ = ∑ first : Index4, ∑ second : Index4,
          inverse first second *
            (4 * localConformalLogGradientCovariantDerivative
              period hPeriod scale patch coordinate first second) := by
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro second _
        rw [localConformalLogGradientCovariantDerivative_symmetric
          period hPeriod scale hScale patch coordinate second first]
      _ = 4 * (∑ first : Index4, ∑ second : Index4,
          inverse first second *
            localConformalLogGradientCovariantDerivative
              period hPeriod scale patch coordinate first second) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro first _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro second _
        ring
      _ = _ := by
        rw [show
          (∑ first : Index4, ∑ second : Index4,
            inverse first second *
              localConformalLogGradientCovariantDerivative
                period hPeriod scale patch coordinate first second) =
            localConformalRaisedLogGradientDivergence
              period hPeriod scale patch coordinate by
          exact localConformalLogGradientCovariantDerivative_trace_eq_divergence
            period hPeriod scale hScale patch coordinate]
  unfold localConformalPalatiniLinearScalarCorrection
  simp_rw [localConformalRicciPalatiniLinear_eq_covariant]
  unfold localConformalRicciPalatiniCovariant
  simp only [mul_sub, Finset.sum_sub_distrib]
  change
    (∑ first : Index4, ∑ second : Index4,
      inverse first second *
        (∑ contracted : Index4,
          localConformalChristoffelCorrectionCovariantDerivative
            period hPeriod scale patch coordinate
            contracted contracted second first)) -
      (∑ first : Index4, ∑ second : Index4,
        inverse first second *
          (∑ contracted : Index4,
            localConformalChristoffelCorrectionCovariantDerivative
              period hPeriod scale patch coordinate
              second contracted contracted first)) =
      -6 * localConformalRaisedLogGradientDivergence
        period hPeriod scale patch coordinate
  rw [hFirst, hSecond]
  ring

theorem localConformalPalatiniLinearScalarCorrection_eq_standard
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localConformalPalatiniLinearScalarCorrection
        period hPeriod scale patch coordinate =
      localStandardConformalLinearScalarCorrection
        period hPeriod scale patch coordinate := by
  rw [localConformalPalatiniLinearScalarCorrection_eq_neg_six_divergence
    period hPeriod scale hScale patch coordinate]
  rw [localConformalRaisedLogGradientDivergence_normal_form
    period hPeriod scale hScale patch coordinate]
  unfold localStandardConformalLinearScalarCorrection
  have hScaleNe :
      localScalarRepresentative period hPeriod scale patch coordinate ≠ 0 :=
    ne_of_gt (hScale (patch.coordinateMap coordinate))
  field_simp [hScaleNe]
  ring

end

end P0EFTJanusMappingTorusSpatialConformalPalatiniLinear4D
end JanusFormal
