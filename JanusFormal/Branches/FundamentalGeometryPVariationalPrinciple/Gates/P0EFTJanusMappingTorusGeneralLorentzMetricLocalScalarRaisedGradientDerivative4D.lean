import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalInverseDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D

/-!
# Actual coordinate derivative of the raised scalar gradient
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarRaisedGradientDerivative4D

set_option autoImplicit false
noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalInverseDerivative4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

variable (period : Real) (hPeriod : period ≠ 0)

/-- The derivative of the genuine coordinate gradient is the genuine raw
second scalar derivative. -/
theorem localScalarGradient_fderiv_basis
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative component : Index4) :
    fderiv Real
        (fun current => localScalarGradient period hPeriod field patch current component)
        coordinate (Pi.single derivative 1) =
      localScalarPartialGradient period hPeriod field patch coordinate
        derivative component := by
  have hFirst : DifferentiableAt Real
      (fderiv Real (localScalarRepresentative period hPeriod field patch))
      coordinate :=
    (((localScalarRepresentative_contDiff period hPeriod field patch).fderiv_right
      (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hDirection : DifferentiableAt Real
      (fun _ : Vector4 => (Pi.single component (1 : Real) : Vector4)) coordinate :=
    differentiableAt_const (c := (Pi.single component (1 : Real) : Vector4))
  have hProduct := fderiv_clm_apply hFirst hDirection
  have hApply := congrArg (fun map => map (Pi.single derivative 1)) hProduct
  change
    fderiv Real
        (fun current =>
          fderiv Real (localScalarRepresentative period hPeriod field patch) current
            (Pi.single component 1))
        coordinate (Pi.single derivative 1) =
      fderiv Real
          (fderiv Real (localScalarRepresentative period hPeriod field patch))
          coordinate (Pi.single derivative 1) (Pi.single component 1)
  simpa using hApply

/-- Raised-gradient components written using the analytic ring inverse. -/
def localActualScalarRaisedGradient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (coordinate : Vector4) (upper : Index4) : Real :=
  ∑ lower : Index4,
    Ring.inverse (localMetricMatrix period hPeriod metric patch coordinate) upper lower *
      localScalarGradient period hPeriod field patch coordinate lower

theorem localActualScalarRaisedGradient_eq_localSmooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (coordinate : Vector4) (upper : Index4) :
    localActualScalarRaisedGradient period hPeriod metric patch field coordinate upper =
      localSmoothScalarRaisedGradient period hPeriod metric patch field coordinate upper := by
  unfold localActualScalarRaisedGradient localSmoothScalarRaisedGradient
    covariantScalarJetRaisedGradient localFixedSignMetric localCovariantScalarJet
    coordinateScalarJetNormalForm localCoordinateScalarJet Matrix.mulVec dotProduct
  rw [← Matrix.nonsing_inv_eq_ringInverse]

/-- Actual Frechet derivative of every raised-gradient component. -/
theorem localActualScalarRaisedGradient_fderiv_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (coordinate : Vector4) (derivative upper : Index4) :
    fderiv Real
        (fun current =>
          localActualScalarRaisedGradient period hPeriod metric patch field current upper)
        coordinate (Pi.single derivative 1) =
      ∑ lower : Index4,
        (localActualInverseMetricDerivative period hPeriod metric patch coordinate derivative
              upper lower *
            localScalarGradient period hPeriod field patch coordinate lower +
          Ring.inverse (localMetricMatrix period hPeriod metric patch coordinate) upper lower *
            localScalarPartialGradient period hPeriod field patch coordinate
              derivative lower) := by
  have hInverse (lower : Index4) : DifferentiableAt Real
      (fun current => Ring.inverse
        (localMetricMatrix period hPeriod metric patch current) upper lower) coordinate := by
    have hFunctions :
        (fun current => Ring.inverse
          (localMetricMatrix period hPeriod metric patch current) upper lower) =
        fun current =>
          (localMetricMatrix period hPeriod metric patch current)⁻¹ upper lower := by
      funext current
      rw [Matrix.nonsing_inv_eq_ringInverse]
    rw [hFunctions]
    exact ((localMetricInverseEntry_contDiff period hPeriod metric patch upper lower).differentiable
      (by simp)).differentiableAt
  have hGradient (lower : Index4) : DifferentiableAt Real
      (fun current => localScalarGradient period hPeriod field patch current lower)
      coordinate :=
    ((localScalarGradient_component_contDiff period hPeriod field patch lower).differentiable
      (by simp)).differentiableAt
  have hSum := fderiv_fun_sum (u := Finset.univ)
    (fun lower _ => (hInverse lower).mul (hGradient lower))
  have hApply := congrArg (fun map => map (Pi.single derivative 1)) hSum
  unfold localActualScalarRaisedGradient
  calc
    _ = (∑ lower : Index4,
        fderiv Real
          ((fun current => Ring.inverse
              (localMetricMatrix period hPeriod metric patch current) upper lower) *
            fun current => localScalarGradient period hPeriod field patch current lower)
          coordinate) (Pi.single derivative 1) := hApply
    _ = _ := by
      simp only [ContinuousLinearMap.sum_apply, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro lower _
      rw [fderiv_mul (hInverse lower) (hGradient lower)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      rw [localMetricInverseEntry_fderiv_basis,
        localScalarGradient_fderiv_basis]
      ring

end
end P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarRaisedGradientDerivative4D
end JanusFormal
