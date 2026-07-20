import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarRaisedGradientDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenDivergence4D

/-!
# Actual coordinate derivative of the scalar Green current
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D

set_option autoImplicit false
noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalInverseDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarRaisedGradientDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenDivergence4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

variable (period : Real) (hPeriod : period ≠ 0)

theorem localScalarRepresentative_fderiv_basis
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative : Index4) :
    fderiv Real (localScalarRepresentative period hPeriod field patch) coordinate
        (Pi.single derivative 1) =
      localScalarGradient period hPeriod field patch coordinate derivative := by
  rfl

/-- Actual coordinate components of `phi grad psi - psi grad phi`. -/
def localActualScalarGreenCurrent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4) (upper : Index4) : Real :=
  localScalarRepresentative period hPeriod field patch coordinate *
      localActualScalarRaisedGradient period hPeriod metric patch test coordinate upper -
    localScalarRepresentative period hPeriod test patch coordinate *
      localActualScalarRaisedGradient period hPeriod metric patch field coordinate upper

theorem localActualScalarGreenCurrent_eq_localSmooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4) (upper : Index4) :
    localActualScalarGreenCurrent period hPeriod metric patch field test coordinate upper =
      localSmoothScalarGreenCurrent period hPeriod metric patch field test coordinate upper := by
  unfold localActualScalarGreenCurrent localSmoothScalarGreenCurrent
    covariantScalarGreenJetCurrent
  rw [localActualScalarRaisedGradient_eq_localSmooth,
    localActualScalarRaisedGradient_eq_localSmooth]
  rfl

theorem localActualScalarGreenCurrent_fderiv_basis_leibniz
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4) (derivative upper : Index4) :
    fderiv Real
        (fun current =>
          localActualScalarGreenCurrent period hPeriod metric patch field test current upper)
        coordinate (Pi.single derivative 1) =
      localScalarGradient period hPeriod field patch coordinate derivative *
          localActualScalarRaisedGradient period hPeriod metric patch test coordinate upper +
        localScalarRepresentative period hPeriod field patch coordinate *
          fderiv Real
            (fun current =>
              localActualScalarRaisedGradient period hPeriod metric patch test current upper)
            coordinate (Pi.single derivative 1) -
      (localScalarGradient period hPeriod test patch coordinate derivative *
          localActualScalarRaisedGradient period hPeriod metric patch field coordinate upper +
        localScalarRepresentative period hPeriod test patch coordinate *
          fderiv Real
            (fun current =>
              localActualScalarRaisedGradient period hPeriod metric patch field current upper)
            coordinate (Pi.single derivative 1)) := by
  have hField : DifferentiableAt Real
      (localScalarRepresentative period hPeriod field patch) coordinate :=
    ((localScalarRepresentative_contDiff period hPeriod field patch).differentiable
      (by simp)).differentiableAt
  have hTest : DifferentiableAt Real
      (localScalarRepresentative period hPeriod test patch) coordinate :=
    ((localScalarRepresentative_contDiff period hPeriod test patch).differentiable
      (by simp)).differentiableAt
  have hRaised (currentField : SmoothScalarField period hPeriod) : DifferentiableAt Real
      (fun current =>
        localActualScalarRaisedGradient period hPeriod metric patch currentField current upper)
      coordinate := by
    have hFunctions :
        (fun current =>
          localActualScalarRaisedGradient period hPeriod metric patch currentField current upper) =
        fun current =>
          localSmoothScalarRaisedGradient period hPeriod metric patch currentField current upper := by
      funext current
      exact localActualScalarRaisedGradient_eq_localSmooth
        period hPeriod metric patch currentField current upper
    rw [hFunctions]
    exact ((localSmoothScalarRaisedGradient_component_contDiff
      period hPeriod metric patch currentField upper).differentiable (by simp)).differentiableAt
  unfold localActualScalarGreenCurrent
  calc
    _ = (fderiv Real
          (fun current =>
            localScalarRepresentative period hPeriod field patch current *
              localActualScalarRaisedGradient period hPeriod metric patch test current upper)
          coordinate) (Pi.single derivative 1) -
        (fderiv Real
          (fun current =>
            localScalarRepresentative period hPeriod test patch current *
              localActualScalarRaisedGradient period hPeriod metric patch field current upper)
          coordinate) (Pi.single derivative 1) :=
      congrArg (fun map => map (Pi.single derivative 1))
        (fderiv_fun_sub (hField.mul (hRaised test)) (hTest.mul (hRaised field)))
    _ = _ := by
      rw [congrArg (fun map => map (Pi.single derivative 1))
          (fderiv_fun_mul hField (hRaised test)),
        congrArg (fun map => map (Pi.single derivative 1))
          (fderiv_fun_mul hTest (hRaised field))]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      rw [localScalarRepresentative_fderiv_basis,
        localScalarRepresentative_fderiv_basis]
      ring

/-- Leibniz rule for the genuine coordinate derivative of every current
component. -/
theorem localActualScalarGreenCurrent_fderiv_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4) (derivative upper : Index4) :
    fderiv Real
        (fun current =>
          localActualScalarGreenCurrent period hPeriod metric patch field test current upper)
        coordinate (Pi.single derivative 1) =
      localScalarGradient period hPeriod field patch coordinate derivative *
          localActualScalarRaisedGradient period hPeriod metric patch test coordinate upper +
        localScalarRepresentative period hPeriod field patch coordinate *
          (∑ lower : Index4,
            (localActualInverseMetricDerivative period hPeriod metric patch coordinate derivative
                  upper lower *
                localScalarGradient period hPeriod test patch coordinate lower +
              Ring.inverse (localMetricMatrix period hPeriod metric patch coordinate) upper lower *
                localScalarPartialGradient period hPeriod test patch coordinate derivative lower)) -
      (localScalarGradient period hPeriod test patch coordinate derivative *
          localActualScalarRaisedGradient period hPeriod metric patch field coordinate upper +
        localScalarRepresentative period hPeriod test patch coordinate *
          (∑ lower : Index4,
            (localActualInverseMetricDerivative period hPeriod metric patch coordinate derivative
                  upper lower *
                localScalarGradient period hPeriod field patch coordinate lower +
              Ring.inverse (localMetricMatrix period hPeriod metric patch coordinate) upper lower *
                localScalarPartialGradient period hPeriod field patch coordinate derivative lower))) := by
  have hField : DifferentiableAt Real
      (localScalarRepresentative period hPeriod field patch) coordinate :=
    ((localScalarRepresentative_contDiff period hPeriod field patch).differentiable
      (by simp)).differentiableAt
  have hTest : DifferentiableAt Real
      (localScalarRepresentative period hPeriod test patch) coordinate :=
    ((localScalarRepresentative_contDiff period hPeriod test patch).differentiable
      (by simp)).differentiableAt
  have hRaisedField : DifferentiableAt Real
      (fun current =>
        localActualScalarRaisedGradient period hPeriod metric patch field current upper)
      coordinate := by
    have hFunctions :
        (fun current =>
          localActualScalarRaisedGradient period hPeriod metric patch field current upper) =
        fun current =>
          localSmoothScalarRaisedGradient period hPeriod metric patch field current upper := by
      funext current
      exact localActualScalarRaisedGradient_eq_localSmooth
        period hPeriod metric patch field current upper
    rw [hFunctions]
    exact ((localSmoothScalarRaisedGradient_component_contDiff
      period hPeriod metric patch field upper).differentiable (by simp)).differentiableAt
  have hRaisedTest : DifferentiableAt Real
      (fun current =>
        localActualScalarRaisedGradient period hPeriod metric patch test current upper)
      coordinate := by
    have hFunctions :
        (fun current =>
          localActualScalarRaisedGradient period hPeriod metric patch test current upper) =
        fun current =>
          localSmoothScalarRaisedGradient period hPeriod metric patch test current upper := by
      funext current
      exact localActualScalarRaisedGradient_eq_localSmooth
        period hPeriod metric patch test current upper
    rw [hFunctions]
    exact ((localSmoothScalarRaisedGradient_component_contDiff
      period hPeriod metric patch test upper).differentiable (by simp)).differentiableAt
  unfold localActualScalarGreenCurrent
  calc
    _ = (fderiv Real
          (fun current =>
            localScalarRepresentative period hPeriod field patch current *
              localActualScalarRaisedGradient period hPeriod metric patch test current upper)
          coordinate) (Pi.single derivative 1) -
        (fderiv Real
          (fun current =>
            localScalarRepresentative period hPeriod test patch current *
              localActualScalarRaisedGradient period hPeriod metric patch field current upper)
          coordinate) (Pi.single derivative 1) :=
      congrArg (fun map => map (Pi.single derivative 1))
        (fderiv_fun_sub (hField.mul hRaisedTest) (hTest.mul hRaisedField))
    _ = _ := by
      rw [congrArg (fun map => map (Pi.single derivative 1))
          (fderiv_fun_mul hField hRaisedTest),
        congrArg (fun map => map (Pi.single derivative 1))
          (fderiv_fun_mul hTest hRaisedField)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      rw [localScalarRepresentative_fderiv_basis,
        localScalarRepresentative_fderiv_basis,
        localActualScalarRaisedGradient_fderiv_basis,
        localActualScalarRaisedGradient_fderiv_basis]
      ring

/-- The genuine coordinate divergence `partial_mu J^mu + Gamma^mu_{mu nu}J^nu`. -/
def localActualScalarGreenCoordinateDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ derivative : Index4,
    (fderiv Real
        (fun current =>
          localActualScalarGreenCurrent period hPeriod metric patch field test
            current derivative)
        coordinate (Pi.single derivative 1) +
      ∑ lower : Index4,
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
            derivative derivative lower *
          localActualScalarGreenCurrent period hPeriod metric patch field test
            coordinate lower)

end
end P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
end JanusFormal
