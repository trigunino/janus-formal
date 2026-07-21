import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D

/-!
# Local covariant divergence of a cutoff scalar Green current
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffScalarGreenDivergence4D

set_option autoImplicit false
noncomputable section

open scoped ContDiff
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarRaisedGradientDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

variable (period : Real) (hPeriod : period ≠ 0)

/-- Coordinate components of `cutoff • (phi grad psi - psi grad phi)`. -/
def localActualCutoffScalarGreenCurrent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (cutoff : Vector4 → Real) (coordinate : Vector4) (upper : Index4) : Real :=
  cutoff coordinate *
    localActualScalarGreenCurrent period hPeriod metric patch field test coordinate upper

/-- Genuine coordinate divergence of the cutoff Green current. -/
def localActualCutoffScalarGreenCoordinateDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (cutoff : Vector4 → Real) (coordinate : Vector4) : Real :=
  ∑ derivative : Index4,
    (fderiv Real
        (fun current =>
          localActualCutoffScalarGreenCurrent period hPeriod metric patch field test
            cutoff current derivative)
        coordinate (Pi.single derivative 1) +
      ∑ lower : Index4,
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
            derivative derivative lower *
          localActualCutoffScalarGreenCurrent period hPeriod metric patch field test
            cutoff coordinate lower)

theorem localActualCutoffScalarGreenCurrent_fderiv_basis
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (cutoff : Vector4 → Real) (coordinate : Vector4)
    (hCutoff : DifferentiableAt Real cutoff coordinate)
    (derivative upper : Index4) :
    fderiv Real
        (fun current =>
          localActualCutoffScalarGreenCurrent period hPeriod metric patch field test
            cutoff current upper)
        coordinate (Pi.single derivative 1) =
      fderiv Real cutoff coordinate (Pi.single derivative 1) *
          localActualScalarGreenCurrent period hPeriod metric patch field test
            coordinate upper +
        cutoff coordinate *
          fderiv Real
            (fun current =>
              localActualScalarGreenCurrent period hPeriod metric patch field test
                current upper)
            coordinate (Pi.single derivative 1) := by
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
    apply DifferentiableAt.congr_of_eventuallyEq
      ((localSmoothScalarRaisedGradient_component_contDiff
        period hPeriod metric patch currentField upper).differentiable
          (by simp)).differentiableAt
    exact Filter.Eventually.of_forall fun current =>
      (localActualScalarRaisedGradient_eq_localSmooth
        period hPeriod metric patch currentField current upper)
  have hGreen : DifferentiableAt Real
      (fun current => localActualScalarGreenCurrent period hPeriod metric patch
        field test current upper) coordinate := by
    unfold localActualScalarGreenCurrent
    exact (hField.mul (hRaised test)).sub (hTest.mul (hRaised field))
  unfold localActualCutoffScalarGreenCurrent
  rw [congrArg (fun map => map (Pi.single derivative 1))
    (fderiv_fun_mul hCutoff hGreen)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Covariant Leibniz rule `div(cutoff J) = d cutoff(J) + cutoff div J`. -/
theorem localActualCutoffScalarGreenCoordinateDivergence_eq_leibniz
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (cutoff : Vector4 → Real) (coordinate : Vector4)
    (hCutoff : DifferentiableAt Real cutoff coordinate) :
    localActualCutoffScalarGreenCoordinateDivergence period hPeriod metric patch
        field test cutoff coordinate =
      (∑ derivative : Index4,
        fderiv Real cutoff coordinate (Pi.single derivative 1) *
          localActualScalarGreenCurrent period hPeriod metric patch field test
            coordinate derivative) +
        cutoff coordinate *
          localActualScalarGreenCoordinateDivergence period hPeriod metric patch
            field test coordinate := by
  unfold localActualCutoffScalarGreenCoordinateDivergence
    localActualScalarGreenCoordinateDivergence
  simp_rw [localActualCutoffScalarGreenCurrent_fderiv_basis
    period hPeriod metric patch field test cutoff coordinate hCutoff]
  unfold localActualCutoffScalarGreenCurrent
  have hConnection :
      (∑ derivative : Index4, ∑ lower : Index4,
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
              derivative derivative lower *
          (cutoff coordinate *
            localActualScalarGreenCurrent period hPeriod metric patch field test
              coordinate lower)) =
        cutoff coordinate * (∑ derivative : Index4, ∑ lower : Index4,
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
              derivative derivative lower *
            localActualScalarGreenCurrent period hPeriod metric patch field test
              coordinate lower) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro derivative _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lower _
    ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hConnection]
  ring

/-- On a Green-conserved representative, only the cutoff-gradient flux remains. -/
theorem localActualCutoffScalarGreenCoordinateDivergence_eq_gradientFlux_of_free
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (cutoff : Vector4 → Real) (coordinate : Vector4)
    (hCutoff : DifferentiableAt Real cutoff coordinate)
    (hFree : localActualScalarGreenCoordinateDivergence period hPeriod metric patch
      field test coordinate = 0) :
    localActualCutoffScalarGreenCoordinateDivergence period hPeriod metric patch
        field test cutoff coordinate =
      ∑ derivative : Index4,
        fderiv Real cutoff coordinate (Pi.single derivative 1) *
          localActualScalarGreenCurrent period hPeriod metric patch field test
            coordinate derivative := by
  rw [localActualCutoffScalarGreenCoordinateDivergence_eq_leibniz
    period hPeriod metric patch field test cutoff coordinate hCutoff, hFree,
    mul_zero, add_zero]

end
end P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffScalarGreenDivergence4D
end JanusFormal
