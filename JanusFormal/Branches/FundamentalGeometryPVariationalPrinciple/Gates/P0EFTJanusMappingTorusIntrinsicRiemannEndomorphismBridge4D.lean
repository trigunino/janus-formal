import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D

/-!
# Intrinsic Riemann endomorphism component bridge

The endomorphism-valued curvature used by the intrinsic Bianchi gate has,
on the coordinate basis, exactly the components of the intrinsic Riemann
tensor used by the Einstein--Hilbert curvature gate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicRiemannEndomorphismBridge4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff Matrix
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

variable (period : Real) (hPeriod : period ≠ 0)

private theorem localConnectionDirectionalDerivative_basis_component
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative direction upper lower : Index4) :
    (algebraDirectionalDerivative
        (fun current =>
          localLeviCivitaConnectionEndomorphism period hPeriod metric patch
            current direction)
        coordinate derivative)
        (Pi.single lower 1) upper =
      localChristoffelDerivative period hPeriod metric patch coordinate
        derivative upper direction lower := by
  let connection :=
    fun current =>
      localLeviCivitaConnectionEndomorphism period hPeriod metric patch
        current direction
  let basisLower : Vector4 := Pi.single lower 1
  let basisDerivative : Vector4 := Pi.single derivative 1
  have hConnection : DifferentiableAt Real connection coordinate :=
    ((localLeviCivitaConnectionEndomorphism_contDiff
      period hPeriod metric patch direction).differentiable
        (by simp)).differentiableAt
  have hBasis : DifferentiableAt Real
      (fun _ : Vector4 => basisLower) coordinate :=
    differentiableAt_const _
  have hApply := fderiv_clm_apply hConnection hBasis
  have hApplyAt :=
    congrArg (fun derivativeMap => derivativeMap basisDerivative) hApply
  have hVectorDerivative :
      fderiv Real (fun current => connection current basisLower)
          coordinate basisDerivative =
        (fderiv Real connection coordinate basisDerivative) basisLower := by
    simpa using hApplyAt
  have hAppliedConnection : DifferentiableAt Real
      (fun current => connection current basisLower) coordinate :=
    hConnection.clm_apply hBasis
  have hComponent :=
    fderiv_apply hAppliedConnection upper
  have hComponentAt :=
    congrArg (fun derivativeMap => derivativeMap basisDerivative) hComponent
  have hScalarDerivative :
      fderiv Real (fun current => connection current basisLower)
          coordinate basisDerivative upper =
        fderiv Real (fun current => connection current basisLower upper)
          coordinate basisDerivative := by
    simpa using hComponentAt.symm
  have hConnectionComponent :
      (fun current => connection current basisLower upper) =
        fun current =>
          localLeviCivitaChristoffel period hPeriod metric patch current
            upper direction lower := by
    funext current
    exact
      localLeviCivitaConnectionEndomorphism_basis_apply
        period hPeriod metric patch current direction upper lower
  unfold algebraDirectionalDerivative
  change (fderiv Real connection coordinate basisDerivative) basisLower upper = _
  rw [← hVectorDerivative, hScalarDerivative, hConnectionComponent]
  unfold localChristoffelDerivative
  congr 1

private theorem localConnectionProduct_basis_component
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second upper lower : Index4) :
    ((localLeviCivitaConnectionEndomorphism period hPeriod metric patch
          coordinate first) *
        (localLeviCivitaConnectionEndomorphism period hPeriod metric patch
          coordinate second))
        (Pi.single lower 1) upper =
      ∑ contracted : Index4,
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
            upper first contracted *
          localLeviCivitaChristoffel period hPeriod metric patch coordinate
            contracted second lower := by
  simp [localLeviCivitaConnectionEndomorphism,
    localLeviCivitaConnectionMatrix, Matrix.mulVecLin, Matrix.mulVec,
    Matrix.col, dotProduct]

/-- The coordinate-basis components of the endomorphism-valued curvature
are the intrinsic Riemann tensor components used by the Einstein--Hilbert
gate. -/
theorem localLeviCivitaRiemannEndomorphism_basis_component
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper lower first second : Index4) :
    localLeviCivitaRiemannEndomorphism period hPeriod metric patch coordinate
        first second (Pi.single lower 1) upper =
      localRiemannCurvature period hPeriod metric patch coordinate
        upper lower first second := by
  unfold localLeviCivitaRiemannEndomorphism algebraConnectionCurvature
    localRiemannCurvature
  change
    (algebraDirectionalDerivative
          (fun current =>
            localLeviCivitaConnectionEndomorphism period hPeriod metric patch
              current second)
          coordinate first)
          (Pi.single lower 1) upper -
        (algebraDirectionalDerivative
          (fun current =>
            localLeviCivitaConnectionEndomorphism period hPeriod metric patch
              current first)
          coordinate second)
          (Pi.single lower 1) upper +
        ((localLeviCivitaConnectionEndomorphism period hPeriod metric patch
              coordinate first) *
            (localLeviCivitaConnectionEndomorphism period hPeriod metric patch
              coordinate second))
          (Pi.single lower 1) upper -
        ((localLeviCivitaConnectionEndomorphism period hPeriod metric patch
              coordinate second) *
            (localLeviCivitaConnectionEndomorphism period hPeriod metric patch
              coordinate first))
          (Pi.single lower 1) upper =
      _
  rw [localConnectionDirectionalDerivative_basis_component
      period hPeriod metric patch coordinate first second upper lower]
  rw [localConnectionDirectionalDerivative_basis_component
      period hPeriod metric patch coordinate second first upper lower]
  rw [localConnectionProduct_basis_component
      period hPeriod metric patch coordinate first second upper lower]
  rw [localConnectionProduct_basis_component
      period hPeriod metric patch coordinate second first upper lower]

end

end P0EFTJanusMappingTorusIntrinsicRiemannEndomorphismBridge4D
end JanusFormal
