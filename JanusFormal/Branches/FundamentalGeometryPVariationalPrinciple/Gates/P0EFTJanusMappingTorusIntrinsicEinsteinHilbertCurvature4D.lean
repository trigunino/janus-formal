import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

/-!
# Intrinsic local curvature of a general quotient metric

Starting from the already constructed Levi--Civita coefficients, this gate
forms their coordinate derivative, the Riemann and Ricci tensors, the scalar
curvature and the Einstein tensor.  Every object is computed from the same
genuine Lorentz metric; no curvature field is supplied independently.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff Matrix
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

private def coordinateBasisVector (index : Index4) : Vector4 :=
  Pi.single index 1

/-- Coordinate derivative `∂_derivative Γ^upper_first,second`. -/
def localChristoffelDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative upper first second : Index4) : Real :=
  fderiv Real
      (fun current =>
        localLeviCivitaChristoffel period hPeriod metric patch current
          upper first second)
      coordinate
      (coordinateBasisVector derivative)

theorem localChristoffelDerivative_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (derivative upper first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localChristoffelDerivative period hPeriod metric patch coordinate
        derivative upper first second) := by
  have hDerivative : ContDiff Real ∞
      (fderiv Real
        (fun current =>
          localLeviCivitaChristoffel period hPeriod metric patch current
            upper first second)) :=
    (localLeviCivitaChristoffel_contDiff period hPeriod metric patch
      upper first second).fderiv_right (m := ∞) (by simp)
  exact hDerivative.clm_apply contDiff_const

/-- Riemann curvature in the convention
`R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ}
  + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}`. -/
def localRiemannCurvature
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper lower first second : Index4) : Real :=
  localChristoffelDerivative period hPeriod metric patch coordinate
      first upper second lower -
    localChristoffelDerivative period hPeriod metric patch coordinate
      second upper first lower +
    ∑ contracted : Index4,
      localLeviCivitaChristoffel period hPeriod metric patch coordinate
          upper first contracted *
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
          contracted second lower -
    ∑ contracted : Index4,
      localLeviCivitaChristoffel period hPeriod metric patch coordinate
          upper second contracted *
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
          contracted first lower

theorem localRiemannCurvature_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (upper lower first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localRiemannCurvature period hPeriod metric patch coordinate
        upper lower first second) := by
  unfold localRiemannCurvature
  apply ContDiff.sub
  · apply ContDiff.add
    · exact
        (localChristoffelDerivative_contDiff period hPeriod metric patch
          first upper second lower).sub
          (localChristoffelDerivative_contDiff period hPeriod metric patch
            second upper first lower)
    · apply ContDiff.sum
      intro contracted _
      exact
        (localLeviCivitaChristoffel_contDiff period hPeriod metric patch
          upper first contracted).mul
          (localLeviCivitaChristoffel_contDiff period hPeriod metric patch
            contracted second lower)
  · apply ContDiff.sum
    intro contracted _
    exact
      (localLeviCivitaChristoffel_contDiff period hPeriod metric patch
        upper second contracted).mul
        (localLeviCivitaChristoffel_contDiff period hPeriod metric patch
          contracted first lower)

theorem localRiemannCurvature_swap_last
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper lower first second : Index4) :
    localRiemannCurvature period hPeriod metric patch coordinate
        upper lower second first =
      -localRiemannCurvature period hPeriod metric patch coordinate
        upper lower first second := by
  unfold localRiemannCurvature
  ring

/-- Ricci contraction `R_σν = R^ρ_{σρν}`. -/
def localRicciCurvature
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) : Real :=
  ∑ contracted : Index4,
    localRiemannCurvature period hPeriod metric patch coordinate
      contracted first contracted second

theorem localRicciCurvature_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localRicciCurvature period hPeriod metric patch coordinate
        first second) := by
  apply ContDiff.sum
  intro contracted _
  exact localRiemannCurvature_contDiff period hPeriod metric patch
    contracted first contracted second

/-- Scalar curvature `R = g^{μν} R_μν`. -/
def localScalarCurvature
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ first : Index4, ∑ second : Index4,
    (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ first second *
      localRicciCurvature period hPeriod metric patch coordinate first second

theorem localScalarCurvature_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localScalarCurvature period hPeriod metric patch) := by
  apply ContDiff.sum
  intro first _
  apply ContDiff.sum
  intro second _
  exact
    (localMetricInverseEntry_contDiff period hPeriod metric patch first second).mul
      (localRicciCurvature_contDiff period hPeriod metric patch first second)

/-- Einstein tensor with cosmological constant,
`G_μν + Λg_μν = R_μν - 1/2 g_μν R + Λg_μν`. -/
def localEinsteinTensor
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) : Real :=
  localRicciCurvature period hPeriod metric patch coordinate first second -
    1 / 2 *
      localMetricMatrix period hPeriod metric patch coordinate first second *
      localScalarCurvature period hPeriod metric patch coordinate +
    cosmologicalConstant *
      localMetricMatrix period hPeriod metric patch coordinate first second

theorem localEinsteinTensor_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (cosmologicalConstant : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localEinsteinTensor period hPeriod metric cosmologicalConstant patch
        coordinate first second) := by
  unfold localEinsteinTensor
  exact
    ((localRicciCurvature_contDiff period hPeriod metric patch first second).sub
      ((contDiff_const.mul
        (localMetricCoefficient_contDiff period hPeriod metric patch
          first second)).mul
        (localScalarCurvature_contDiff period hPeriod metric patch))).add
      (contDiff_const.mul
        (localMetricCoefficient_contDiff period hPeriod metric patch
          first second))

end

end P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
end JanusFormal
