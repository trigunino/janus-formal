import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

/-!
# Smooth scalar jets on local Levi--Civita patches

A genuine smooth scalar field on the effective quotient is pulled back through
a supplied smooth holonomic patch.  Its first and second Fréchet derivatives
give the coordinate scalar jet, and Schwarz symmetry supplies the required
symmetric raw Hessian.  Combining this jet with the local Levi--Civita gate
proves patchwise stress conservation under the corresponding scalar Euler
equation.  No overlap compatibility or global connection is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private def coordinateBasisVector (index : Index4) : Vector4 :=
  Pi.single index 1

/-- Coordinate representative of a genuine smooth quotient scalar. -/
def localScalarRepresentative
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) : Vector4 → Real :=
  fun coordinate => field (patch.coordinateMap coordinate)

theorem localScalarRepresentative_contDiff
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (localScalarRepresentative period hPeriod field patch) := by
  exact
    ((field.contMDiff_toFun.of_le (m := ∞) (by simp)).comp
      patch.coordinateMap_contMDiff).contDiff

/-- Genuine first coordinate derivative of the pulled-back scalar. -/
def localScalarGradient
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Vector4 :=
  fun index =>
    fderiv Real (localScalarRepresentative period hPeriod field patch)
      coordinate (coordinateBasisVector index)

theorem localScalarGradient_component_contDiff
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (index : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localScalarGradient period hPeriod field patch coordinate index) := by
  have hDerivative : ContDiff Real ∞
      (fderiv Real (localScalarRepresentative period hPeriod field patch)) :=
    (localScalarRepresentative_contDiff period hPeriod field patch).fderiv_right
      (m := ∞) (by simp)
  exact hDerivative.clm_apply contDiff_const

theorem localScalarGradient_contDiff
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (localScalarGradient period hPeriod field patch) := by
  rw [contDiff_pi]
  exact localScalarGradient_component_contDiff period hPeriod field patch

/-- Genuine second coordinate derivative of the pulled-back scalar. -/
def localScalarPartialGradient
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Matrix4 :=
  fun first second =>
    fderiv Real
        (fderiv Real (localScalarRepresentative period hPeriod field patch))
        coordinate (coordinateBasisVector first) (coordinateBasisVector second)

theorem localScalarPartialGradient_component_contDiff
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localScalarPartialGradient period hPeriod field patch coordinate
        first second) := by
  have hFirstDerivative : ContDiff Real ∞
      (fderiv Real (localScalarRepresentative period hPeriod field patch)) :=
    (localScalarRepresentative_contDiff period hPeriod field patch).fderiv_right
      (m := ∞) (by simp)
  have hSecondDerivative : ContDiff Real ∞
      (fderiv Real
        (fderiv Real (localScalarRepresentative period hPeriod field patch))) :=
    hFirstDerivative.fderiv_right (m := ∞) (by simp)
  exact
    (hSecondDerivative.clm_apply contDiff_const).clm_apply contDiff_const

theorem localScalarPartialGradient_contDiff
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localScalarPartialGradient period hPeriod field patch) := by
  have hFormula :
      localScalarPartialGradient period hPeriod field patch =
        fun coordinate => ∑ first : Index4, ∑ second : Index4,
          localScalarPartialGradient period hPeriod field patch coordinate
              first second •
            Matrix.single first second (1 : Real) := by
    funext coordinate
    simpa using
      (Matrix.matrix_eq_sum_single
        (localScalarPartialGradient period hPeriod field patch coordinate))
  rw [hFormula]
  apply ContDiff.sum
  intro first _
  apply ContDiff.sum
  intro second _
  exact
    (localScalarPartialGradient_component_contDiff
      period hPeriod field patch first second).smul_const _

theorem localScalarPartialGradient_symmetric
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (localScalarPartialGradient period hPeriod field patch coordinate).transpose =
      localScalarPartialGradient period hPeriod field patch coordinate := by
  ext first second
  simp only [Matrix.transpose_apply, localScalarPartialGradient]
  have hSmooth : minSmoothness Real 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact ContDiffAt.isSymmSndFDerivAt
    (localScalarRepresentative_contDiff period hPeriod field patch).contDiffAt
    hSmooth
    (coordinateBasisVector second) (coordinateBasisVector first)

/-- Actual coordinate second jet of a smooth quotient scalar in the patch. -/
def localCoordinateScalarJet
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : CoordinateScalarJet2 where
  field := localScalarRepresentative period hPeriod field patch coordinate
  gradient := localScalarGradient period hPeriod field patch coordinate
  partialGradient := localScalarPartialGradient period hPeriod field patch coordinate
  partialGradient_symmetric :=
    localScalarPartialGradient_symmetric period hPeriod field patch coordinate

/-- Genuine covariant scalar jet obtained from the smooth scalar derivatives
and the local Levi--Civita connection. -/
def localCovariantScalarJet
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (coordinate : Vector4) : CovariantScalarJet2 :=
  coordinateScalarJetNormalForm
    (localLeviCivitaConnectionJet period hPeriod metric patch coordinate)
    (localCoordinateScalarJet period hPeriod field patch coordinate)

theorem localCovariantScalarJet_field_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod) :
    ContDiff Real ∞ (fun coordinate =>
      (localCovariantScalarJet period hPeriod metric patch field coordinate).field) := by
  simpa [localCovariantScalarJet, coordinateScalarJetNormalForm,
    localCoordinateScalarJet] using
    localScalarRepresentative_contDiff period hPeriod field patch

theorem localCovariantScalarJet_gradient_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod) :
    ContDiff Real ∞ (fun coordinate =>
      (localCovariantScalarJet period hPeriod metric patch field coordinate).gradient) := by
  simpa [localCovariantScalarJet, coordinateScalarJetNormalForm,
    localCoordinateScalarJet] using
    localScalarGradient_contDiff period hPeriod field patch

theorem localCovariantScalarJet_hessian_component_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      (localCovariantScalarJet period hPeriod metric patch field coordinate).hessian
        first second) := by
  have hCorrection : ContDiff Real ∞ (fun coordinate =>
      ∑ upper : Index4,
        localLeviCivitaChristoffel period hPeriod metric patch coordinate
            upper first second *
          localScalarGradient period hPeriod field patch coordinate upper) := by
    apply ContDiff.sum
    intro upper _
    exact
      (localLeviCivitaChristoffel_contDiff period hPeriod metric patch
        upper first second).mul
        (localScalarGradient_component_contDiff period hPeriod field patch upper)
  simpa [localCovariantScalarJet, coordinateScalarJetNormalForm,
    coordinateCovariantHessian, localCoordinateScalarJet] using
    (localScalarPartialGradient_component_contDiff
      period hPeriod field patch first second).sub hCorrection

theorem localCovariantScalarJet_hessian_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod) :
    ContDiff Real ∞ (fun coordinate =>
      (localCovariantScalarJet period hPeriod metric patch field coordinate).hessian) := by
  have hFormula :
      (fun coordinate =>
        (localCovariantScalarJet period hPeriod metric patch field coordinate).hessian) =
        fun coordinate => ∑ first : Index4, ∑ second : Index4,
          (localCovariantScalarJet period hPeriod metric patch field coordinate).hessian
              first second •
            Matrix.single first second (1 : Real) := by
    funext coordinate
    simpa using
      (Matrix.matrix_eq_sum_single
        (localCovariantScalarJet period hPeriod metric patch field coordinate).hessian)
  rw [hFormula]
  apply ContDiff.sum
  intro first _
  apply ContDiff.sum
  intro second _
  exact
    (localCovariantScalarJet_hessian_component_contDiff
      period hPeriod metric patch field first second).smul_const _

/-- Local Euler residual for the pointwise scalar-potential convention. -/
def localSmoothScalarEulerResidual
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (massSquared source : Real) (coordinate : Vector4) : Real :=
  covariantScalarStressEulerResidual
    (localFixedSignMetric period hPeriod metric patch coordinate)
    (pointwiseScalarPotentialSlope massSquared source
      (localScalarRepresentative period hPeriod field patch coordinate))
    (localCovariantScalarJet period hPeriod metric patch field coordinate)

theorem localSmoothScalarEulerResidual_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (massSquared source : Real) :
    ContDiff Real ∞
      (localSmoothScalarEulerResidual period hPeriod metric patch field
        massSquared source) := by
  have hWave : ContDiff Real ∞ (fun coordinate =>
      covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch field coordinate)) := by
    unfold covariantScalarJetWave
    apply ContDiff.sum
    intro first _
    apply ContDiff.sum
    intro second _
    exact
      (localMetricInverseEntry_contDiff period hPeriod metric patch first second).mul
        (localCovariantScalarJet_hessian_component_contDiff
          period hPeriod metric patch field first second)
  have hSlope : ContDiff Real ∞ (fun coordinate =>
      pointwiseScalarPotentialSlope massSquared source
        (localScalarRepresentative period hPeriod field patch coordinate)) := by
    unfold pointwiseScalarPotentialSlope
    exact
      (contDiff_const.mul
        (localScalarRepresentative_contDiff period hPeriod field patch)).add
        contDiff_const
  change ContDiff Real ∞ (fun coordinate =>
    covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch field coordinate) -
      pointwiseScalarPotentialSlope massSquared source
        (localScalarRepresentative period hPeriod field patch coordinate))
  exact hWave.sub hSlope

/-- Metric-raised gradient of the genuine local covariant scalar jet. -/
def localSmoothScalarRaisedGradient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (coordinate : Vector4) : Vector4 :=
  covariantScalarJetRaisedGradient
    (localFixedSignMetric period hPeriod metric patch coordinate)
    (localCovariantScalarJet period hPeriod metric patch field coordinate)

theorem localSmoothScalarRaisedGradient_component_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (index : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localSmoothScalarRaisedGradient period hPeriod metric patch field coordinate
        index) := by
  have hSum : ContDiff Real ∞ (fun coordinate =>
      ∑ second : Index4,
        (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ index second *
          localScalarGradient period hPeriod field patch coordinate second) := by
    apply ContDiff.sum
    intro second _
    exact
      (localMetricInverseEntry_contDiff period hPeriod metric patch index second).mul
        (localScalarGradient_component_contDiff period hPeriod field patch second)
  simpa [localSmoothScalarRaisedGradient, covariantScalarJetRaisedGradient,
    localFixedSignMetric, localCovariantScalarJet, coordinateScalarJetNormalForm,
    localCoordinateScalarJet, Matrix.mulVec, dotProduct] using hSum

theorem localSmoothScalarRaisedGradient_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod) :
    ContDiff Real ∞
      (localSmoothScalarRaisedGradient period hPeriod metric patch field) := by
  rw [contDiff_pi]
  exact localSmoothScalarRaisedGradient_component_contDiff
    period hPeriod metric patch field

/-- Canonically realized local covariant divergence of the smooth scalar
stress. -/
def localSmoothScalarStressDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (massSquared source : Real)
    (coordinate : Vector4) : Vector4 :=
  coordinateCovariantStressDivergence
    (localLeviCivitaStressRealization period hPeriod metric patch
      (fun current => pointwiseScalarPotentialValue massSquared source
        (localScalarRepresentative period hPeriod field patch current))
      (fun current => pointwiseScalarPotentialSlope massSquared source
        (localScalarRepresentative period hPeriod field patch current))
      (localCoordinateScalarJet period hPeriod field patch)
      coordinate)

theorem localSmoothScalarStressDivergence_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (massSquared source : Real) (coordinate : Vector4) (index : Index4) :
    localSmoothScalarStressDivergence period hPeriod metric patch field
        massSquared source coordinate index =
      localSmoothScalarEulerResidual period hPeriod metric patch field
          massSquared source coordinate *
        localSmoothScalarRaisedGradient period hPeriod metric patch field
          coordinate index := by
  unfold localSmoothScalarStressDivergence
  rw [coordinateCovariantStressDivergence_transport_normal,
    covariantScalarJetStressDivergence_eq_euler_mul_raisedGradient]
  rfl

theorem localSmoothScalarStressDivergence_component_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (massSquared source : Real) (index : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localSmoothScalarStressDivergence period hPeriod metric patch field
        massSquared source coordinate index) := by
  have hFormula :
      (fun coordinate =>
        localSmoothScalarStressDivergence period hPeriod metric patch field
          massSquared source coordinate index) =
        fun coordinate =>
          localSmoothScalarEulerResidual period hPeriod metric patch field
              massSquared source coordinate *
            localSmoothScalarRaisedGradient period hPeriod metric patch field
              coordinate index := by
    funext coordinate
    exact localSmoothScalarStressDivergence_apply
      period hPeriod metric patch field massSquared source coordinate index
  rw [hFormula]
  exact
    (localSmoothScalarEulerResidual_contDiff
      period hPeriod metric patch field massSquared source).mul
      (localSmoothScalarRaisedGradient_component_contDiff
        period hPeriod metric patch field index)

theorem localSmoothScalarStressDivergence_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (massSquared source : Real) :
    ContDiff Real ∞
      (localSmoothScalarStressDivergence period hPeriod metric patch field
        massSquared source) := by
  rw [contDiff_pi]
  exact localSmoothScalarStressDivergence_component_contDiff
    period hPeriod metric patch field massSquared source

/-- Stress conservation for the actual smooth scalar jet in every coordinate
of the supplied Levi--Civita patch. -/
theorem localSmoothScalarStressDivergence_eq_zero_of_euler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (massSquared source : Real)
    (hEuler : ∀ coordinate,
      localSmoothScalarEulerResidual period hPeriod metric patch field
        massSquared source coordinate = 0) :
    ∀ coordinate,
      localSmoothScalarStressDivergence period hPeriod metric patch field
        massSquared source coordinate = 0 := by
  intro coordinate
  funext index
  rw [localSmoothScalarStressDivergence_apply, hEuler coordinate]
  simp

end

end P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
end JanusFormal
