import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSpatialConformalCurvatureClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSpatialConformalExponentialBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarRaisedGradientDerivative4D

/-!
# Scalar curvature along a spatial conformal exponential line

This gate specializes the closed four-dimensional conformal scalar-curvature
formula to the genuine positive metric line `g_t = exp (2 t u) g`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSpatialConformalExponentialCurvature4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarRaisedGradientDerivative4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusMappingTorusGlobalSmoothScalarWave4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSpatialConformalCurvatureJet4D
open P0EFTJanusMappingTorusSpatialConformalCurvatureClosure4D
open P0EFTJanusMappingTorusSpatialConformalExponentialBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev Index4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

theorem localScalarPartialGradient_spatialConformalExponentialScale
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) :
    localScalarPartialGradient period hPeriod
        (spatialConformalExponentialScale
          period hPeriod direction parameter) patch coordinate first second =
      (2 * parameter) ^ 2 *
          localScalarRepresentative period hPeriod
            (spatialConformalExponentialScale
              period hPeriod direction parameter) patch coordinate *
          localScalarGradient period hPeriod direction patch coordinate first *
          localScalarGradient period hPeriod direction patch coordinate second +
        2 * parameter *
          localScalarRepresentative period hPeriod
            (spatialConformalExponentialScale
              period hPeriod direction parameter) patch coordinate *
          localScalarPartialGradient period hPeriod direction patch coordinate
            first second := by
  rw [← localScalarGradient_fderiv_basis period hPeriod
    (spatialConformalExponentialScale period hPeriod direction parameter)
    patch coordinate first second]
  have hFunction :
      (fun current =>
        localScalarGradient period hPeriod
          (spatialConformalExponentialScale
            period hPeriod direction parameter) patch current second) =
        (fun current =>
          (2 * parameter) *
            localScalarRepresentative period hPeriod
              (spatialConformalExponentialScale
                period hPeriod direction parameter) patch current) *
          fun current =>
            localScalarGradient period hPeriod
              direction patch current second := by
    funext current
    simp only [Pi.mul_apply]
    rw [localScalarGradient_spatialConformalExponentialScale]
  rw [hFunction]
  have hScale : DifferentiableAt Real
      (localScalarRepresentative period hPeriod
        (spatialConformalExponentialScale
          period hPeriod direction parameter) patch) coordinate :=
    ((localScalarRepresentative_contDiff period hPeriod
      (spatialConformalExponentialScale
        period hPeriod direction parameter) patch).differentiable
      (by simp)).differentiableAt
  have hGradient : DifferentiableAt Real
      (fun current =>
        localScalarGradient period hPeriod
          direction patch current second) coordinate :=
    ((localScalarGradient_component_contDiff period hPeriod
      direction patch second).differentiable (by simp)).differentiableAt
  have hFactor : DifferentiableAt Real
      (fun current =>
        (2 * parameter) *
          localScalarRepresentative period hPeriod
            (spatialConformalExponentialScale
              period hPeriod direction parameter) patch current) coordinate :=
    hScale.const_mul _
  rw [fderiv_mul hFactor hGradient]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_const_mul hScale (2 * parameter)]
  simp only [smul_apply, smul_eq_mul]
  have hScaleDerivative :
      (fderiv Real
        (localScalarRepresentative period hPeriod
          (spatialConformalExponentialScale
            period hPeriod direction parameter) patch) coordinate)
          (Pi.single first 1) =
        localScalarGradient period hPeriod
          (spatialConformalExponentialScale
            period hPeriod direction parameter) patch coordinate first :=
    rfl
  rw [localScalarGradient_fderiv_basis
    period hPeriod direction patch coordinate first second,
    hScaleDerivative,
    localScalarGradient_spatialConformalExponentialScale]
  ring

theorem localCovariantScalarWave_spatialConformalExponentialScale
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    covariantScalarJetWave
        (localFixedSignMetric period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)
        (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch
          (spatialConformalExponentialScale
            period hPeriod direction parameter) coordinate) =
      2 * parameter *
          localScalarRepresentative period hPeriod
            (spatialConformalExponentialScale
              period hPeriod direction parameter) patch coordinate *
          covariantScalarJetWave
            (localFixedSignMetric period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate)
            (localCovariantScalarJet period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch direction coordinate) +
        4 * parameter ^ 2 *
          localScalarRepresentative period hPeriod
            (spatialConformalExponentialScale
              period hPeriod direction parameter) patch coordinate *
          covariantScalarGradientPairing
            (localFixedSignMetric period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate)
            (localCovariantScalarJet period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch direction coordinate)
            (localCovariantScalarJet period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch direction coordinate) := by
  have hHessian : ∀ first second : Index4,
      (localCovariantScalarJet period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch
        (spatialConformalExponentialScale
          period hPeriod direction parameter) coordinate).hessian first second =
        2 * parameter *
            localScalarRepresentative period hPeriod
              (spatialConformalExponentialScale
                period hPeriod direction parameter) patch coordinate *
            (localCovariantScalarJet period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch direction coordinate).hessian first second +
          4 * parameter ^ 2 *
            localScalarRepresentative period hPeriod
              (spatialConformalExponentialScale
                period hPeriod direction parameter) patch coordinate *
            localScalarGradient period hPeriod direction patch coordinate first *
            localScalarGradient period hPeriod direction patch coordinate second := by
    intro first second
    have hConnection :
        (∑ auxiliary : Index4,
          (localLeviCivitaConnectionJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate).christoffel auxiliary first second *
            (2 * parameter *
              localScalarRepresentative period hPeriod
                (spatialConformalExponentialScale
                  period hPeriod direction parameter) patch coordinate *
              localScalarGradient period hPeriod
                direction patch coordinate auxiliary)) =
          2 * parameter *
            localScalarRepresentative period hPeriod
              (spatialConformalExponentialScale
                period hPeriod direction parameter) patch coordinate *
            ∑ auxiliary : Index4,
              (localLeviCivitaConnectionJet period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch coordinate).christoffel auxiliary first second *
                localScalarGradient period hPeriod
                  direction patch coordinate auxiliary := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro auxiliary _
      ring
    unfold localCovariantScalarJet coordinateScalarJetNormalForm
      coordinateCovariantHessian localCoordinateScalarJet
    dsimp only
    rw [localScalarPartialGradient_spatialConformalExponentialScale]
    simp_rw [localScalarGradient_spatialConformalExponentialScale]
    rw [hConnection]
    ring
  have hLinear :
      (∑ first : Index4, ∑ second : Index4,
        (localFixedSignMetric period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate).metric⁻¹ first second *
          (2 * parameter *
            localScalarRepresentative period hPeriod
              (spatialConformalExponentialScale
                period hPeriod direction parameter) patch coordinate *
            (localCovariantScalarJet period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch direction coordinate).hessian first second)) =
        2 * parameter *
          localScalarRepresentative period hPeriod
            (spatialConformalExponentialScale
              period hPeriod direction parameter) patch coordinate *
          covariantScalarJetWave
            (localFixedSignMetric period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate)
            (localCovariantScalarJet period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch direction coordinate) := by
    unfold covariantScalarJetWave
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    ring
  have hQuadratic :
      (∑ first : Index4, ∑ second : Index4,
        (localFixedSignMetric period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate).metric⁻¹ first second *
          (4 * parameter ^ 2 *
            localScalarRepresentative period hPeriod
              (spatialConformalExponentialScale
                period hPeriod direction parameter) patch coordinate *
            localScalarGradient period hPeriod direction patch coordinate first *
            localScalarGradient period hPeriod direction patch coordinate second)) =
        4 * parameter ^ 2 *
          localScalarRepresentative period hPeriod
            (spatialConformalExponentialScale
              period hPeriod direction parameter) patch coordinate *
          covariantScalarGradientPairing
            (localFixedSignMetric period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate)
            (localCovariantScalarJet period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch direction coordinate)
            (localCovariantScalarJet period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch direction coordinate) := by
    unfold covariantScalarGradientPairing localCovariantScalarJet
      coordinateScalarJetNormalForm localCoordinateScalarJet
    dsimp only
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    ring
  unfold covariantScalarJetWave
  simp_rw [hHessian, mul_add, Finset.sum_add_distrib]
  rw [hLinear, hQuadratic]
  rfl

theorem localCovariantScalarGradientPairing_spatialConformalExponentialScale
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    covariantScalarGradientPairing
        (localFixedSignMetric period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)
        (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch
          (spatialConformalExponentialScale
            period hPeriod direction parameter) coordinate)
        (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch
          (spatialConformalExponentialScale
            period hPeriod direction parameter) coordinate) =
      4 * parameter ^ 2 *
        (localScalarRepresentative period hPeriod
          (spatialConformalExponentialScale
            period hPeriod direction parameter) patch coordinate) ^ 2 *
        covariantScalarGradientPairing
          (localFixedSignMetric period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch direction coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch direction coordinate) := by
  unfold covariantScalarGradientPairing localCovariantScalarJet
    coordinateScalarJetNormalForm localCoordinateScalarJet
  dsimp only
  simp_rw [localScalarGradient_spatialConformalExponentialScale]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem localStandardConformalScalarCurvatureCorrection_spatialConformalExponentialScale
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localStandardConformalScalarCurvatureCorrection period hPeriod
        (spatialConformalExponentialScale
          period hPeriod direction parameter) patch coordinate =
      -6 * parameter *
          covariantScalarJetWave
            (localFixedSignMetric period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate)
            (localCovariantScalarJet period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch direction coordinate) -
        6 * parameter ^ 2 *
          covariantScalarGradientPairing
            (localFixedSignMetric period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate)
            (localCovariantScalarJet period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch direction coordinate)
            (localCovariantScalarJet period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch direction coordinate) := by
  unfold localStandardConformalScalarCurvatureCorrection
  dsimp only
  rw [localCovariantScalarWave_spatialConformalExponentialScale,
    localCovariantScalarGradientPairing_spatialConformalExponentialScale]
  have hScaleNe :
      localScalarRepresentative period hPeriod
        (spatialConformalExponentialScale
          period hPeriod direction parameter) patch coordinate ≠ 0 := by
    rw [localScalarRepresentative_spatialConformalExponentialScale]
    exact Real.exp_ne_zero _
  field_simp [hScaleNe]
  ring

theorem localScalarCurvature_spatialConformalExponentialScale
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localScalarCurvature period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod
          (spatialConformalExponentialScale
            period hPeriod direction parameter)
          (spatialConformalExponentialScale_pos
            period hPeriod direction parameter))
        patch coordinate =
      Real.exp (-2 * parameter *
          localScalarRepresentative period hPeriod direction patch coordinate) *
        (localScalarCurvature period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate -
          6 * parameter *
            covariantScalarJetWave
              (localFixedSignMetric period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch coordinate)
              (localCovariantScalarJet period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch direction coordinate) -
          6 * parameter ^ 2 *
            covariantScalarGradientPairing
              (localFixedSignMetric period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch coordinate)
              (localCovariantScalarJet period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch direction coordinate)
              (localCovariantScalarJet period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch direction coordinate)) := by
  rw [localScalarCurvature_conformal_standard,
    localStandardConformalScalarCurvatureCorrection_spatialConformalExponentialScale,
    localScalarRepresentative_spatialConformalExponentialScale,
    ← Real.exp_neg]
  ring

theorem globalScalarCurvature_spatialConformalExponentialScale
    (direction : SmoothScalarField period hPeriod)
    (parameter : Real)
    (point : EffectiveQuotient period hPeriod) :
    globalScalarCurvature period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod
          (spatialConformalExponentialScale
            period hPeriod direction parameter)
          (spatialConformalExponentialScale_pos
            period hPeriod direction parameter))
        point =
      Real.exp (-2 * parameter * direction point) *
        (globalScalarCurvature period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) point -
          6 * parameter *
            canonicalGlobalSmoothScalarWave period hPeriod direction point -
          6 * parameter ^ 2 *
            canonicalGlobalScalarGradientPairing
              period hPeriod direction direction point) := by
  let witness := selectedScalarCurvatureChart period hPeriod point
  have hDirection :
      direction point =
        localScalarRepresentative period hPeriod direction
          witness.patch witness.coordinate := by
    change direction point =
      direction (witness.patch.coordinateMap witness.coordinate)
    rw [witness.coordinateMap_eq]
  have hWave :
      canonicalGlobalSmoothScalarWave period hPeriod direction point =
        canonicalPhysicalScalarWaveAtlasRepresentative period hPeriod direction
          witness.patch witness.coordinate := by
    calc
      canonicalGlobalSmoothScalarWave period hPeriod direction point =
          canonicalGlobalSmoothScalarWave period hPeriod direction
            (witness.patch.coordinateMap witness.coordinate) :=
        congrArg (canonicalGlobalSmoothScalarWave period hPeriod direction)
          witness.coordinateMap_eq.symm
      _ = _ := canonicalGlobalSmoothScalarWave_eq_local
        period hPeriod direction witness.patch witness.coordinate
  have hPairing :
      canonicalGlobalScalarGradientPairing
          period hPeriod direction direction point =
        covariantScalarGradientPairing
          (localFixedSignMetric period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            witness.patch witness.coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            witness.patch direction witness.coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            witness.patch direction witness.coordinate) := by
    calc
      canonicalGlobalScalarGradientPairing
          period hPeriod direction direction point =
        canonicalGlobalScalarGradientPairing period hPeriod direction direction
          (witness.patch.coordinateMap witness.coordinate) :=
        congrArg
          (canonicalGlobalScalarGradientPairing
            period hPeriod direction direction)
          witness.coordinateMap_eq.symm
      _ = _ := canonicalGlobalScalarGradientPairing_eq_local
        period hPeriod direction direction witness.patch witness.coordinate
  change
    localScalarCurvature period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod
          (spatialConformalExponentialScale
            period hPeriod direction parameter)
          (spatialConformalExponentialScale_pos
            period hPeriod direction parameter))
        witness.patch witness.coordinate =
      Real.exp (-2 * parameter * direction point) *
        (localScalarCurvature period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            witness.patch witness.coordinate -
          6 * parameter *
            canonicalGlobalSmoothScalarWave period hPeriod direction point -
          6 * parameter ^ 2 *
            canonicalGlobalScalarGradientPairing
              period hPeriod direction direction point)
  rw [hDirection, hWave, hPairing]
  exact localScalarCurvature_spatialConformalExponentialScale
    period hPeriod direction parameter witness.patch witness.coordinate

end

end P0EFTJanusMappingTorusSpatialConformalExponentialCurvature4D
end JanusFormal
