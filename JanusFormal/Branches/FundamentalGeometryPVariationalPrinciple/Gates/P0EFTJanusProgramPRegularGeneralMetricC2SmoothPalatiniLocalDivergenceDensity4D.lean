import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalMetricVolumeChristoffelTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalBoxStokes4D

/-! # Holonomic divergence density of the smooth Palatini current -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalDivergenceDensity4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusLocalMetricVolumeChristoffelTrace4D
open P0EFTJanusProgramPRegularGeneralMetricC2PalatiniGlobalVector4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalBoxStokes4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Holonomic formula for the covariant divergence of the genuine Palatini
vector. -/
def regularGeneralMetricC2PalatiniLocalCovariantDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  (∑ derivative : Index4,
      fderiv Real
        (regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric tensor
          patch) coordinate (Pi.single derivative 1) derivative) +
    ∑ vector : Index4,
      (∑ contracted : Index4,
        localLeviCivitaChristoffel period hPeriod metric.metric patch coordinate
          contracted contracted vector) *
        regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric tensor
          patch coordinate vector

/-- Coordinate product rule: the ordinary divergence of `sqrt(|det g|) V`
is the metric volume times the holonomic covariant divergence of `V`. -/
theorem regularGeneralMetricC2DensitizedPalatiniLocalDivergence_eq_volume_mul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularGeneralMetricC2DensitizedPalatiniLocalDivergence period hPeriod
        metric tensor patch coordinate =
      localMetricVolumeFactor period hPeriod metric.metric patch coordinate *
        regularGeneralMetricC2PalatiniLocalCovariantDivergence period hPeriod
          metric tensor patch coordinate := by
  let volume := localMetricVolumeFactor period hPeriod metric.metric patch
  let vector := regularGeneralMetricC2PalatiniVectorLocal period hPeriod metric
    tensor patch
  let christoffel :=
    localLeviCivitaChristoffel period hPeriod metric.metric patch coordinate
  have hVolume : DifferentiableAt Real volume coordinate :=
    (localMetricVolumeFactor_contDiff period hPeriod metric.metric patch
      ).differentiable (by simp) coordinate
  have hVector : DifferentiableAt Real vector coordinate :=
    (regularGeneralMetricC2PalatiniVectorLocal_contDiff period hPeriod metric
      tensor patch).differentiable (by simp) coordinate
  have hDerivative (derivative : Index4) :
      fderiv Real (fun current => volume current • vector current) coordinate
          (Pi.single derivative 1) derivative =
        volume coordinate *
            fderiv Real vector coordinate (Pi.single derivative 1) derivative +
          fderiv Real volume coordinate (Pi.single derivative 1) *
            vector coordinate derivative := by
    change
      fderiv Real (volume • vector) coordinate (Pi.single derivative 1)
          derivative = _
    have hProduct := fderiv_smul hVolume hVector
    have hApplied := congrArg
      (fun derivativeMap : Vector4 →L[Real] Vector4 =>
        derivativeMap (Pi.single derivative 1)) hProduct
    have hComponent := congrArg (fun value : Vector4 => value derivative)
      hApplied
    simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hComponent
  have hVolumeDerivative (derivative : Index4) :
      fderiv Real volume coordinate (Pi.single derivative 1) =
        volume coordinate *
          ∑ contracted : Index4, christoffel contracted derivative contracted :=
    localMetricVolumeFactor_fderiv_basis_eq_christoffelTrace period hPeriod
      metric.metric patch coordinate derivative
  have hTorsion (upper first second : Index4) :
      christoffel upper first second = christoffel upper second first := by
    exact
      (localLeviCivitaConnectionJet period hPeriod metric.metric patch coordinate
        ).torsionFree upper first second
  have hConnection :
      (∑ derivative : Index4,
          (∑ contracted : Index4,
            christoffel contracted derivative contracted) *
              vector coordinate derivative) =
        ∑ vectorIndex : Index4,
          (∑ contracted : Index4,
            christoffel contracted contracted vectorIndex) *
              vector coordinate vectorIndex := by
    apply Finset.sum_congr rfl
    intro derivative _
    apply congrArg (· * vector coordinate derivative)
    apply Finset.sum_congr rfl
    intro contracted _
    exact hTorsion contracted derivative contracted
  unfold regularGeneralMetricC2DensitizedPalatiniLocalDivergence
    regularGeneralMetricC2DensitizedPalatiniLocalCurrent
    regularGeneralMetricC2PalatiniLocalCovariantDivergence
  change
    (∑ derivative : Index4,
      fderiv Real (fun current => volume current • vector current) coordinate
        (Pi.single derivative 1) derivative) =
      volume coordinate *
        ((∑ derivative : Index4,
          fderiv Real vector coordinate (Pi.single derivative 1) derivative) +
        ∑ vectorIndex : Index4,
          (∑ contracted : Index4,
            christoffel contracted contracted vectorIndex) *
              vector coordinate vectorIndex)
  simp_rw [hDerivative, hVolumeDerivative]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  calc
    volume coordinate *
          (∑ derivative : Index4,
            fderiv Real vector coordinate (Pi.single derivative 1)
              derivative) +
        ∑ derivative : Index4,
          (volume coordinate *
              ∑ contracted : Index4,
                christoffel contracted derivative contracted) *
            vector coordinate derivative =
      volume coordinate *
          (∑ derivative : Index4,
            fderiv Real vector coordinate (Pi.single derivative 1)
              derivative) +
        volume coordinate *
          ∑ derivative : Index4,
            (∑ contracted : Index4,
              christoffel contracted derivative contracted) *
                vector coordinate derivative := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro derivative _
      ring
    _ = volume coordinate *
          (∑ derivative : Index4,
            fderiv Real vector coordinate (Pi.single derivative 1)
              derivative) +
        volume coordinate *
          ∑ vectorIndex : Index4,
            (∑ contracted : Index4,
              christoffel contracted contracted vectorIndex) *
                vector coordinate vectorIndex := by
      rw [hConnection]
    _ = _ := by ring

/-- Gate marker for the exact density/covariant-divergence bridge. -/
theorem regular_general_metric_c2_smooth_palatini_local_divergence_density_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularGeneralMetricC2DensitizedPalatiniLocalDivergence period hPeriod
        metric tensor patch coordinate =
      localMetricVolumeFactor period hPeriod metric.metric patch coordinate *
        regularGeneralMetricC2PalatiniLocalCovariantDivergence period hPeriod
          metric tensor patch coordinate :=
  regularGeneralMetricC2DensitizedPalatiniLocalDivergence_eq_volume_mul
    period hPeriod metric tensor patch coordinate

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniLocalDivergenceDensity4D
end JanusFormal
