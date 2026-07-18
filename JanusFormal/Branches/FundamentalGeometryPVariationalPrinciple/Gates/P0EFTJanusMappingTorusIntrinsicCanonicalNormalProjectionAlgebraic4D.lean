import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothThroatEmbedding

/-!
# Canonical algebraic normal projection for the intrinsic D8 throat

This gate constructs the latitude normal in the actual tangent fibers and
starts the metric-normal projection independently of the transported normal
bundle topology.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Set Topology Bundle Module
open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)

private local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

private local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

private abbrev CoverTangent (point : EffectiveCover period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- Tangent of the explicit latitude curve at the equator. -/
def coverLatitudeNormalVector
    (anchor : EffectiveThroatCover period hPeriod) :
    CoverTangent period hPeriod
      (fixedThroatCoverInclusion period hPeriod anchor) := by
  simpa only [normalLatitudeCover_zero] using
    (mfderiv 𝓘(Real, Real) coverModelWithCorners
      (normalLatitudeCover period hPeriod anchor) 0 1)

def rawLatitudeDerivative :
    Real →L[Real] (Fin 4 → Real) :=
  ContinuousLinearMap.pi fun index =>
    Fin.cases (ContinuousLinearMap.toSpanSingleton Real 1)
      (fun _ => 0) index

def latitudeAmbientDerivative :
    Real →L[Real] (EuclideanR4 × Real) :=
  ((EuclideanSpace.equiv (Fin 4) Real).symm.toContinuousLinearMap.comp
      rawLatitudeDerivative).prod 0

theorem rawLatitude_hasFDerivAt
    (point : EquatorialTwoSphere) :
    HasFDerivAt (fun normal => (equatorialLatitude point normal).1)
      rawLatitudeDerivative 0 := by
  unfold rawLatitudeDerivative
  rw [hasFDerivAt_pi]
  intro index
  refine Fin.cases ?_ (fun tail => ?_) index
  · simpa [equatorialLatitude] using (Real.hasDerivAt_sin 0).hasFDerivAt
  · simpa [equatorialLatitude] using
      ((Real.hasDerivAt_cos 0).mul_const
        (point.1 tail.succ)).hasFDerivAt

theorem latitudeAmbient_hasFDerivAt
    (point : EquatorialTwoSphere) (time : Real) :
    HasFDerivAt
      (fun normal =>
        ((unitThreeSphereHomeomorph
            (equatorialLatitude point normal)).1, time))
      latitudeAmbientDerivative 0 := by
  have hEuclidean :=
    (EuclideanSpace.equiv (Fin 4) Real).symm.toContinuousLinearMap.hasFDerivAt.comp
      0 (rawLatitude_hasFDerivAt point)
  exact hEuclidean.prodMk (hasFDerivAt_const (x := 0) (c := time))

theorem latitudeAmbientDerivative_one :
    latitudeAmbientDerivative 1 =
      (EuclideanSpace.single (0 : Fin 4) 1, 0) := by
  apply Prod.ext
  · apply (EuclideanSpace.equiv (Fin 4) Real).injective
    funext index
    refine Fin.cases ?_ (fun tail => ?_) index <;>
      simp [latitudeAmbientDerivative, rawLatitudeDerivative]
  · simp [latitudeAmbientDerivative]

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D
end JanusFormal
