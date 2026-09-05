import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhasedNormalRotationSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusInvariantMeasureFlowIPP4D

/-! # Integration by parts for canonical volume-preserving quotient flows -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalVolumePreservingFlowIPP4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set Topology MeasureTheory Bundle
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusInvariantMeasureFlowIPP4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- A complete smooth real action preserving the actual canonical volume. -/
structure CanonicalVolumePreservingFlow where
  flow : Real → EffectiveQuotient period hPeriod →
    EffectiveQuotient period hPeriod
  joint_contMDiff : ContMDiff
    (𝓘(Real, Real).prod coverModelWithCorners) coverModelWithCorners ∞
    (Function.uncurry flow)
  flow_zero : ∀ point, flow 0 point = point
  flow_add : ∀ first second point,
    flow (first + second) point = flow first (flow second point)
  flow_embedding : ∀ parameter, MeasurableEmbedding (flow parameter)
  measurePreserving : ∀ parameter,
    MeasurePreserving (flow parameter)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

private def canonicalFlowInputBundle
    (point : EffectiveQuotient period hPeriod) :
    TangentBundle (𝓘(Real, Real).prod coverModelWithCorners)
      (Real × EffectiveQuotient period hPeriod) :=
  (equivTangentBundleProd 𝓘(Real, Real) Real coverModelWithCorners
      (EffectiveQuotient period hPeriod)).symm
    (⟨0, 1⟩, ⟨point, 0⟩)

@[simp]
private theorem canonicalFlowInputBundle_eq
    (point : EffectiveQuotient period hPeriod) :
    canonicalFlowInputBundle period hPeriod point =
      (⟨(0, point), (1, 0)⟩ :
        TangentBundle (𝓘(Real, Real).prod coverModelWithCorners)
          (Real × EffectiveQuotient period hPeriod)) :=
  rfl

private theorem canonicalFlowInputBundle_contMDiff :
    ContMDiff coverModelWithCorners
      (𝓘(Real, Real).prod coverModelWithCorners).tangent ∞
      (canonicalFlowInputBundle period hPeriod) := by
  apply (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(Real, Real)) (I' := coverModelWithCorners)
    (M := Real) (M' := EffectiveQuotient period hPeriod)).comp
  exact contMDiff_const.prodMk
    (Bundle.contMDiff_zeroSection (n := ∞) Real
      (TangentSpace coverModelWithCorners :
        EffectiveQuotient period hPeriod → Type _))

private def rawCanonicalFlowGeneratorBundle
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod) :=
  tangentMap (𝓘(Real, Real).prod coverModelWithCorners)
    coverModelWithCorners (Function.uncurry data.flow)
    (canonicalFlowInputBundle period hPeriod point)

private theorem rawCanonicalFlowGeneratorBundle_contMDiff
    (data : CanonicalVolumePreservingFlow period hPeriod) :
    ContMDiff coverModelWithCorners coverModelWithCorners.tangent ∞
      (rawCanonicalFlowGeneratorBundle period hPeriod data) :=
  (data.joint_contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp
    (canonicalFlowInputBundle_contMDiff period hPeriod)

private theorem rawCanonicalFlowGeneratorBundle_base
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (rawCanonicalFlowGeneratorBundle period hPeriod data point).1 = point := by
  simpa [rawCanonicalFlowGeneratorBundle, canonicalFlowInputBundle, tangentMap]
    using data.flow_zero point

/-- Intrinsic infinitesimal generator of a canonical invariant flow. -/
def canonicalFlowGenerator
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TangentSpace coverModelWithCorners point :=
  (rawCanonicalFlowGeneratorBundle_base period hPeriod data point) ▸
    (rawCanonicalFlowGeneratorBundle period hPeriod data point).2

private theorem canonicalFlowGenerator_bundle
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (⟨point, canonicalFlowGenerator period hPeriod data point⟩ :
        TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod)) =
      rawCanonicalFlowGeneratorBundle period hPeriod data point := by
  let raw := rawCanonicalFlowGeneratorBundle period hPeriod data point
  have hBase : raw.1 = point :=
    rawCanonicalFlowGeneratorBundle_base period hPeriod data point
  change (⟨point, hBase ▸ raw.2⟩ :
      TangentBundle coverModelWithCorners
        (EffectiveQuotient period hPeriod)) = raw
  rcases raw with ⟨base, vector⟩
  simp only at hBase
  subst base
  rfl

theorem canonicalFlowGenerator_contMDiff
    (data : CanonicalVolumePreservingFlow period hPeriod) :
    ContMDiff coverModelWithCorners coverModelWithCorners.tangent ∞
      (fun point =>
        (⟨point, canonicalFlowGenerator period hPeriod data point⟩ :
          TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod))) :=
  (rawCanonicalFlowGeneratorBundle_contMDiff period hPeriod data).congr
    (canonicalFlowGenerator_bundle period hPeriod data)

private def canonicalFlowCurve
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (point : EffectiveQuotient period hPeriod) (parameter : Real) :
    EffectiveQuotient period hPeriod :=
  data.flow parameter point

private theorem canonicalFlowCurve_contMDiff
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    ContMDiff 𝓘(Real, Real) coverModelWithCorners ∞
      (canonicalFlowCurve period hPeriod data point) :=
  data.joint_contMDiff.comp (contMDiff_id.prodMk contMDiff_const)

private theorem rawCanonicalFlowGeneratorBundle_eq_curve
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    rawCanonicalFlowGeneratorBundle period hPeriod data point =
      tangentMap 𝓘(Real, Real) coverModelWithCorners
        (canonicalFlowCurve period hPeriod data point)
        (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real) := by
  let slice : Real → Real × EffectiveQuotient period hPeriod :=
    fun parameter => (parameter, point)
  have hFlowAt : MDifferentiableAt
      (𝓘(Real, Real).prod coverModelWithCorners) coverModelWithCorners
      (Function.uncurry data.flow) (0, point) :=
    data.joint_contMDiff.mdifferentiableAt (by simp)
  have hSliceAt : MDifferentiableAt 𝓘(Real, Real)
      (𝓘(Real, Real).prod coverModelWithCorners) slice 0 :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hComp := tangentMap_comp_at
    (I := 𝓘(Real, Real))
    (I' := 𝓘(Real, Real).prod coverModelWithCorners)
    (I'' := coverModelWithCorners)
    (f := slice) (g := Function.uncurry data.flow)
    (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real)
    hFlowAt hSliceAt
  rw [tangentMap_prod_left] at hComp
  change tangentMap 𝓘(Real, Real) coverModelWithCorners
      (canonicalFlowCurve period hPeriod data point)
      (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real) =
    rawCanonicalFlowGeneratorBundle period hPeriod data point at hComp
  exact hComp.symm

theorem canonicalFlowGenerator_eq_curve_mfderiv
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalFlowGenerator period hPeriod data point =
      mfderiv 𝓘(Real, Real) coverModelWithCorners
        (canonicalFlowCurve period hPeriod data point) 0 1 := by
  apply (TotalSpace.mk_injective (F := CoverCoordinates) (b := point))
  calc
    (⟨point, canonicalFlowGenerator period hPeriod data point⟩ :
        TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod)) =
      rawCanonicalFlowGeneratorBundle period hPeriod data point :=
        canonicalFlowGenerator_bundle period hPeriod data point
    _ = tangentMap 𝓘(Real, Real) coverModelWithCorners
        (canonicalFlowCurve period hPeriod data point)
        (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real) :=
      rawCanonicalFlowGeneratorBundle_eq_curve period hPeriod data point
    _ = (⟨point, mfderiv 𝓘(Real, Real) coverModelWithCorners
          (canonicalFlowCurve period hPeriod data point) 0 1⟩ :
        TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod)) := by
      simp [tangentMap, canonicalFlowCurve, data.flow_zero]
      exact HEq.rfl

universe u

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Directional derivative along the infinitesimal generator of the flow. -/
def canonicalFlowDerivative
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) : Fiber :=
  mvfderiv coverModelWithCorners field.toFun point
    (canonicalFlowGenerator period hPeriod data point)

theorem canonicalFlowDerivative_contMDiff
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (field : SmoothQuotientField period hPeriod Fiber) :
    ContMDiff coverModelWithCorners 𝓘(Real, Fiber) ∞
      (canonicalFlowDerivative period hPeriod Fiber data field) := by
  have hDerivative :=
    (contMDiff_snd_tangentBundle_modelSpace Fiber 𝓘(Real, Fiber)).comp
      ((field.contMDiff_toFun.contMDiff_tangentMap (by simp)).comp
        (canonicalFlowGenerator_contMDiff period hPeriod data))
  convert hDerivative using 1
  rfl

private theorem smoothQuotientField_hasDerivAt_along_curve_zero
    [ContinuousSMul Real Fiber]
    (field : SmoothQuotientField period hPeriod Fiber)
    (curve : Real → EffectiveQuotient period hPeriod)
    (hCurve : ContMDiff 𝓘(Real, Real) coverModelWithCorners ∞ curve) :
    HasDerivAt (fun parameter => field (curve parameter))
      (mvfderiv coverModelWithCorners field.toFun (curve 0)
        (mfderiv 𝓘(Real, Real) coverModelWithCorners curve 0 1)) 0 := by
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real)
      coverModelWithCorners curve 0 :=
    hCurve.mdifferentiableAt (by simp)
  have hFieldAt : MDifferentiableAt coverModelWithCorners
      𝓘(Real, Fiber) field.toFun (curve 0) :=
    field.contMDiff_toFun.mdifferentiableAt (by simp)
  have hComp := hFieldAt.hasMFDerivAt.comp 0 hCurveAt.hasMFDerivAt
  have hCompF : HasFDerivAt (field.toFun ∘ curve)
      ((mfderiv coverModelWithCorners 𝓘(Real, Fiber)
        field.toFun (curve 0)).comp
          (mfderiv 𝓘(Real, Real) coverModelWithCorners curve 0)) 0 :=
    hComp.hasFDerivAt
  have hDeriv : HasDerivAt (field.toFun ∘ curve)
      (((mfderiv coverModelWithCorners 𝓘(Real, Fiber)
        field.toFun (curve 0)).comp
          (mfderiv 𝓘(Real, Real) coverModelWithCorners curve 0)) 1) 0 :=
    hasFDerivAt_iff_hasDerivAt.mp hCompF
  change HasDerivAt (field.toFun ∘ curve) _ 0
  convert hDeriv using 1
  simp only [ContinuousLinearMap.comp_apply]
  rfl

theorem smoothQuotientField_flow_hasDerivAt_zero
    [ContinuousSMul Real Fiber]
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) :
    HasDerivAt (fun parameter => field (data.flow parameter point))
      (canonicalFlowDerivative period hPeriod Fiber data field point) 0 := by
  have h := smoothQuotientField_hasDerivAt_along_curve_zero
    period hPeriod Fiber field
      (canonicalFlowCurve period hPeriod data point)
      (canonicalFlowCurve_contMDiff period hPeriod data point)
  have hCurveZero : canonicalFlowCurve period hPeriod data point 0 = point :=
    data.flow_zero point
  have hVelocity := canonicalFlowGenerator_eq_curve_mfderiv
    period hPeriod data point
  rw [hCurveZero] at h hVelocity
  rw [← hVelocity] at h
  exact h

theorem smoothQuotientField_flow_hasDerivAt
    [ContinuousSMul Real Fiber]
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (field : SmoothQuotientField period hPeriod Fiber)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt (fun t => field (data.flow t point))
      (canonicalFlowDerivative period hPeriod Fiber data field
        (data.flow parameter point)) parameter := by
  have hZero := smoothQuotientField_flow_hasDerivAt_zero
    period hPeriod Fiber data field (data.flow parameter point)
  have hShift : HasDerivAt (fun t : Real => t - parameter) 1 parameter :=
    (hasDerivAt_id parameter).sub_const parameter
  have hComp := hZero.scomp_of_eq parameter hShift (by simp)
  have hEventually :
      (fun t => field (data.flow t point)) =ᶠ[𝓝 parameter]
        ((fun offset => field (data.flow offset (data.flow parameter point))) ∘
          fun t => t - parameter) := by
    filter_upwards with t
    simp only [Function.comp_apply]
    rw [← data.flow_add]
    congr 2
    ring
  exact (hComp.congr_of_eventuallyEq hEventually).congr_deriv
    (one_smul Real _)

/-- Skew-adjoint integration by parts generated by any canonical invariant
flow, with no boundary or Stokes hypothesis. -/
theorem canonicalVolumePreservingFlow_integral_inner_derivative_eq_neg
    {InnerFiber : Type*} [NormedAddCommGroup InnerFiber]
    [InnerProductSpace Real InnerFiber]
    (data : CanonicalVolumePreservingFlow period hPeriod)
    (first second : SmoothQuotientField period hPeriod InnerFiber) :
    (∫ point, inner Real (first point)
        (canonicalFlowDerivative period hPeriod InnerFiber data second point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      -∫ point, inner Real
        (canonicalFlowDerivative period hPeriod InnerFiber data first point)
        (second point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  refine integral_inner_derivative_eq_neg
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    data.flow data.joint_contMDiff.continuous data.flow_zero
    data.flow_embedding data.measurePreserving
    first.toFun second.toFun
    (canonicalFlowDerivative period hPeriod InnerFiber data first)
    (canonicalFlowDerivative period hPeriod InnerFiber data second)
    first.contMDiff_toFun.continuous second.contMDiff_toFun.continuous
    (canonicalFlowDerivative_contMDiff period hPeriod InnerFiber data first).continuous
    (canonicalFlowDerivative_contMDiff period hPeriod InnerFiber data second).continuous
    (smoothQuotientField_flow_hasDerivAt period hPeriod InnerFiber data first)
    (smoothQuotientField_flow_hasDerivAt period hPeriod InnerFiber data second)

end
end P0EFTJanusMappingTorusCanonicalVolumePreservingFlowIPP4D
end JanusFormal
