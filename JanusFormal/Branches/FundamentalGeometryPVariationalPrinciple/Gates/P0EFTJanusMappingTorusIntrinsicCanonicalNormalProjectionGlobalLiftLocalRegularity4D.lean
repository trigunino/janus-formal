import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftContinuity4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusDifferentialNormalSmoothBundleIsomorphism
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D

/-!
# Local regularity of the canonical global normal lift

The transported differential-normal charts use the preferred latitude-normal
equivalence.  Its unit generator has intrinsic Lorentz square one, while every
transition function is a sign.  Hence the global metric square is exactly
`scalar²` in every local chart.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftLocalRegularity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000

noncomputable section

open Set Topology Bundle Module
open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle
open P0EFTJanusMappingTorusDifferentialNormalSmoothBundleIsomorphism
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftChoice4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftContinuity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

private local instance throatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance throatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance quotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

/-- Fiberwise specialization of the global metric square. -/
def canonicalGlobalNormalMetricSquareAt
    (point : EffectiveThroat period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point) : Real :=
  canonicalGlobalNormalMetricSquare period hPeriod
    (⟨point, normal⟩ : DifferentialNormalTotalSpace period hPeriod)

/-- At a point presented by a cover anchor, the global square is exactly the
square of the explicit canonical local normal coordinate. -/
theorem canonicalGlobalNormalMetricSquareAt_eq_local
    (anchor : EffectiveThroatCover period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod
      (mappingTorusMk (throatData period hPeriod) anchor)) :
    canonicalGlobalNormalMetricSquareAt period hPeriod
        (mappingTorusMk (throatData period hPeriod) anchor) normal =
      ((canonicalLocalNormalClassEquiv period hPeriod anchor).symm normal) ^ 2 := by
  unfold canonicalGlobalNormalMetricSquareAt canonicalGlobalNormalMetricSquare
  rw [canonicalGlobalOrthogonalNormalLift_eq_fromAnchor period hPeriod
    anchor (mappingTorusMk (throatData period hPeriod) anchor) rfl]
  change
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod
          (mappingTorusMk (throatData period hPeriod) anchor))
        (canonicalLocalOrthogonalNormalLift period hPeriod anchor normal)
        (canonicalLocalOrthogonalNormalLift period hPeriod anchor normal) =
      ((canonicalLocalNormalClassEquiv period hPeriod anchor).symm normal) ^ 2
  exact canonicalLocalOrthogonalNormalLift_square
    period hPeriod anchor normal

private theorem canonicalGlobalNormalMetricSquareAt_smul_fromAnchor
    (anchor : EffectiveThroatCover period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod
      (mappingTorusMk (throatData period hPeriod) anchor))
    (scalar : Real) :
    canonicalGlobalNormalMetricSquareAt period hPeriod
        (mappingTorusMk (throatData period hPeriod) anchor) (scalar • normal) =
      scalar ^ 2 * canonicalGlobalNormalMetricSquareAt period hPeriod
        (mappingTorusMk (throatData period hPeriod) anchor) normal := by
  rw [canonicalGlobalNormalMetricSquareAt_eq_local,
    canonicalGlobalNormalMetricSquareAt_eq_local, map_smul]
  simp only [smul_eq_mul]
  ring

private theorem canonicalGlobalNormalMetricSquareAt_smul_ofAnchor
    (anchor : EffectiveThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hPoint : mappingTorusMk (throatData period hPeriod) anchor = point)
    (normal : DifferentialNormalFiber period hPeriod point)
    (scalar : Real) :
    canonicalGlobalNormalMetricSquareAt period hPeriod point
        (scalar • normal) =
      scalar ^ 2 * canonicalGlobalNormalMetricSquareAt
        period hPeriod point normal := by
  cases hPoint
  exact canonicalGlobalNormalMetricSquareAt_smul_fromAnchor
    period hPeriod anchor normal scalar

/-- The chosen global square is homogeneous of degree two on every fiber. -/
theorem canonicalGlobalNormalMetricSquareAt_smul
    (point : EffectiveThroat period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point)
    (scalar : Real) :
    canonicalGlobalNormalMetricSquareAt period hPeriod point
        (scalar • normal) =
      scalar ^ 2 * canonicalGlobalNormalMetricSquareAt
        period hPeriod point normal := by
  let anchor := normalBundleIndexAt period hPeriod point
  have hPoint : mappingTorusMk (throatData period hPeriod) anchor = point :=
    normalBundleIndexAt_projects period hPeriod point
  exact canonicalGlobalNormalMetricSquareAt_smul_ofAnchor
    period hPeriod anchor point hPoint normal scalar

private theorem canonicalGlobalNormalMetricSquareAt_fiberEquiv_ofAnchor
    (anchor : EffectiveThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hPoint : mappingTorusMk (throatData period hPeriod) anchor = point)
    (scalar : Real) :
    canonicalGlobalNormalMetricSquareAt period hPeriod point
        (differentialNormalFiberTransport period hPeriod hPoint
          (canonicalDifferentialNormalClassEquiv period hPeriod anchor scalar)) =
      scalar ^ 2 := by
  cases hPoint
  change
    canonicalGlobalNormalMetricSquareAt period hPeriod
        (mappingTorusMk (throatData period hPeriod) anchor)
        (canonicalDifferentialNormalClassEquiv period hPeriod anchor scalar) =
      scalar ^ 2
  rw [canonicalGlobalNormalMetricSquareAt_eq_local]
  change
    ((canonicalLocalNormalClassEquiv period hPeriod anchor).symm
        (canonicalLocalNormalClassEquiv period hPeriod anchor scalar)) ^ 2 =
      scalar ^ 2
  rw [(canonicalLocalNormalClassEquiv period hPeriod anchor).symm_apply_apply]

/-- The preferred fiber equivalence is normalized by the unit latitude normal. -/
private theorem canonicalGlobalNormalMetricSquareAt_fiberEquiv
    (point : EffectiveThroat period hPeriod) (scalar : Real) :
    canonicalGlobalNormalMetricSquareAt period hPeriod point
        (differentialNormalFiberEquiv period hPeriod point scalar) =
      scalar ^ 2 := by
  rw [differentialNormalFiberEquiv_apply]
  exact canonicalGlobalNormalMetricSquareAt_fiberEquiv_ofAnchor
    period hPeriod (normalBundleIndexAt period hPeriod point) point
      (normalBundleIndexAt_projects period hPeriod point) scalar

/-- Every sign-clutched coordinate transition preserves the scalar square. -/
private theorem normalCoordChange_sq
    (first second : EffectiveThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod) (scalar : Real) :
    ((fixedThroatNormalVectorBundleCore period hPeriod).coordChange
        first second point scalar) ^ 2 = scalar ^ 2 := by
  change
    (((normalSignRepresentation
        (localTransitionWinding period hPeriod first second point) : Real) *
      scalar) ^ 2) = scalar ^ 2
  by_cases hEven : Even
      (localTransitionWinding period hPeriod first second point)
  · rw [normal_sign_even _ hEven]
    simp
  · rw [normal_sign_odd _ hEven]
    norm_num

private theorem canonicalGlobalNormalMetricSquare_mk
    (point : EffectiveThroat period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point) :
    canonicalGlobalNormalMetricSquare period hPeriod
        (⟨point, normal⟩ : DifferentialNormalTotalSpace period hPeriod) =
      canonicalGlobalNormalMetricSquareAt period hPeriod point normal := by
  rfl

private theorem canonicalGlobalNormalMetricSquareInChart_apply
    (anchor : EffectiveThroatCover period hPeriod)
    (parameter : EffectiveThroat period hPeriod × Real) :
    canonicalGlobalNormalMetricSquareInChart period hPeriod anchor parameter =
      canonicalGlobalNormalMetricSquare period hPeriod
        ((differentialNormalLocalTriv period hPeriod anchor).toOpenPartialHomeomorph.symm
          parameter) := by
  rfl

private theorem canonicalGlobalNormalMetricSquare_congr
    {first second : DifferentialNormalTotalSpace period hPeriod}
    (h : first = second) :
    canonicalGlobalNormalMetricSquare period hPeriod first =
      canonicalGlobalNormalMetricSquare period hPeriod second :=
  congrArg (canonicalGlobalNormalMetricSquare period hPeriod) h

private theorem canonicalGlobalNormalMetricSquareInChart_eq_squareAt
    (anchor : EffectiveThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod) (scalar : Real) :
    canonicalGlobalNormalMetricSquareInChart period hPeriod anchor
        ⟨point, scalar⟩ =
      canonicalGlobalNormalMetricSquareAt period hPeriod point
        (differentialNormalFiberEquiv period hPeriod point
          ((fixedThroatNormalVectorBundleCore period hPeriod).coordChange
            anchor (normalBundleIndexAt period hPeriod point) point scalar)) := by
  calc
    _ = canonicalGlobalNormalMetricSquare period hPeriod
          ((differentialNormalLocalTriv period hPeriod anchor).toOpenPartialHomeomorph.symm
            ⟨point, scalar⟩) :=
      canonicalGlobalNormalMetricSquareInChart_apply
        period hPeriod anchor ⟨point, scalar⟩
    _ = canonicalGlobalNormalMetricSquare period hPeriod
          (⟨point, differentialNormalFiberEquiv period hPeriod point
            ((fixedThroatNormalVectorBundleCore period hPeriod).coordChange
              anchor (normalBundleIndexAt period hPeriod point) point scalar)⟩ :
            DifferentialNormalTotalSpace period hPeriod) :=
      canonicalGlobalNormalMetricSquare_congr period hPeriod
        (differentialNormalLocalTriv_symm_fst
          period hPeriod anchor point scalar)
    _ = _ := canonicalGlobalNormalMetricSquare_mk period hPeriod point _

/-- In every transported differential-normal chart, the canonical global
metric square is exactly the square of the fiber coordinate. -/
theorem canonicalGlobalNormalMetricSquareInChart_eq_sq
    (anchor : EffectiveThroatCover period hPeriod)
    (parameter : EffectiveThroat period hPeriod × Real)
    (_hParameter : parameter ∈
      (differentialNormalLocalTriv period hPeriod anchor).target) :
    canonicalGlobalNormalMetricSquareInChart period hPeriod anchor parameter =
      parameter.2 ^ 2 := by
  rcases parameter with ⟨point, scalar⟩
  rw [canonicalGlobalNormalMetricSquareInChart_eq_squareAt]
  rw [canonicalGlobalNormalMetricSquareAt_fiberEquiv]
  exact normalCoordChange_sq period hPeriod anchor
    (normalBundleIndexAt period hPeriod point) point scalar

/-- The exact local regularity contract now follows unconditionally. -/
theorem canonicalGlobalNormalMetricSquareLocalRegularity :
    CanonicalGlobalNormalMetricSquareLocalRegularity period hPeriod := by
  intro anchor
  apply ContinuousOn.congr (continuous_snd.pow 2).continuousOn
  intro parameter hParameter
  exact canonicalGlobalNormalMetricSquareInChart_eq_sq
    period hPeriod anchor parameter hParameter

end

end P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftLocalRegularity4D
end JanusFormal
