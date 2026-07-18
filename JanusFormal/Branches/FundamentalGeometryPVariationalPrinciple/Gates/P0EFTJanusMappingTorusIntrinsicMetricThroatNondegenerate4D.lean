import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D

/-!
# Nondegenerate intrinsic metric on the effective throat

The explicit unit normal splits every ambient tangent into a throat tangent
and a metric-orthogonal normal component.  Ambient nondegeneracy therefore
implies nondegeneracy of the intrinsic metric restricted to the throat.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D

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
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionLocal4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

private local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

private local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

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

private abbrev AmbientTangent (point : EffectiveThroat period hPeriod) :=
  TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)

private abbrev TangentialRange (point : EffectiveThroat period hPeriod) :
    Submodule Real (AmbientTangent period hPeriod point) :=
  LinearMap.range
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap

/-- The actual intrinsic Lorentz metric has no tangential radical along the
effective throat. -/
theorem intrinsicSmoothGeneralLorentzMetric_hasNoTangentialRadical :
    HasNoTangentialRadical period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) := by
  intro point first hRadical
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (throatData period hPeriod) point
  let throatPoint :=
    mappingTorusMk (throatData period hPeriod) anchor
  let ambientPoint :=
    fixedThroatQuotientInclusion period hPeriod throatPoint
  let derivative :=
    mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) throatPoint
  have hFlatZero :
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          ambientPoint (derivative first) = 0 := by
    apply ContinuousLinearMap.ext
    intro ambient
    let normalClass : DifferentialNormalFiber period hPeriod throatPoint :=
      (TangentialRange period hPeriod throatPoint).mkQ ambient
    let normalLift := canonicalLocalOrthogonalNormalLift
      period hPeriod anchor normalClass
    have hRepresents := canonicalLocalOrthogonalNormalLift_represents
      period hPeriod anchor normalClass
    have hDifferenceZero :
        (TangentialRange period hPeriod throatPoint).mkQ
            (ambient - normalLift) = 0 := by
      rw [map_sub, hRepresents]
      simp [normalClass]
    have hDifferenceMem : ambient - normalLift ∈
        TangentialRange period hPeriod throatPoint :=
      (Submodule.Quotient.mk_eq_zero
        (TangentialRange period hPeriod throatPoint)).mp hDifferenceZero
    obtain ⟨tangent, hTangent⟩ := hDifferenceMem
    have hTangent' : derivative tangent = ambient - normalLift := by
      exact hTangent
    have hDecomposition : ambient = derivative tangent + normalLift := by
      rw [hTangent']
      exact (sub_add_cancel ambient normalLift).symm
    have hNormal := canonicalLocalOrthogonalNormalLift_orthogonal
      period hPeriod anchor normalClass first
    have hNormal' :
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
            ambientPoint (derivative first) normalLift = 0 := by
      rw [(intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.symmetric]
      exact hNormal
    rw [hDecomposition, map_add]
    change
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          ambientPoint (derivative first) (derivative tangent) +
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          ambientPoint (derivative first) normalLift = 0
    rw [hRadical tangent, hNormal']
    exact zero_add 0
  have hDerivativeZero : derivative first = 0 := by
    apply metric_nondegenerate_at period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) ambientPoint
    simpa using hFlatZero
  apply mfderiv_fixedThroatQuotientInclusion_injective
    period hPeriod throatPoint
  simpa using hDerivativeZero

/-- Consequently the genuine intrinsic metric restricts to a nondegenerate
smooth symmetric metric on the effective throat. -/
theorem intrinsicGeneralLorentzMetricThroatTrace_nondegenerate :
    ThroatTensorIsNondegenerate period hPeriod
      (generalLorentzMetricThroatTrace period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)) :=
  (throatTrace_nondegenerate_iff_no_tangential_radical period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)).2
      (intrinsicSmoothGeneralLorentzMetric_hasNoTangentialRadical
        period hPeriod)

/-- The intrinsic restriction packaged on the nondegenerate throat-metric
domain. -/
def intrinsicSmoothNondegenerateThroatMetric :
    SmoothNondegenerateThroatMetric period hPeriod :=
  generalLorentzMetricNondegenerateThroatTrace period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
    (intrinsicSmoothGeneralLorentzMetric_hasNoTangentialRadical
      period hPeriod)

end

end P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
end JanusFormal
