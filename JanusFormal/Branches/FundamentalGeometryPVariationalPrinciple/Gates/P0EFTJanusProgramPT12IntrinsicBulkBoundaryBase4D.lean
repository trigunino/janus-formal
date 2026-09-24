import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

/-! The intrinsic bulk geometry supplies the actual non-null boundary datum at zero displacement
parameter, retaining the existing two-sheet GHY action and arbitrary coupling. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkBoundaryBase4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

theorem intrinsicBulkGeometry_plusMetric_tensor (point : EffectiveQuotient period hPeriod) :
    (intrinsicBulkGeometry period hPeriod).plusMetric.tensor.tensor point =
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point := by
  change (1 : Real) • (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point = _
  exact one_smul Real _

theorem intrinsicBulkGeometry_plusMetric_hasNoTangentialRadical :
    HasNoTangentialRadical period hPeriod (intrinsicBulkGeometry period hPeriod).plusMetric := by
  intro point first hRadical
  apply intrinsicSmoothGeneralLorentzMetric_hasNoTangentialRadical period hPeriod point first
  intro second
  have h := hRadical second
  rw [intrinsicBulkGeometry_plusMetric_tensor] at h
  exact h

variable (displacement : SmoothNormalDisplacement period hPeriod)

theorem intrinsicBulkNonNullDomain_isOpen :
    IsOpen (normalGraphNonNullDomain period hPeriod
      (intrinsicBulkGeometry period hPeriod).plusMetric displacement) :=
  normalGraphNonNullDomain_isOpen period hPeriod
    (intrinsicBulkGeometry period hPeriod).plusMetric displacement

theorem intrinsicBulkNonNullDomain_zero_mem :
    0 ∈ normalGraphNonNullDomain period hPeriod
      (intrinsicBulkGeometry period hPeriod).plusMetric displacement :=
  zero_mem_normalGraphNonNullDomain period hPeriod
    (intrinsicBulkGeometry period hPeriod).plusMetric displacement
    (intrinsicBulkGeometry_plusMetric_hasNoTangentialRadical period hPeriod)

theorem intrinsicBulkNonNullDomain_mem_nhds :
    normalGraphNonNullDomain period hPeriod
      (intrinsicBulkGeometry period hPeriod).plusMetric displacement ∈ 𝓝 (0 : Real) :=
  (intrinsicBulkNonNullDomain_isOpen period hPeriod displacement).mem_nhds
    (intrinsicBulkNonNullDomain_zero_mem period hPeriod displacement)

/-- The existing canonical two-sheet boundary datum for this same bulk metric. -/
def intrinsicBulkBoundaryBase {NonNullFace : Type*} [Fintype NonNullFace]
    (einsteinScale : Real) : GlobalCandidateANonNullBoundaryDatum period hPeriod NonNullFace :=
  normalGraphCanonicalCandidateANonNullBoundaryDatum period hPeriod einsteinScale
    (intrinsicBulkGeometry period hPeriod).plusMetric displacement 0
    (intrinsicBulkNonNullDomain_zero_mem period hPeriod displacement)

theorem intrinsicBulkBoundaryBase_action_eq_ghy
    {NonNullFace : Type*} [Fintype NonNullFace] (einsteinScale : Real) :
    globalCandidateANonNullBoundaryAction period hPeriod
        (intrinsicBulkBoundaryBase period hPeriod displacement
          (NonNullFace := NonNullFace) einsteinScale) =
      normalGraphCanonicalTwoSheetGaussGHYAction period hPeriod einsteinScale
        (intrinsicBulkGeometry period hPeriod).plusMetric displacement 0
        (intrinsicBulkNonNullDomain_zero_mem period hPeriod displacement) :=
  globalCandidateANonNullBoundaryAction_normalGraph_eq period hPeriod einsteinScale
    (intrinsicBulkGeometry period hPeriod).plusMetric displacement 0
    (intrinsicBulkNonNullDomain_zero_mem period hPeriod displacement)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkBoundaryBase4D
