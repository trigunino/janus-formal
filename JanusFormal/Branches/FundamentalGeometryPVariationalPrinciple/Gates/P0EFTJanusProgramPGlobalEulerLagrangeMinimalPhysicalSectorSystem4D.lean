import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlasRetraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D

/-!
# Minimal-physical Euler sector system

The corrected minimal tangent splits canonically into a bulk tangent with the
legacy ghost/auxiliary directions removed and primitive SpinC matter.  The
minimal-chart Euler equation is exactly the corresponding two-sector system.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlasRetraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- Legacy ghost/auxiliary projection restricted to the non-SpinC bulk
tangent. -/
def globalBulkLegacyNonminimalProjectionLinearMap :
    GeneralMetricMatterFreeVariation period hPeriod →ₗ[Real]
      GlobalLegacyNonminimalDirection period hPeriod where
  toFun := fun variation =>
    (variation.1.1.independent.ghosts,
      variation.1.1.independent.auxiliaries)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Corrected bulk tangent with both obsolete coefficient ghost/auxiliary
directions held fixed. -/
abbrev GlobalMinimalPhysicalBulkTangent :=
  LinearMap.ker (globalBulkLegacyNonminimalProjectionLinearMap period hPeriod)

local instance globalMinimalPhysicalBulkTangentAddCommGroup :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModule :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalTangentAddCommGroup
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

local instance globalMinimalPhysicalTangentModule
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real
      (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

/-- Canonical bulk/SpinC product decomposition of the corrected physical
tangent. -/
def globalMinimalPhysicalTangentSectorEquiv
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration ≃ₗ[Real]
      (GlobalMinimalPhysicalBulkTangent period hPeriod ×
        (Sector → D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter)) where
  toFun := fun variation =>
    (⟨variation.1.1, variation.2⟩, variation.1.2)
  invFun := fun variation =>
    ⟨(variation.1.1, variation.2), variation.1.2⟩
  left_inv variation := by
    apply Subtype.ext
    rfl
  right_inv variation := by
    ext <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identity core bridge upgraded to a genuine linear equivalence between
the canonical minimal tangent and the chart model. -/
def globalCandidateAMinimalPhysicalChartTangentEquiv
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical ≃ₗ[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  LinearEquiv.ofBijective
    (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
      configuration data analysis chartData).tangentAnalysis
    ⟨(globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
        configuration data analysis chartData).tangentAnalysis_injective,
      by
        intro point
        exact ⟨point, rfl⟩⟩

/-- Euler covector of the minimal chart transported to the canonical
bulk/SpinC product. -/
def globalCandidateAMinimalPhysicalSectorEulerCovectorAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    (GlobalMinimalPhysicalBulkTangent period hPeriod ×
        (Sector → D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter)) →ₗ[Real] Real :=
  ((globalCandidateALocalEulerLagrangeOperator period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData) point).toLinearMap.comp
    (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
      configuration data analysis chartData).toLinearMap).comp
    (globalMinimalPhysicalTangentSectorEquiv period hPeriod
      configuration.physical).symm.toLinearMap

/-- Corrected bulk component of the minimal-physical Euler equation. -/
def globalCandidateAMinimalPhysicalBulkEulerCovectorAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    GlobalMinimalPhysicalBulkTangent period hPeriod →ₗ[Real] Real :=
  productCovectorFirst
    (globalCandidateAMinimalPhysicalSectorEulerCovectorAt period hPeriod
      configuration data analysis chartData point)

/-- Primitive SpinC component of the minimal-physical Euler equation. -/
def globalCandidateAMinimalPhysicalSpinCMatterEulerCovectorAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    (Sector → D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter) →ₗ[Real] Real :=
  productCovectorSecond
    (globalCandidateAMinimalPhysicalSectorEulerCovectorAt period hPeriod
      configuration data analysis chartData point)

/-- Minimal-chart Euler vanishing is exactly the corrected bulk and SpinC
sector system, with no equivalence to the obsolete larger tangent. -/
theorem globalCandidateAMinimalPhysicalEuler_eq_zero_iff_sectors
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData) point = 0 ↔
      globalCandidateAMinimalPhysicalBulkEulerCovectorAt period hPeriod
          configuration data analysis chartData point = 0 ∧
        globalCandidateAMinimalPhysicalSpinCMatterEulerCovectorAt period hPeriod
          configuration data analysis chartData point = 0 := by
  let euler := globalCandidateALocalEulerLagrangeOperator period hPeriod
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData) point
  let tangentEquiv := globalCandidateAMinimalPhysicalChartTangentEquiv
    period hPeriod configuration data analysis chartData
  let sectorEquiv := globalMinimalPhysicalTangentSectorEquiv period hPeriod
    configuration.physical
  let canonical := euler.toLinearMap.comp tangentEquiv.toLinearMap
  let sectors := canonical.comp sectorEquiv.symm.toLinearMap
  change euler = 0 ↔
    productCovectorFirst sectors = 0 ∧ productCovectorSecond sectors = 0
  rw [← productCovector_eq_zero_iff sectors]
  rw [covector_comp_equiv_symm_eq_zero_iff sectorEquiv canonical]
  have hCanonical : canonical = 0 ↔ euler.toLinearMap = 0 := by
    simpa [canonical] using
      (covector_comp_equiv_symm_eq_zero_iff
        tangentEquiv.symm euler.toLinearMap)
  constructor
  · intro h
    apply hCanonical.mpr
    rw [h]
    rfl
  · intro h
    have hLinear := hCanonical.mp h
    apply ContinuousLinearMap.ext
    intro direction
    have hApply := congrArg (fun map => map direction) hLinear
    simpa using hApply

/-- On the retractive atlas, global criticality at the covered base is exactly
the corrected bulk and primitive SpinC sector system. -/
theorem globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff_sectors
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (retraction : LocalChartCoordinateRetraction period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)) :
    (globalCandidateAMinimalPhysicalVariationalAtlas_of_retraction period
        hPeriod configuration data analysis chartData retraction).IsEulerCritical
          period hPeriod configuration.physical ↔
      globalCandidateAMinimalPhysicalBulkEulerCovectorAt period hPeriod
          configuration data analysis chartData
            (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
              configuration data analysis chartData).basePoint = 0 ∧
        globalCandidateAMinimalPhysicalSpinCMatterEulerCovectorAt period hPeriod
          configuration data analysis chartData
            (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
              configuration data analysis chartData).basePoint = 0 := by
  rw [globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff
    period hPeriod configuration data analysis chartData retraction]
  exact globalCandidateAMinimalPhysicalEuler_eq_zero_iff_sectors period hPeriod
    configuration data analysis chartData
      (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
        configuration data analysis chartData).basePoint

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
end JanusFormal
