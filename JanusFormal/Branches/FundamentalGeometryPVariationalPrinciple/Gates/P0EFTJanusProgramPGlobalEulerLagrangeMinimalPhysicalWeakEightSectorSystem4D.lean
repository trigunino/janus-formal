import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D

/-!
# Weak eight-sector Euler system

The exact nine-block derivative sum vanishes against every corrected bulk
test variation and every primitive SpinC test variation if and only if the
minimal-chart Euler covector vanishes.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalWeakEightSectorSystem4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlasRetraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)
private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

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

local instance effectiveThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

local instance globalMinimalPhysicalBulkTangentAddCommGroup :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModule :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

/-- Weak component system written solely with the true nine-block action
derivative and the two exhaustive corrected test packets. -/
def GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt
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
      hPeriod configuration data analysis chartData).Model) : Prop :=
  (∀ variation : GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod,
    fullCoupledEulerBlockSum
      (globalCandidateAActionBlocks period hPeriod
        ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.toActionFamily
            period hPeriod 0
            (globalCandidateAMinimalPhysicalLocalVariationalChart period
              hPeriod configuration data analysis chartData).zero_mem_domain)
        measure)
      point
      (globalCandidateAMinimalPhysicalSevenBulkChartDirection period hPeriod
        configuration data analysis chartData variation) = 0) ∧
  (∀ variation : Sector → D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter,
    fullCoupledEulerBlockSum
      (globalCandidateAActionBlocks period hPeriod
        ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.toActionFamily
            period hPeriod 0
            (globalCandidateAMinimalPhysicalLocalVariationalChart period
              hPeriod configuration data analysis chartData).zero_mem_domain)
        measure)
      point
      (globalCandidateAMinimalPhysicalSpinCMatterChartDirection period hPeriod
        configuration data analysis chartData variation) = 0)

/-- Seven-coordinate transport reflects vanishing of the corrected bulk Euler
covector. -/
theorem globalCandidateAMinimalPhysicalSevenBulkEuler_eq_zero_iff_bulk
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
    globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point = 0 ↔
      globalCandidateAMinimalPhysicalBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point = 0 :=
  covector_comp_equiv_symm_eq_zero_iff
    (globalMinimalPhysicalSevenBulkEquiv period hPeriod)
    (globalCandidateAMinimalPhysicalBulkEulerCovectorAt period hPeriod
      configuration data analysis chartData point)

/-- Local Euler vanishing is equivalent to the exact weak eight-sector
nine-block system at every admissible point. -/
theorem globalCandidateAMinimalPhysicalEuler_eq_zero_iff_weakEightSectorSystem
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
      hPeriod configuration data analysis chartData).Model)
    (hPoint : point ∈
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).family.domain) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData) point = 0 ↔
      GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt period hPeriod
        configuration data analysis chartData point := by
  rw [globalCandidateAMinimalPhysicalEuler_eq_zero_iff_sectors period hPeriod
    configuration data analysis chartData point]
  unfold GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt
  constructor
  · rintro ⟨hBulk, hSpin⟩
    have hSeven :
        globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
          configuration data analysis chartData point = 0 :=
      (globalCandidateAMinimalPhysicalSevenBulkEuler_eq_zero_iff_bulk
        period hPeriod configuration data analysis chartData point).2 hBulk
    constructor
    · intro variation
      rw [← globalCandidateAMinimalPhysicalSevenBulkEuler_apply_eq_blockSum
        period hPeriod configuration data analysis chartData point hPoint
          variation]
      have hApply := congrArg (fun map => map variation) hSeven
      simpa using hApply
    · intro variation
      rw [← globalCandidateAMinimalPhysicalSpinCMatterEuler_apply_eq_blockSum
        period hPeriod configuration data analysis chartData point hPoint
          variation]
      have hApply := congrArg (fun map => map variation) hSpin
      simpa using hApply
  · rintro ⟨hBulk, hSpin⟩
    have hSevenZero :
        globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
          configuration data analysis chartData point = 0 := by
      apply LinearMap.ext
      intro variation
      rw [globalCandidateAMinimalPhysicalSevenBulkEuler_apply_eq_blockSum
        period hPeriod configuration data analysis chartData point hPoint
          variation]
      exact hBulk variation
    have hBulkZero :=
      (globalCandidateAMinimalPhysicalSevenBulkEuler_eq_zero_iff_bulk
        period hPeriod configuration data analysis chartData point).1 hSevenZero
    have hSpinZero :
        globalCandidateAMinimalPhysicalSpinCMatterEulerCovectorAt period hPeriod
          configuration data analysis chartData point = 0 := by
      apply LinearMap.ext
      intro variation
      rw [globalCandidateAMinimalPhysicalSpinCMatterEuler_apply_eq_blockSum
        period hPeriod configuration data analysis chartData point hPoint
          variation]
      exact hSpin variation
    exact ⟨hBulkZero, hSpinZero⟩

/-- Retractive-atlas criticality at the covered base is exactly the weak
eight-sector nine-block system. -/
theorem globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff_weakEightSectorSystem
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
      GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt period hPeriod
        configuration data analysis chartData
          (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
            configuration data analysis chartData).basePoint := by
  rw [globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff
    period hPeriod configuration data analysis chartData retraction]
  exact
    globalCandidateAMinimalPhysicalEuler_eq_zero_iff_weakEightSectorSystem
      period hPeriod configuration data analysis chartData
        (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
          configuration data analysis chartData).basePoint
        (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
          configuration data analysis chartData).basePoint_mem

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalWeakEightSectorSystem4D
end JanusFormal
