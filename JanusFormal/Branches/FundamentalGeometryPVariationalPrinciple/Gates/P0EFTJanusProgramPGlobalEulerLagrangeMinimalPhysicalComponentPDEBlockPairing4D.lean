import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentwisePDEResidual4D

/-!
# Exact action-block pairings for component PDE residuals

The seven canonical pure-field inclusions are made explicit.  Every separating
component residual therefore pairs exactly with the true nine-block action
derivative along its transported pure variation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusIndependentFieldVariationLinearSpace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusCompleteVariationModuleCore4D
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
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentwisePDEResidual4D

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

abbrev GlobalMinimalPhysicalMetricTest :=
  Sector → SmoothSymmetricCovariantTwoTensor period hPeriod

abbrev GlobalMinimalPhysicalGaugeTest :=
  SmoothQuotientField period hPeriod GaugeFiber ×
    SmoothQuotientField period hPeriod GaugeFiber

abbrev GlobalMinimalPhysicalNormalTest :=
  Sector → SmoothNormalDisplacement period hPeriod

abbrev GlobalMinimalPhysicalDiffeomorphismGhostTest :=
  Sector → CInfinityThroatGhost period hPeriod

abbrev GlobalMinimalPhysicalLLAuxMetricTest :=
  SmoothThroatField period hPeriod LLMetricFiber

abbrev GlobalMinimalPhysicalLLMeasureTest :=
  SmoothThroatField period hPeriod Real

abbrev GlobalMinimalPhysicalLLFieldTest :=
  SmoothThroatField period hPeriod LLFieldFiber

/-- Pure metric inclusion into the seven corrected bulk coordinates. -/
def globalMinimalPhysicalMetricTestInclusion :
    GlobalMinimalPhysicalMetricTest period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod where
  toFun variation := (variation, 0)
  map_add' first second := by
    simp
  map_smul' scalar variation := by
    simp

/-- Pure paired-Abelian inclusion. -/
def globalMinimalPhysicalGaugeTestInclusion :
    GlobalMinimalPhysicalGaugeTest period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod where
  toFun variation := (0, (variation, 0))
  map_add' first second := by
    simp
  map_smul' scalar variation := by
    simp

/-- Pure normal-displacement inclusion. -/
def globalMinimalPhysicalNormalTestInclusion :
    GlobalMinimalPhysicalNormalTest period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod where
  toFun variation := (0, (0, (variation, 0)))
  map_add' first second := by
    simp
  map_smul' scalar variation := by
    simp

/-- Pure diffeomorphism-ghost inclusion. -/
def globalMinimalPhysicalDiffeomorphismGhostTestInclusion :
    GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod where
  toFun variation := (0, (0, (0, (variation, 0))))
  map_add' first second := by
    simp
  map_smul' scalar variation := by
    simp

/-- Pure auxiliary-LL-metric inclusion. -/
def globalMinimalPhysicalLLAuxMetricTestInclusion :
    GlobalMinimalPhysicalLLAuxMetricTest period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod where
  toFun variation := (0, (0, (0, (0, (variation, 0)))))
  map_add' first second := by
    simp
  map_smul' scalar variation := by
    simp

/-- Pure LL-measure inclusion. -/
def globalMinimalPhysicalLLMeasureTestInclusion :
    GlobalMinimalPhysicalLLMeasureTest period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod where
  toFun variation := (0, (0, (0, (0, (0, (variation, 0))))))
  map_add' first second := by
    simp
  map_smul' scalar variation := by
    simp

/-- Pure LL-field inclusion. -/
def globalMinimalPhysicalLLFieldTestInclusion :
    GlobalMinimalPhysicalLLFieldTest period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod where
  toFun variation := (0, (0, (0, (0, (0, (0, variation))))))
  map_add' first second := by
    simp
  map_smul' scalar variation := by
    simp

/-- Each named component covector is precisely restriction along its pure
seven-coordinate inclusion. -/
theorem globalCandidateAMinimalPhysicalMetricEuler_eq_restrict
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalMetricEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point).comp
          (globalMinimalPhysicalMetricTestInclusion period hPeriod) := by
  apply LinearMap.ext
  intro variation
  change
    (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
      configuration data analysis chartData point) (variation, 0) = _
  simp [globalMinimalPhysicalMetricTestInclusion]

theorem globalCandidateAMinimalPhysicalGaugeEuler_eq_restrict
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalGaugeEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point).comp
          (globalMinimalPhysicalGaugeTestInclusion period hPeriod) := by
  apply LinearMap.ext
  intro variation
  change
    (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
      configuration data analysis chartData point) (0, (variation, 0)) = _
  simp [globalMinimalPhysicalGaugeTestInclusion]

theorem globalCandidateAMinimalPhysicalNormalEuler_eq_restrict
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalNormalEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point).comp
          (globalMinimalPhysicalNormalTestInclusion period hPeriod) := by
  apply LinearMap.ext
  intro variation
  change
    (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
      configuration data analysis chartData point) (0, (0, (variation, 0))) = _
  simp [globalMinimalPhysicalNormalTestInclusion]

theorem globalCandidateAMinimalPhysicalDiffeomorphismGhostEuler_eq_restrict
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalDiffeomorphismGhostEulerCovectorAt
        period hPeriod configuration data analysis chartData point =
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point).comp
          (globalMinimalPhysicalDiffeomorphismGhostTestInclusion period
            hPeriod) := by
  apply LinearMap.ext
  intro variation
  change
    (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
      configuration data analysis chartData point)
        (0, (0, (0, (variation, 0)))) = _
  simp [globalMinimalPhysicalDiffeomorphismGhostTestInclusion]

theorem globalCandidateAMinimalPhysicalLLAuxMetricEuler_eq_restrict
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalLLAuxMetricEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point).comp
          (globalMinimalPhysicalLLAuxMetricTestInclusion period hPeriod) := by
  apply LinearMap.ext
  intro variation
  change
    (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
      configuration data analysis chartData point)
        (0, (0, (0, (0, (variation, 0))))) = _
  simp [globalMinimalPhysicalLLAuxMetricTestInclusion]

theorem globalCandidateAMinimalPhysicalLLMeasureEuler_eq_restrict
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalLLMeasureEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point).comp
          (globalMinimalPhysicalLLMeasureTestInclusion period hPeriod) := by
  apply LinearMap.ext
  intro variation
  change
    (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
      configuration data analysis chartData point)
        (0, (0, (0, (0, (0, (variation, 0)))))) = _
  simp [globalMinimalPhysicalLLMeasureTestInclusion]

theorem globalCandidateAMinimalPhysicalLLFieldEuler_eq_restrict
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model) :
    globalCandidateAMinimalPhysicalLLFieldEulerCovectorAt period hPeriod
        configuration data analysis chartData point =
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point).comp
          (globalMinimalPhysicalLLFieldTestInclusion period hPeriod) := by
  apply LinearMap.ext
  intro variation
  change
    (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
      configuration data analysis chartData point)
        (0, (0, (0, (0, (0, (0, variation)))))) = _
  simp [globalMinimalPhysicalLLFieldTestInclusion]

/-- Generic exact bridge from any named component representation to the true
nine-block action derivative. -/
theorem globalCandidateAMinimalPhysicalComponentBlockSum_eq_residualPairing
    {Component : Type*} [AddCommGroup Component] [Module Real Component]
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
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
        configuration data analysis chartData).family.domain)
    (componentCovector : Component →ₗ[Real] Real)
    (inclusion : Component →ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod)
    (hRestriction : componentCovector =
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point).comp inclusion)
    (representation : SeparatingPDEResidualRepresentation componentCovector)
    (variation : Component) :
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
          configuration data analysis chartData (inclusion variation)) =
      representation.pairing representation.residual variation := by
  rw [← globalCandidateAMinimalPhysicalSevenBulkEuler_restrict_apply_eq_blockSum
    period hPeriod configuration data analysis chartData point hPoint inclusion
      variation]
  rw [← hRestriction]
  exact representation.represents variation

/-- The primitive SpinC residual pairing is likewise the exact nine-block
derivative along the pure SpinC chart direction. -/
theorem globalCandidateAMinimalPhysicalSpinCBlockSum_eq_residualPairing
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
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
        configuration data analysis chartData).family.domain)
    (pdeData : GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period
      hPeriod configuration data analysis chartData point)
    (variation : Sector → D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter) :
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
          configuration data analysis chartData variation) =
      pdeData.spinC.pairing pdeData.spinC.residual variation := by
  rw [← globalCandidateAMinimalPhysicalSpinCMatterEuler_apply_eq_blockSum
    period hPeriod configuration data analysis chartData point hPoint variation]
  exact pdeData.spinC.represents variation

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
end JanusFormal
