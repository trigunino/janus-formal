import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D

/-!
# Seven-component corrected bulk Euler system

The corrected minimal bulk is identified with its seven genuinely free field
families.  Its Euler covector vanishes exactly when all seven restrictions do.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D

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
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
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

/-- Seven unconstrained field families remaining in the corrected bulk. -/
abbrev GlobalMinimalPhysicalSevenBulkCoordinates :=
  (Sector → SmoothSymmetricCovariantTwoTensor period hPeriod) ×
    ((SmoothQuotientField period hPeriod GaugeFiber ×
        SmoothQuotientField period hPeriod GaugeFiber) ×
      ((Sector → SmoothNormalDisplacement period hPeriod) ×
        ((Sector → CInfinityThroatGhost period hPeriod) ×
          (SmoothThroatField period hPeriod LLMetricFiber ×
            (SmoothThroatField period hPeriod Real ×
              SmoothThroatField period hPeriod LLFieldFiber)))))

/-- Exact linear coordinates of the corrected minimal bulk. -/
def globalMinimalPhysicalSevenBulkEquiv :
    GlobalMinimalPhysicalBulkTangent period hPeriod ≃ₗ[Real]
      GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod where
  toFun := fun variation =>
    let complete := variation.1.1.1
    (complete.fullMetricPerturbation,
      (complete.independent.gauge,
        (complete.normalDisplacement,
          (complete.diffeomorphismGhost,
            (complete.independent.llAuxMetric,
              (complete.independent.llMeasure,
                complete.independent.llField))))))
  invFun := fun coordinates =>
    ⟨⟨⟨
      { independent :=
          { metrics := 0
            matter := 0
            gauge := coordinates.2.1
            ghosts := 0
            auxiliaries := 0
            llAuxMetric := coordinates.2.2.2.2.1
            llMeasure := coordinates.2.2.2.2.2.1
            llField := coordinates.2.2.2.2.2.2 }
        normalDisplacement := coordinates.2.2.1
        diffeomorphismGhost := coordinates.2.2.2.1
        fullMetricPerturbation := coordinates.1 }, rfl⟩, rfl⟩, rfl⟩
  left_inv variation := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply ProgramPCompleteVariation4D.ext
    · apply IndependentFieldVariation.ext
      · exact variation.1.2.symm
      · exact variation.1.1.2.symm
      · rfl
      · have h := congrArg Prod.fst variation.2
        exact h.symm
      · have h := congrArg Prod.snd variation.2
        exact h.symm
      · rfl
      · rfl
      · rfl
    · rfl
    · rfl
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Corrected bulk Euler covector in the exact seven field coordinates. -/
def globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt
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
    GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod →ₗ[Real] Real :=
  (globalCandidateAMinimalPhysicalBulkEulerCovectorAt period hPeriod
    configuration data analysis chartData point).comp
      (globalMinimalPhysicalSevenBulkEquiv period hPeriod).symm.toLinearMap

def globalCandidateAMinimalPhysicalMetricEulerCovectorAt
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
      hPeriod configuration data analysis chartData).Model) :=
  productCovectorFirst
    (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
      configuration data analysis chartData point)

def globalCandidateAMinimalPhysicalGaugeEulerCovectorAt
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
      hPeriod configuration data analysis chartData).Model) :=
  productCovectorFirst (productCovectorSecond
    (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
      configuration data analysis chartData point))

def globalCandidateAMinimalPhysicalNormalEulerCovectorAt
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
      hPeriod configuration data analysis chartData).Model) :=
  productCovectorFirst (productCovectorSecond (productCovectorSecond
    (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
      configuration data analysis chartData point)))

def globalCandidateAMinimalPhysicalDiffeomorphismGhostEulerCovectorAt
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
      hPeriod configuration data analysis chartData).Model) :=
  productCovectorFirst (productCovectorSecond (productCovectorSecond
    (productCovectorSecond
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point))))

def globalCandidateAMinimalPhysicalLLAuxMetricEulerCovectorAt
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
      hPeriod configuration data analysis chartData).Model) :=
  productCovectorFirst (productCovectorSecond (productCovectorSecond
    (productCovectorSecond (productCovectorSecond
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point)))))

def globalCandidateAMinimalPhysicalLLMeasureEulerCovectorAt
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
      hPeriod configuration data analysis chartData).Model) :=
  productCovectorFirst (productCovectorSecond (productCovectorSecond
    (productCovectorSecond (productCovectorSecond (productCovectorSecond
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point))))))

def globalCandidateAMinimalPhysicalLLFieldEulerCovectorAt
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
      hPeriod configuration data analysis chartData).Model) :=
  productCovectorSecond (productCovectorSecond (productCovectorSecond
    (productCovectorSecond (productCovectorSecond (productCovectorSecond
      (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point))))))

/-- A covector on the seven-fold bulk product vanishes exactly when its seven
successive restrictions vanish. -/
theorem sevenBulkCovector_eq_zero_iff
    (covector : GlobalMinimalPhysicalSevenBulkCoordinates period hPeriod
      →ₗ[Real] Real) :
    covector = 0 ↔
      productCovectorFirst covector = 0 ∧
      productCovectorFirst (productCovectorSecond covector) = 0 ∧
      productCovectorFirst
          (productCovectorSecond (productCovectorSecond covector)) = 0 ∧
      productCovectorFirst
          (productCovectorSecond (productCovectorSecond
            (productCovectorSecond covector))) = 0 ∧
      productCovectorFirst
          (productCovectorSecond (productCovectorSecond
            (productCovectorSecond (productCovectorSecond covector)))) = 0 ∧
      productCovectorFirst
          (productCovectorSecond (productCovectorSecond
            (productCovectorSecond (productCovectorSecond
              (productCovectorSecond covector))))) = 0 ∧
      productCovectorSecond
          (productCovectorSecond (productCovectorSecond
            (productCovectorSecond (productCovectorSecond
              (productCovectorSecond covector))))) = 0 := by
  rw [productCovector_eq_zero_iff covector]
  rw [productCovector_eq_zero_iff (productCovectorSecond covector)]
  rw [productCovector_eq_zero_iff
    (productCovectorSecond (productCovectorSecond covector))]
  rw [productCovector_eq_zero_iff
    (productCovectorSecond (productCovectorSecond
      (productCovectorSecond covector)))]
  rw [productCovector_eq_zero_iff
    (productCovectorSecond (productCovectorSecond
      (productCovectorSecond (productCovectorSecond covector))))]
  rw [productCovector_eq_zero_iff
    (productCovectorSecond (productCovectorSecond
      (productCovectorSecond (productCovectorSecond
        (productCovectorSecond covector)))))]

/-- The corrected bulk Euler equation is exactly the seven component
equations for metric, gauge, normal displacement, diffeomorphism ghost and LL
metric/measure/field. -/
theorem globalCandidateAMinimalPhysicalBulkEuler_eq_zero_iff_seven
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
    globalCandidateAMinimalPhysicalBulkEulerCovectorAt period hPeriod
        configuration data analysis chartData point = 0 ↔
      globalCandidateAMinimalPhysicalMetricEulerCovectorAt period hPeriod
          configuration data analysis chartData point = 0 ∧
      globalCandidateAMinimalPhysicalGaugeEulerCovectorAt period hPeriod
          configuration data analysis chartData point = 0 ∧
      globalCandidateAMinimalPhysicalNormalEulerCovectorAt period hPeriod
          configuration data analysis chartData point = 0 ∧
      globalCandidateAMinimalPhysicalDiffeomorphismGhostEulerCovectorAt
          period hPeriod configuration data analysis chartData point = 0 ∧
      globalCandidateAMinimalPhysicalLLAuxMetricEulerCovectorAt period hPeriod
          configuration data analysis chartData point = 0 ∧
      globalCandidateAMinimalPhysicalLLMeasureEulerCovectorAt period hPeriod
          configuration data analysis chartData point = 0 ∧
      globalCandidateAMinimalPhysicalLLFieldEulerCovectorAt period hPeriod
          configuration data analysis chartData point = 0 := by
  let bulk := globalCandidateAMinimalPhysicalBulkEulerCovectorAt period hPeriod
    configuration data analysis chartData point
  let seven := globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period
    hPeriod configuration data analysis chartData point
  change bulk = 0 ↔
    productCovectorFirst seven = 0 ∧
    productCovectorFirst (productCovectorSecond seven) = 0 ∧
    productCovectorFirst
        (productCovectorSecond (productCovectorSecond seven)) = 0 ∧
    productCovectorFirst
        (productCovectorSecond (productCovectorSecond
          (productCovectorSecond seven))) = 0 ∧
    productCovectorFirst
        (productCovectorSecond (productCovectorSecond
          (productCovectorSecond (productCovectorSecond seven)))) = 0 ∧
    productCovectorFirst
        (productCovectorSecond (productCovectorSecond
          (productCovectorSecond (productCovectorSecond
            (productCovectorSecond seven))))) = 0 ∧
    productCovectorSecond
        (productCovectorSecond (productCovectorSecond
          (productCovectorSecond (productCovectorSecond
            (productCovectorSecond seven))))) = 0
  rw [← sevenBulkCovector_eq_zero_iff period hPeriod seven]
  exact (covector_comp_equiv_symm_eq_zero_iff
    (globalMinimalPhysicalSevenBulkEquiv period hPeriod) bulk).symm

/-- The complete corrected component system: seven bulk equations and the
primitive SpinC equation. -/
def GlobalCandidateAMinimalPhysicalEightSectorEulerSystemAt
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
  (globalCandidateAMinimalPhysicalMetricEulerCovectorAt period hPeriod
        configuration data analysis chartData point = 0 ∧
    globalCandidateAMinimalPhysicalGaugeEulerCovectorAt period hPeriod
        configuration data analysis chartData point = 0 ∧
    globalCandidateAMinimalPhysicalNormalEulerCovectorAt period hPeriod
        configuration data analysis chartData point = 0 ∧
    globalCandidateAMinimalPhysicalDiffeomorphismGhostEulerCovectorAt
        period hPeriod configuration data analysis chartData point = 0 ∧
    globalCandidateAMinimalPhysicalLLAuxMetricEulerCovectorAt period hPeriod
        configuration data analysis chartData point = 0 ∧
    globalCandidateAMinimalPhysicalLLMeasureEulerCovectorAt period hPeriod
        configuration data analysis chartData point = 0 ∧
    globalCandidateAMinimalPhysicalLLFieldEulerCovectorAt period hPeriod
        configuration data analysis chartData point = 0) ∧
  globalCandidateAMinimalPhysicalSpinCMatterEulerCovectorAt period hPeriod
      configuration data analysis chartData point = 0

/-- The local minimal Euler equation is the exact eight-sector system. -/
theorem globalCandidateAMinimalPhysicalEuler_eq_zero_iff_eightSectors
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
      GlobalCandidateAMinimalPhysicalEightSectorEulerSystemAt period hPeriod
        configuration data analysis chartData point := by
  unfold GlobalCandidateAMinimalPhysicalEightSectorEulerSystemAt
  rw [globalCandidateAMinimalPhysicalEuler_eq_zero_iff_sectors period hPeriod
    configuration data analysis chartData point]
  rw [globalCandidateAMinimalPhysicalBulkEuler_eq_zero_iff_seven period hPeriod
    configuration data analysis chartData point]

/-- On a retractive minimal atlas, global criticality at the base is the same
eight-sector component system. -/
theorem globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff_eightSectors
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
      GlobalCandidateAMinimalPhysicalEightSectorEulerSystemAt period hPeriod
        configuration data analysis chartData
          (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
            configuration data analysis chartData).basePoint := by
  unfold GlobalCandidateAMinimalPhysicalEightSectorEulerSystemAt
  rw [globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff_sectors
    period hPeriod configuration data analysis chartData retraction]
  rw [globalCandidateAMinimalPhysicalBulkEuler_eq_zero_iff_seven period hPeriod
    configuration data analysis chartData
      (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
        configuration data analysis chartData).basePoint]

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
end JanusFormal
