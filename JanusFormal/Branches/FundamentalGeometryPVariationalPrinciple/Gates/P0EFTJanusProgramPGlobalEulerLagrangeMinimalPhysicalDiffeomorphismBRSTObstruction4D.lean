import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEinsteinMaxwellMetricCrossBlockDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

/-!
# Diffeomorphism-BRST obstruction for the minimal physical chart

The canonical core-to-chart map forgets the typed diffeomorphism nonminimal
fields.  Consequently, any nonzero such direction rules out both injectivity
and a linear left inverse.  A faithful BRST residual therefore cannot be
identified with the present minimal chart without changing the architecture.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalDiffeomorphismBRSTObstruction4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

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

variable
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

/-- Any nonzero typed diffeomorphism nonminimal direction makes the canonical
minimal core-to-chart map noninjective. -/
theorem globalCandidateAMinimalPhysicalCoreToChart_not_injective_of_nonzero_diffeomorphismNonminimal
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod)
    (hNonzero : nonminimal ≠ 0) :
    ¬ Function.Injective
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData)) := by
  intro hInjective
  let core := globalCandidateAPureDiffeomorphismNonminimalCore period hPeriod
    configuration analysis nonminimal
  let coreToChart := globalCandidateACanonicalSixCoreToChart period hPeriod
    configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData)
  have hImages : coreToChart core = coreToChart 0 := by
    rw [globalCandidateAMinimalPhysicalCoreToChart_pureDiffeomorphismNonminimal_eq_zero]
    exact coreToChart.map_zero.symm
  have hCoreZero : core = 0 := hInjective hImages
  exact hNonzero
    ((globalCandidateAPureDiffeomorphismNonminimalCore_eq_zero_iff period
      hPeriod configuration analysis nonminimal).mp hCoreZero)

/-- Under the same nontriviality hypothesis, no linear recovery map can be a
left inverse of the canonical minimal core-to-chart map. -/
theorem globalCandidateAMinimalPhysicalCoreToChart_no_linearLeftInverse_of_nonzero_diffeomorphismNonminimal
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod)
    (hNonzero : nonminimal ≠ 0) :
    ¬ ∃ recover :
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).Model →ₗ[Real]
          GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis,
      recover.comp
          (globalCandidateACanonicalSixCoreToChart period hPeriod configuration
            data analysis
            (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
              configuration data analysis chartData)
            (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period
              hPeriod configuration data analysis chartData)) =
        LinearMap.id := by
  rintro ⟨recover, hLeftInverse⟩
  have hInjective : Function.Injective
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData)) := by
    intro first second hEqual
    have hRecovered := congrArg recover hEqual
    have hFirst := LinearMap.congr_fun hLeftInverse first
    have hSecond := LinearMap.congr_fun hLeftInverse second
    change recover _ = first at hFirst
    change recover _ = second at hSecond
    exact hFirst.symm.trans (hRecovered.trans hSecond)
  exact
    (globalCandidateAMinimalPhysicalCoreToChart_not_injective_of_nonzero_diffeomorphismNonminimal
      period hPeriod configuration data analysis chartData nonminimal hNonzero)
      hInjective

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalDiffeomorphismBRSTObstruction4D
end JanusFormal
