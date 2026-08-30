import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeVariationalAtlasHilbertResidualBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D

/-!
# Exact block formula in every Hilbert realization chart

For a compatible Hilbert realization over a physical variational atlas, the
global strong residual paired with a test is the exact nine-block Euler sum in
every chart, not only in the distinguished reference chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeVariationalAtlasHilbertBlockSum4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeVariationalAtlasHilbertResidualBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D

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

section

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)

local instance atlasCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedNormedAddCommGroup period hPeriod configuration data analysis

local instance atlasCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedNormedSpace period hPeriod configuration data analysis

variable
    {physicalAtlas : GlobalCandidateAVariationalAtlas period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure}
    (realization : GlobalCandidateAVariationalAtlasHilbertRealization period
      hPeriod configuration data analysis physicalAtlas)

/-- In every atlas chart, the descended residual has the exact nine-block
Euler pairing formula. -/
theorem GlobalCandidateAVariationalAtlasHilbertRealization.residual_pairing_eq_blockSum
    (state test : CommonAugmentedHilbert period hPeriod configuration data
      analysis)
    (hState : state ∈ realization.carrier)
    (index : physicalAtlas.Index) :
    inner Real
        ((realization.toNonlinearHilbertResidualAtlas period hPeriod).residual
          period hPeriod state) test =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          ((physicalAtlas.chart index).family.toActionFamily period hPeriod 0
            (physicalAtlas.chart index).zero_mem_domain) measure)
        (globalCandidateAVariationalAtlasHilbertPoint period hPeriod
          configuration data analysis physicalAtlas realization.basePoint
            realization.chartEquiv index state)
        ((realization.chartEquiv index).toContinuousLinearMap test) := by
  rw [GlobalCandidateANonlinearHilbertResidualAtlas.residual_eq_chart period
    hPeriod (realization.toNonlinearHilbertResidualAtlas period hPeriod) state
      hState index]
  change
    inner Real
      (globalCandidateANonlinearHilbertRieszResidual period hPeriod
        configuration data analysis (physicalAtlas.chart index)
        (realization.basePoint index)
        (realization.chartEquiv index).toContinuousLinearMap state) test = _
  rw [globalCandidateANonlinearHilbertRieszResidual_pairing period hPeriod
    configuration data analysis (physicalAtlas.chart index)
      (realization.basePoint index)
      (realization.chartEquiv index).toContinuousLinearMap state test]
  change
    globalCandidateALocalEulerLagrangeOperator period hPeriod
        (physicalAtlas.chart index)
        (globalCandidateAVariationalAtlasHilbertPoint period hPeriod
          configuration data analysis physicalAtlas realization.basePoint
            realization.chartEquiv index state)
        ((realization.chartEquiv index).toContinuousLinearMap test) = _
  exact globalCandidateALocalEulerLagrangeOperator_apply_eq_blockSum period
    hPeriod (physicalAtlas.chart index)
      (globalCandidateAVariationalAtlasHilbertPoint period hPeriod
        configuration data analysis physicalAtlas realization.basePoint
          realization.chartEquiv index state)
      (realization.point_mem state hState index)
      ((realization.chartEquiv index).toContinuousLinearMap test)

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeVariationalAtlasHilbertBlockSum4D
end JanusFormal
