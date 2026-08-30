import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPDEResidualBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D

/-!
# Exact nine-block formula for the minimal Hilbert Euler residual

On every admissible Hilbert state, pairing the nonlinear strong residual with
a Hilbert test is exactly the sum of the derivatives of the nine true action
blocks along the realized chart direction.  The same formula computes the
Frechet derivative of the pulled nonlinear action.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertBlockSum4D

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
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertResidualAtlas4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPhysicalAtlasBridge4D
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
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData))

local instance denseCoreCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedNormedAddCommGroup period hPeriod configuration data analysis

local instance denseCoreCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  commonAugmentedNormedSpace period hPeriod configuration data analysis

/-- The nonlinear strong residual is the Riesz representative of the exact
nine-block Euler derivative at every admissible Hilbert state. -/
theorem globalCandidateAMinimalPhysicalHilbertResidual_pairing_eq_blockSum
    (state test : CommonAugmentedHilbert period hPeriod configuration data
      analysis)
    (hState : state ∈
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).carrier) :
    inner Real
        ((globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
          hPeriod configuration data analysis chartData hilbertChart).residual
            period hPeriod state) test =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.toActionFamily
              period hPeriod 0
                (globalCandidateAMinimalPhysicalLocalVariationalChart period
                  hPeriod configuration data analysis chartData).zero_mem_domain)
          measure)
        (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
          configuration data analysis chartData hilbertChart state)
        (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
          configuration data analysis chartData hilbertChart test) := by
  change
    inner Real
      (globalCandidateANonlinearHilbertRieszResidual period hPeriod
        configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge.basePoint
        (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
          configuration data analysis chartData hilbertChart) state) test = _
  rw [globalCandidateANonlinearHilbertRieszResidual_pairing period hPeriod
    configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData).chartBridge.basePoint
      (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
        configuration data analysis chartData hilbertChart) state test]
  change
    globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
          configuration data analysis chartData hilbertChart state)
        (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
          configuration data analysis chartData hilbertChart test) = _
  exact globalCandidateALocalEulerLagrangeOperator_apply_eq_blockSum period
    hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
        configuration data analysis chartData hilbertChart state)
      (globalCandidateAMinimalPhysicalHilbertChartPoint_mem_domain period
        hPeriod configuration data analysis chartData hilbertChart state hState)
      (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
        configuration data analysis chartData hilbertChart test)

/-- Surjectivity of the Hilbert chart equivalence realizes any chart test
direction in the exact residual pairing formula. -/
theorem globalCandidateAMinimalPhysicalHilbertResidual_pairing_symm_eq_blockSum
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).carrier)
    (direction :
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model) :
    inner Real
        ((globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
          hPeriod configuration data analysis chartData hilbertChart).residual
            period hPeriod state)
        (hilbertChart.toChart.symm direction) =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.toActionFamily
              period hPeriod 0
                (globalCandidateAMinimalPhysicalLocalVariationalChart period
                  hPeriod configuration data analysis chartData).zero_mem_domain)
          measure)
        (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
          configuration data analysis chartData hilbertChart state)
        direction := by
  rw [globalCandidateAMinimalPhysicalHilbertResidual_pairing_eq_blockSum period
    hPeriod configuration data analysis chartData hilbertChart state
      (hilbertChart.toChart.symm direction) hState]
  change
    fullCoupledEulerBlockSum _ _
      (hilbertChart.toChart (hilbertChart.toChart.symm direction)) = _
  rw [hilbertChart.toChart.apply_symm_apply]

/-- The Frechet derivative of the pulled nonlinear action has the same exact
nine-block formula. -/
theorem globalCandidateAMinimalPhysicalHilbertAction_fderiv_apply_eq_blockSum
    (state test : CommonAugmentedHilbert period hPeriod configuration data
      analysis)
    (hState : state ∈
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).carrier) :
    fderiv Real
        (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
          hPeriod configuration data analysis chartData hilbertChart).action
        state test =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.toActionFamily
              period hPeriod 0
                (globalCandidateAMinimalPhysicalLocalVariationalChart period
                  hPeriod configuration data analysis chartData).zero_mem_domain)
          measure)
        (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
          configuration data analysis chartData hilbertChart state)
        (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
          configuration data analysis chartData hilbertChart test) := by
  change
    fderiv Real
      (globalCandidateANonlinearHilbertAction period hPeriod configuration data
        analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge.basePoint
        (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
          configuration data analysis chartData hilbertChart)) state test = _
  rw [globalCandidateANonlinearHilbertAction_fderiv period hPeriod configuration
    data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData).chartBridge.basePoint
      (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
        configuration data analysis chartData hilbertChart) state
      (globalCandidateAMinimalPhysicalHilbertChartPoint_mem_domain period
        hPeriod configuration data analysis chartData hilbertChart state hState)]
  change
    globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
          configuration data analysis chartData hilbertChart state)
        (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
          configuration data analysis chartData hilbertChart test) = _
  exact globalCandidateALocalEulerLagrangeOperator_apply_eq_blockSum period
    hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
        configuration data analysis chartData hilbertChart state)
      (globalCandidateAMinimalPhysicalHilbertChartPoint_mem_domain period
        hPeriod configuration data analysis chartData hilbertChart state hState)
      (globalCandidateAMinimalPhysicalHilbertChartRealization period hPeriod
        configuration data analysis chartData hilbertChart test)

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertBlockSum4D
end JanusFormal
