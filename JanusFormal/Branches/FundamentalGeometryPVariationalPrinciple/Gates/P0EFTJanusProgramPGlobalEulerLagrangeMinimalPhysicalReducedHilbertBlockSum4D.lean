import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D

/-!
# Exact nine-block formula on the reduced physical Hilbert space

The reduced strong residual and the derivative of the reduced nonlinear action
pair exactly as the derivative sum of the nine genuine action blocks.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertBlockSum4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D

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
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData)

/-- Pairing the reduced strong residual with any Hilbert test gives the exact
nine-block derivative sum. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertResidual_pairing_eq_blockSum
    (state test : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period
          hPeriod configuration data analysis chartData reducedChart state)
        test =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.toActionFamily
              period hPeriod 0
                (globalCandidateAMinimalPhysicalLocalVariationalChart period
                  hPeriod configuration data analysis chartData).zero_mem_domain)
          measure)
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis chartData reducedChart state)
        (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
          hPeriod configuration data analysis chartData reducedChart test) := by
  rw [globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing]
  change
    globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis chartData reducedChart state)
        (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
          hPeriod configuration data analysis chartData reducedChart test) = _
  exact globalCandidateALocalEulerLagrangeOperator_apply_eq_blockSum period
    hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis chartData reducedChart state)
      hState
      (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis chartData reducedChart test)

/-- Any chart test direction is realized through the inverse reduced Hilbert
chart equivalence. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertResidual_pairing_symm_eq_blockSum
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain)
    (direction :
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period
          hPeriod configuration data analysis chartData reducedChart state)
        (reducedChart.toChart.symm direction) =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.toActionFamily
              period hPeriod 0
                (globalCandidateAMinimalPhysicalLocalVariationalChart period
                  hPeriod configuration data analysis chartData).zero_mem_domain)
          measure)
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis chartData reducedChart state)
        direction := by
  rw [globalCandidateAMinimalPhysicalReducedHilbertResidual_pairing_eq_blockSum
    period hPeriod configuration data analysis chartData reducedChart state
      (reducedChart.toChart.symm direction) hState]
  change fullCoupledEulerBlockSum _ _
    (reducedChart.toChart (reducedChart.toChart.symm direction)) = _
  rw [reducedChart.toChart.apply_symm_apply]

/-- The Frechet derivative of the reduced nonlinear action obeys the same
exact nine-block formula. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv_apply_eq_blockSum
    (state test : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
          configuration data analysis chartData reducedChart) state test =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.toActionFamily
              period hPeriod 0
                (globalCandidateAMinimalPhysicalLocalVariationalChart period
                  hPeriod configuration data analysis chartData).zero_mem_domain)
          measure)
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis chartData reducedChart state)
        (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
          hPeriod configuration data analysis chartData reducedChart test) := by
  rw [globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv period hPeriod
    configuration data analysis chartData reducedChart state hState]
  change
    globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis chartData reducedChart state)
        (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
          hPeriod configuration data analysis chartData reducedChart test) = _
  exact globalCandidateALocalEulerLagrangeOperator_apply_eq_blockSum period
    hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis chartData reducedChart state)
      hState
      (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis chartData reducedChart test)

/-- Quotient-core tests give the exact block sum along the canonical reduced
core-to-chart direction. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertResidual_pairing_core_eq_blockSum
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (core : GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period
          hPeriod configuration data analysis chartData reducedChart state)
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis core) =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData).family.toActionFamily
              period hPeriod 0
                (globalCandidateAMinimalPhysicalLocalVariationalChart period
                  hPeriod configuration data analysis chartData).zero_mem_domain)
          measure)
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis chartData reducedChart state)
        (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
          configuration data analysis chartData core) := by
  rw [globalCandidateAMinimalPhysicalReducedHilbertResidual_pairing_eq_blockSum
    period hPeriod configuration data analysis chartData reducedChart state
      (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding period
        hPeriod configuration data analysis core) hState]
  rw [globalCandidateAMinimalPhysicalReducedHilbertChartRealization_core]

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertBlockSum4D
end JanusFormal
