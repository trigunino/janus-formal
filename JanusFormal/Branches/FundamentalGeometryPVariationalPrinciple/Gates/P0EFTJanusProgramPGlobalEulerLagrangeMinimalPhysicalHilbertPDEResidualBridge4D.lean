import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPhysicalAtlasBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalCanonicalAlgebraicResidual4D

/-!
# Hilbert residual bridge to the minimal physical PDE systems

The nonlinear Hilbert residual vanishes exactly when the canonical algebraic
or any supplied componentwise strong PDE residual system vanishes at the
represented minimal-chart point.  At the Hilbert origin these equations are
the corresponding systems at the selected physical base configuration.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPDEResidualBridge4D

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
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
open P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlas4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlasRetraction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalWeakEightSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAtlasResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertResidualAtlas4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPhysicalAtlasBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentwisePDEResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalCanonicalAlgebraicResidual4D

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

/-- On the admissible carrier, Hilbert criticality is exactly the weak
eight-sector Euler system at the represented chart point. -/
theorem globalCandidateAMinimalPhysicalHilbertCritical_iff_weakEightSectorSystem
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (hState : state ∈
      (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).carrier) :
    (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).IsEulerCritical
          period hPeriod state ↔
      GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt period hPeriod
        configuration data analysis chartData
          (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
            configuration data analysis chartData hilbertChart state) :=
  (globalCandidateAMinimalPhysicalHilbertCritical_iff_localEuler period hPeriod
    configuration data analysis chartData hilbertChart state).trans
      (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_weakEightSectorSystem
        period hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
            configuration data analysis chartData hilbertChart state)
          (globalCandidateAMinimalPhysicalHilbertChartPoint_mem_domain period
            hPeriod configuration data analysis chartData hilbertChart state
              hState))

/-- Hilbert criticality is the canonical eight-sector algebraic residual
system at the represented chart point. -/
theorem globalCandidateAMinimalPhysicalHilbertCritical_iff_canonicalAlgebraicResidual
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).IsEulerCritical
          period hPeriod state ↔
      GlobalCandidateAMinimalPhysicalCanonicalAlgebraicResidualSystemAt
        period hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
            configuration data analysis chartData hilbertChart state) :=
  (globalCandidateAMinimalPhysicalHilbertCritical_iff_localEuler period hPeriod
    configuration data analysis chartData hilbertChart state).trans
      (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_canonicalAlgebraicResidual
        period hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
            configuration data analysis chartData hilbertChart state))

/-- Any separating componentwise PDE realization is equivalent to Hilbert
criticality at the same represented point. -/
theorem globalCandidateAMinimalPhysicalHilbertCritical_iff_componentwiseStrongPDE
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (pdeData : GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period
      hPeriod configuration data analysis chartData
        (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
          configuration data analysis chartData hilbertChart state)) :
    (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).IsEulerCritical
          period hPeriod state ↔
      GlobalCandidateAMinimalPhysicalComponentwiseStrongPDESystemAt period
        hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
            configuration data analysis chartData hilbertChart state) pdeData :=
  (globalCandidateAMinimalPhysicalHilbertCritical_iff_localEuler period hPeriod
    configuration data analysis chartData hilbertChart state).trans
      (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_componentwiseStrongPDE
        period hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalHilbertChartPoint period hPeriod
            configuration data analysis chartData hilbertChart state) pdeData)

/-- At the Hilbert origin, canonical algebraic residual vanishing is exactly
criticality of the selected physical base configuration. -/
theorem globalCandidateAMinimalPhysicalHilbertZeroCritical_iff_canonicalAlgebraicResidual
    (retraction : LocalChartCoordinateRetraction period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)) :
    (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).IsEulerCritical
          period hPeriod 0 ↔
      GlobalCandidateAMinimalPhysicalCanonicalAlgebraicResidualSystemAt
        period hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
            configuration data analysis chartData).basePoint :=
  (globalCandidateAMinimalPhysicalHilbertZeroCritical_iff_baseConfiguration
    period hPeriod configuration data analysis chartData hilbertChart
      retraction).trans
    (globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff_canonicalAlgebraicResidual
      period hPeriod configuration data analysis chartData retraction)

/-- At the Hilbert origin, every supplied componentwise PDE realization is
equivalent to criticality of the selected physical base configuration. -/
theorem globalCandidateAMinimalPhysicalHilbertZeroCritical_iff_componentwiseStrongPDE
    (retraction : LocalChartCoordinateRetraction period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData))
    (pdeData : GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period
      hPeriod configuration data analysis chartData
        (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
          configuration data analysis chartData).basePoint) :
    (globalCandidateAMinimalPhysicalNonlinearHilbertResidualAtlas period
        hPeriod configuration data analysis chartData hilbertChart).IsEulerCritical
          period hPeriod 0 ↔
      GlobalCandidateAMinimalPhysicalComponentwiseStrongPDESystemAt period
        hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
            configuration data analysis chartData).basePoint pdeData :=
  (globalCandidateAMinimalPhysicalHilbertZeroCritical_iff_baseConfiguration
    period hPeriod configuration data analysis chartData hilbertChart
      retraction).trans
    (globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff_componentwiseStrongPDE
      period hPeriod configuration data analysis chartData retraction pdeData)

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertPDEResidualBridge4D
end JanusFormal
