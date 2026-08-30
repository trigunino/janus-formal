import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D

/-!
# Canonical algebraic residual baseline

Every algebraic covector canonically represents itself and is separated by all
tests.  Applying this to the eight minimal sectors gives an unconditional
inhabitant of the residual interface.  Its residuals are dual elements, not
local tensorial differential operators; this isolates the remaining PDE task.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalCanonicalAlgebraicResidual4D

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
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalWeakEightSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalAtlasRetraction4D
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

/-- Canonical self-representation of an algebraic covector. -/
def separatingPDEResidualRepresentationSelf
    {Test : Type*} [AddCommGroup Test] [Module Real Test]
    (covector : Test →ₗ[Real] Real) :
    SeparatingPDEResidualRepresentation covector where
  Residual := Test →ₗ[Real] Real
  zeroResidual := 0
  residual := covector
  pairing := fun residual test ↦ residual test
  represents := fun _ ↦ rfl
  separates := by
    constructor
    · intro hZero
      apply LinearMap.ext
      intro test
      simpa using hZero test
    · intro hZero test
      rw [hZero]
      rfl

/-- Unconditional eight-sector residual data whose carriers are precisely the
eight algebraic duals. -/
def globalCandidateAMinimalPhysicalCanonicalAlgebraicPDEDataAt
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
    GlobalCandidateAMinimalPhysicalComponentwisePDEDataAt period hPeriod
      configuration data analysis chartData point where
  metric := separatingPDEResidualRepresentationSelf _
  gauge := separatingPDEResidualRepresentationSelf _
  normal := separatingPDEResidualRepresentationSelf _
  diffeomorphismGhost := separatingPDEResidualRepresentationSelf _
  llAuxMetric := separatingPDEResidualRepresentationSelf _
  llMeasure := separatingPDEResidualRepresentationSelf _
  llField := separatingPDEResidualRepresentationSelf _
  spinC := separatingPDEResidualRepresentationSelf _

/-- The canonical algebraic residual system.  This is a baseline, not the
missing tensorial PDE realization. -/
def GlobalCandidateAMinimalPhysicalCanonicalAlgebraicResidualSystemAt
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
  GlobalCandidateAMinimalPhysicalComponentwiseStrongPDESystemAt period hPeriod
    configuration data analysis chartData point
      (globalCandidateAMinimalPhysicalCanonicalAlgebraicPDEDataAt period
        hPeriod configuration data analysis chartData point)

/-- The canonical algebraic residual system is exactly local Euler
vanishing. -/
theorem globalCandidateAMinimalPhysicalEuler_eq_zero_iff_canonicalAlgebraicResidual
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
      GlobalCandidateAMinimalPhysicalCanonicalAlgebraicResidualSystemAt
        period hPeriod configuration data analysis chartData point :=
  globalCandidateAMinimalPhysicalEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis chartData point
      (globalCandidateAMinimalPhysicalCanonicalAlgebraicPDEDataAt period
        hPeriod configuration data analysis chartData point)

/-- At admissible points, the exact weak system is unconditionally equivalent
to the canonical algebraic residual equations. -/
theorem globalCandidateAMinimalPhysicalWeakEightSectorSystem_iff_canonicalAlgebraicResidual
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
    GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt period hPeriod
        configuration data analysis chartData point ↔
      GlobalCandidateAMinimalPhysicalCanonicalAlgebraicResidualSystemAt
        period hPeriod configuration data analysis chartData point :=
  (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_weakEightSectorSystem
    period hPeriod configuration data analysis chartData point hPoint).symm.trans
      (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_canonicalAlgebraicResidual
        period hPeriod configuration data analysis chartData point)

/-- At the covered base, atlas criticality is also exactly the canonical
algebraic residual system. -/
theorem globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff_canonicalAlgebraicResidual
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
      GlobalCandidateAMinimalPhysicalCanonicalAlgebraicResidualSystemAt
        period hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
            configuration data analysis chartData).basePoint := by
  rw [globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff
    period hPeriod configuration data analysis chartData retraction]
  exact
    globalCandidateAMinimalPhysicalEuler_eq_zero_iff_canonicalAlgebraicResidual
      period hPeriod configuration data analysis chartData
        (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
          configuration data analysis chartData).basePoint

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalCanonicalAlgebraicResidual4D
end JanusFormal
