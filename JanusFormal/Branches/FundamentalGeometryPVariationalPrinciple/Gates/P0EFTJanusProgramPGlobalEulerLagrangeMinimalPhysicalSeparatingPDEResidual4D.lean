import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalWeakEightSectorSystem4D

/-!
# Separating PDE residual frontier for the minimal eight-sector system

This gate states the exact data needed to turn the proved weak equations into
strong residual equations.  It does not identify an older scalar or LL
operator with the current minimal covectors: concrete tensorial residuals must
provide the representation and separation laws below.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalWeakEightSectorSystem4D
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

/-- A strong PDE residual represents a weak covector and is separated by its
test space.  The residual carrier may be a tensor field, distribution, or a
product of sector residuals. -/
structure SeparatingPDEResidualRepresentation
    {Test : Type*} [AddCommGroup Test] [Module Real Test]
    (covector : Test →ₗ[Real] Real) where
  Residual : Type*
  zeroResidual : Residual
  residual : Residual
  pairing : Residual → Test → Real
  represents : ∀ test, covector test = pairing residual test
  separates : (∀ test, pairing residual test = 0) ↔ residual = zeroResidual

/-- Separation makes weak covector vanishing equivalent to the strong
residual equation. -/
theorem separatingPDEResidualRepresentation_covector_eq_zero_iff
    {Test : Type*} [AddCommGroup Test] [Module Real Test]
    {covector : Test →ₗ[Real] Real}
    (representation : SeparatingPDEResidualRepresentation covector) :
    covector = 0 ↔
      representation.residual = representation.zeroResidual := by
  constructor
  · intro hCovector
    apply representation.separates.mp
    intro test
    rw [← representation.represents test, hCovector]
    rfl
  · intro hResidual
    apply LinearMap.ext
    intro test
    rw [representation.represents test]
    simpa using representation.separates.mpr hResidual test

/-- The two separating residual representations cover the seven named bulk
fields and primitive SpinC matter, hence the exact eight-sector system. -/
structure GlobalCandidateAMinimalPhysicalStrongEightSectorPDEDataAt
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
      hPeriod configuration data analysis chartData).Model) where
  sevenBulk : SeparatingPDEResidualRepresentation
    (globalCandidateAMinimalPhysicalSevenBulkEulerCovectorAt period hPeriod
      configuration data analysis chartData point)
  spinC : SeparatingPDEResidualRepresentation
    (globalCandidateAMinimalPhysicalSpinCMatterEulerCovectorAt period hPeriod
      configuration data analysis chartData point)

/-- Strong eight-sector PDE system attached to supplied concrete residual
representatives. -/
def GlobalCandidateAMinimalPhysicalStrongEightSectorPDESystemAt
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
    (pdeData : GlobalCandidateAMinimalPhysicalStrongEightSectorPDEDataAt
      period hPeriod configuration data analysis chartData point) : Prop :=
  pdeData.sevenBulk.residual = pdeData.sevenBulk.zeroResidual ∧
    pdeData.spinC.residual = pdeData.spinC.zeroResidual

/-- The local minimal Euler equation is equivalent to the two strong residual
equations whenever separating representatives have been constructed. -/
theorem globalCandidateAMinimalPhysicalEuler_eq_zero_iff_strongEightSectorPDE
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
    (pdeData : GlobalCandidateAMinimalPhysicalStrongEightSectorPDEDataAt
      period hPeriod configuration data analysis chartData point) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData) point = 0 ↔
      GlobalCandidateAMinimalPhysicalStrongEightSectorPDESystemAt period
        hPeriod configuration data analysis chartData point pdeData := by
  rw [globalCandidateAMinimalPhysicalEuler_eq_zero_iff_sectors period hPeriod
    configuration data analysis chartData point]
  rw [← globalCandidateAMinimalPhysicalSevenBulkEuler_eq_zero_iff_bulk
    period hPeriod configuration data analysis chartData point]
  exact and_congr
    (separatingPDEResidualRepresentation_covector_eq_zero_iff
      pdeData.sevenBulk)
    (separatingPDEResidualRepresentation_covector_eq_zero_iff pdeData.spinC)

/-- At admissible chart points, the exact weak nine-block system is equivalent
to the supplied strong eight-sector PDE residual equations. -/
theorem globalCandidateAMinimalPhysicalWeakEightSectorSystem_iff_strongPDE
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
        configuration data analysis chartData).family.domain)
    (pdeData : GlobalCandidateAMinimalPhysicalStrongEightSectorPDEDataAt
      period hPeriod configuration data analysis chartData point) :
    GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt period hPeriod
        configuration data analysis chartData point ↔
      GlobalCandidateAMinimalPhysicalStrongEightSectorPDESystemAt period
        hPeriod configuration data analysis chartData point pdeData :=
  (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_weakEightSectorSystem
    period hPeriod configuration data analysis chartData point hPoint).symm.trans
      (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_strongEightSectorPDE
        period hPeriod configuration data analysis chartData point pdeData)

/-- At the covered base, retractive-atlas criticality is equivalent to the
supplied strong eight-sector residual equations. -/
theorem globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff_strongPDE
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
        configuration data analysis chartData))
    (pdeData : GlobalCandidateAMinimalPhysicalStrongEightSectorPDEDataAt
      period hPeriod configuration data analysis chartData
        (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
          configuration data analysis chartData).basePoint) :
    (globalCandidateAMinimalPhysicalVariationalAtlas_of_retraction period
        hPeriod configuration data analysis chartData retraction).IsEulerCritical
          period hPeriod configuration.physical ↔
      GlobalCandidateAMinimalPhysicalStrongEightSectorPDESystemAt period
        hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
            configuration data analysis chartData).basePoint pdeData :=
  (globalCandidateAMinimalPhysicalRetractiveAtlas_isEulerCritical_iff_weakEightSectorSystem
    period hPeriod configuration data analysis chartData retraction).trans
      (globalCandidateAMinimalPhysicalWeakEightSectorSystem_iff_strongPDE
        period hPeriod configuration data analysis chartData
          (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
            configuration data analysis chartData).basePoint
          (globalCandidateAMinimalPhysicalLocalChartBridge period hPeriod
            configuration data analysis chartData).basePoint_mem pdeData)

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
end JanusFormal
