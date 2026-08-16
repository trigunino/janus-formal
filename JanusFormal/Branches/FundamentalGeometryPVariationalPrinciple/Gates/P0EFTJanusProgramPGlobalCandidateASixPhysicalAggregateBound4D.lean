import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D

/-!
# Canonical H11 extension from one six-block aggregate bound

The H10 Robin Hessian is already continuous on the common Hilbert space after
pullback by the boundary projection.  Its operator norm therefore gives its
product estimate automatically.

Define the non-Robin core form by subtraction:

`B_six = B_physical - B_Robin`.

One bound on `B_six` combines with the automatic H10 bound to control the true
seven-block Hessian.  The existing two-variable `extendOfNorm` construction
then produces the unique continuous H11 extension.

Hence H11 can be supplied by one boundary projection and one scalar estimate
on the genuine six-block remainder; no continuous extension is chosen by hand.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateBound4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

private abbrev PhysicalCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev CommonHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) aggregateBoundHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) aggregateBoundHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) aggregateBoundHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) aggregateBoundHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) aggregateBoundHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)

local instance aggregateBoundBoundaryCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance aggregateBoundBoundaryCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance aggregateBoundBoundaryCoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreCompleteSpace period hPeriod metric

/-- Canonical Robin form on the diagonal smooth core. -/
def globalCandidateAH10RobinCoreLinearForm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (projection : CommonHilbert period hPeriod configuration data analysis →L[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real) :
    PhysicalCore period hPeriod analysis →ₗ[Real]
      PhysicalCore period hPeriod analysis →ₗ[Real] Real where
  toFun first :=
    { toFun := fun second =>
        globalCandidateAH10RobinCommonDomainForm period hPeriod configuration data
          analysis einsteinScale projection
          (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
            data analysis first)
          (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
            data analysis second)
      map_add' := by
        intro second third
        simp only [map_add]
      map_smul' := by
        intro scalar second
        simp only [map_smul]
        rfl }
  map_add' := by
    intro first second
    ext test
    simp only [map_add]
  map_smul' := by
    intro scalar first
    ext test
    simp only [map_smul]
    rfl

/-- The genuine six-block remainder on the smooth core. -/
def globalCandidateASixPhysicalAggregateCoreLinearForm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real)
    (projection : CommonHilbert period hPeriod configuration data analysis →L[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real) :
    PhysicalCore period hPeriod analysis →ₗ[Real]
      PhysicalCore period hPeriod analysis →ₗ[Real] Real :=
  globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration data
      analysis chart sameAction -
    globalCandidateAH10RobinCoreLinearForm period hPeriod configuration data
      analysis einsteinScale projection

/-- Single H11 estimate remaining after consuming H10. -/
structure GlobalCandidateASixPhysicalAggregateCoreBound4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real) : Prop where
  boundaryProjection : CommonHilbert period hPeriod configuration data analysis →L[Real]
    Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod
        data.plusGravity.metric) Real
  constant : Real
  constant_nonneg : 0 ≤ constant
  estimate : ∀ first second : PhysicalCore period hPeriod analysis,
    ‖globalCandidateASixPhysicalAggregateCoreLinearForm period hPeriod
        configuration data analysis chart sameAction einsteinScale
          boundaryProjection first second‖ ≤
      constant *
        ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis first‖ *
        ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis second‖

private theorem h10RobinCore_bound
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (projection : CommonHilbert period hPeriod configuration data analysis →L[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real)
    (first second : PhysicalCore period hPeriod analysis) :
    ‖globalCandidateAH10RobinCoreLinearForm period hPeriod configuration data
        analysis einsteinScale projection first second‖ ≤
      ‖globalCandidateAH10RobinCommonDomainForm period hPeriod configuration data
          analysis einsteinScale projection‖ *
        ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis first‖ *
        ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis second‖ := by
  let robin := globalCandidateAH10RobinCommonDomainForm period hPeriod
    configuration data analysis einsteinScale projection
  let firstImage := globalCandidateASevenPhysicalCoreEmbedding period hPeriod
    configuration data analysis first
  let secondImage := globalCandidateASevenPhysicalCoreEmbedding period hPeriod
    configuration data analysis second
  change ‖robin firstImage secondImage‖ ≤
    ‖robin‖ * ‖firstImage‖ * ‖secondImage‖
  calc
    ‖robin firstImage secondImage‖ ≤
        ‖robin firstImage‖ * ‖secondImage‖ :=
      (robin firstImage).le_opNorm secondImage
    _ ≤ (‖robin‖ * ‖firstImage‖) * ‖secondImage‖ :=
      mul_le_mul_of_nonneg_right (robin.le_opNorm firstImage)
        (norm_nonneg secondImage)

/-- Combine the automatic Robin bound with the single six-block estimate. -/
def globalCandidateASevenPhysicalCoreBound_of_sixAggregate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real)
    (bound : GlobalCandidateASixPhysicalAggregateCoreBound4D period hPeriod
      configuration data analysis chart sameAction einsteinScale) :
    GlobalCandidateASevenPhysicalCoreBound4D period hPeriod configuration data
      analysis chart sameAction where
  constant :=
    ‖globalCandidateAH10RobinCommonDomainForm period hPeriod configuration data
      analysis einsteinScale bound.boundaryProjection‖ + bound.constant
  constant_nonneg := add_nonneg (norm_nonneg _) bound.constant_nonneg
  estimate := by
    intro first second
    let robin := globalCandidateAH10RobinCoreLinearForm period hPeriod
      configuration data analysis einsteinScale bound.boundaryProjection
    let six := globalCandidateASixPhysicalAggregateCoreLinearForm period hPeriod
      configuration data analysis chart sameAction einsteinScale
        bound.boundaryProjection
    have hReconstruct :
        globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration
            data analysis chart sameAction first second =
          robin first second + six first second := by
      unfold six
      simp only [LinearMap.sub_apply]
      ring
    rw [hReconstruct]
    calc
      ‖robin first second + six first second‖ ≤
          ‖robin first second‖ + ‖six first second‖ :=
        norm_add_le _ _
      _ ≤
          ‖globalCandidateAH10RobinCommonDomainForm period hPeriod configuration
              data analysis einsteinScale bound.boundaryProjection‖ *
              ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis first‖ *
              ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis second‖ +
            bound.constant *
              ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis first‖ *
              ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis second‖ :=
        add_le_add
          (h10RobinCore_bound period hPeriod configuration data analysis
            einsteinScale bound.boundaryProjection first second)
          (bound.estimate first second)
      _ =
          (‖globalCandidateAH10RobinCommonDomainForm period hPeriod configuration
              data analysis einsteinScale bound.boundaryProjection‖ +
            bound.constant) *
              ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis first‖ *
              ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis second‖ := by
        ring

/-- Canonical H11 extension from the one remaining core estimate. -/
def globalCandidateASevenPhysicalCommonDomainExtension_of_sixAggregateBound
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real)
    (bound : GlobalCandidateASixPhysicalAggregateCoreBound4D period hPeriod
      configuration data analysis chart sameAction einsteinScale) :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_bound period hPeriod
    configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCoreBound_of_sixAggregate period hPeriod
        configuration data analysis chart sameAction einsteinScale bound)

/-- H11 checkpoint from a single six-block estimate. -/
theorem global_candidateA_h11_gate_of_sixAggregateBound
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real)
    (bound : GlobalCandidateASixPhysicalAggregateCoreBound4D period hPeriod
      configuration data analysis chart sameAction einsteinScale) :=
  global_candidateA_h11_common_augmented_domain_gate_of_bound period hPeriod
    configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCoreBound_of_sixAggregate period hPeriod
        configuration data analysis chart sameAction einsteinScale bound)

end
end P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateBound4D
end JanusFormal
