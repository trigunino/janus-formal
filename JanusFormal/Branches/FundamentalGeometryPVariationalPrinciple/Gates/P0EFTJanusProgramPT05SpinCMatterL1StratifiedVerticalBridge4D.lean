import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05SpinCMatterIntrinsicL1Variation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05FixedCarrierStratifiedVerticalDifferential4D

/-!
# T05 SpinC L1 stratified vertical bridge

Gate 830 keeps the maximal SpinC state as an integrated frontier.  Gate 857
now supplies its canonical intrinsic L1 density.  This module installs that
density in an enriched bulk slot while retaining exact projections to the
Gate-830 carrier.

The physical SpinC vertical component is Gate 860's L1 Frechet derivative.
Its projection to Gate 854 stores precisely its integral in the older scalar
SpinC coefficient, and sectorwise integration recovers the existing graph
Euler covector.  The other physical density derivatives are left zero here;
no full stratified physical vertical differential or terminal result is
claimed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05SpinCMatterL1StratifiedVerticalBridge4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal lp
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05LLLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
open P0EFTJanusProgramPT05StratifiedLocalVerticalDensityComplex4D
open P0EFTJanusProgramPT05FixedCarrierStratifiedVerticalDifferential4D
open P0EFTJanusProgramPT05SpinCMatterIntrinsicL1Completion4D
open P0EFTJanusProgramPT05SpinCMatterIntrinsicL1Variation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCMatterL1 :=
  Lp Real 1 (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

local instance spinCMatterL1StratifiedMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance spinCMatterL1StratifiedBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance spinCMatterL1StratifiedFiniteMeasure :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance spinCMatterL1StratifiedHilbertRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

/-- Bulk slot with the former three Gate-830 components and the actual
intrinsic L1 density of its SpinC frontier. -/
structure ProgramPT05SpinCMatterL1BulkDensitySlot
    (period : Real) (hPeriod : period ≠ 0)
    (couplings : GlobalCandidateAActionCouplings) where
  bulkDensity : C(EffectiveQuotient period hPeriod, Real)
  spinCFrontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
    couplings.matterMassSquared
  spinCDensityL1 : SpinCMatterL1 period hPeriod
  spinCDensityL1_eq_frontier :
    spinCDensityL1 =
      ProgramPT05BulkSpinCLocalDensityFrontier.intrinsicDensityL1
        period hPeriod couplings spinCFrontier
  llDensity : C(EffectiveThroat period hPeriod, Real)

/-- Gate 830 with its bulk slot enriched by the canonical maximal SpinC L1
density. -/
structure ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain
    (period : Real) (hPeriod : period ≠ 0)
    (couplings : GlobalCandidateAActionCouplings)
    (NullFace : Type*) where
  bulk : ProgramPT05SpinCMatterL1BulkDensitySlot period hPeriod couplings
  nonNullBoundaryDensity : CandidateANormalBoundaryScalarField period hPeriod
  nullFaceInterval : NullFace → OrientedNullInterval
  nullBoundaryDensity : NullFace → Real → Real
  jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real

/-- Canonical enrichment of every Gate-830 carrier. -/
def programPT05SpinCMatterL1StratifiedDensityOfGeometric
    {NullFace : Type*}
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace where
  bulk :=
    { bulkDensity := density.bulkDensity
      spinCFrontier := density.spinCFrontier
      spinCDensityL1 :=
        ProgramPT05BulkSpinCLocalDensityFrontier.intrinsicDensityL1
          period hPeriod couplings density.spinCFrontier
      spinCDensityL1_eq_frontier := rfl
      llDensity := density.llDensity }
  nonNullBoundaryDensity := density.nonNullBoundaryDensity
  nullFaceInterval := density.nullFaceInterval
  nullBoundaryDensity := density.nullBoundaryDensity
  jointDensity := density.jointDensity

/-- Forgetting the additional L1 representative recovers a Gate-830
carrier. -/
def ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain.toGeometric
    {NullFace : Type*}
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain
      period hPeriod couplings NullFace) :
    ProgramPT05GeometricStratifiedDensityCochain period hPeriod couplings
      NullFace where
  bulkDensity := density.bulk.bulkDensity
  spinCFrontier := density.bulk.spinCFrontier
  llDensity := density.bulk.llDensity
  nonNullBoundaryDensity := density.nonNullBoundaryDensity
  nullFaceInterval := density.nullFaceInterval
  nullBoundaryDensity := density.nullBoundaryDensity
  jointDensity := density.jointDensity

@[simp]
theorem programPT05SpinCMatterL1StratifiedDensityOfGeometric_toGeometric
    {NullFace : Type*}
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain.toGeometric
      period hPeriod couplings
        (programPT05SpinCMatterL1StratifiedDensityOfGeometric period hPeriod
          couplings density) = density := by
  rfl

/-- The L1 density stored in an enriched bulk slot integrates to the action
of its retained Gate-830 frontier. -/
theorem ProgramPT05SpinCMatterL1BulkDensitySlot.integral_spinCDensityL1
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05SpinCMatterL1BulkDensitySlot period hPeriod couplings) :
    L1.integralCLM bulk.spinCDensityL1 =
      programPT05BulkSpinCFrontierAction period hPeriod couplings
        bulk.spinCFrontier := by
  rw [bulk.spinCDensityL1_eq_frontier]
  calc
    L1.integralCLM
        (ProgramPT05BulkSpinCLocalDensityFrontier.intrinsicDensityL1
          period hPeriod couplings bulk.spinCFrontier) =
        L1.integral
          (ProgramPT05BulkSpinCLocalDensityFrontier.intrinsicDensityL1
            period hPeriod couplings bulk.spinCFrontier) :=
      (L1.integral_eq _).symm
    _ = ∫ base,
          ProgramPT05BulkSpinCLocalDensityFrontier.intrinsicDensityL1
            period hPeriod couplings bulk.spinCFrontier base
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
      L1.integral_eq_integral _
    _ = programPT05BulkSpinCFrontierAction period hPeriod couplings
          bulk.spinCFrontier :=
      ProgramPT05BulkSpinCLocalDensityFrontier.integral_intrinsicDensityL1
        period hPeriod couplings bulk.spinCFrontier

/-- Bulk-stratum integration using the actual SpinC L1 density rather than
the frontier action as a primitive scalar. -/
def programPT05SpinCMatterL1BulkDensityIntegral
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05SpinCMatterL1BulkDensitySlot period hPeriod couplings) :
    Real :=
  (programPT05GeometricBulkDensityIntegral period hPeriod bulk.bulkDensity +
    L1.integralCLM bulk.spinCDensityL1) +
  programPT05GeometricLLDensityIntegral period hPeriod bulk.llDensity

/-- The enriched bulk integral is exactly Gate 830's former mixed
bulk/frontier/LL evaluation. -/
theorem programPT05SpinCMatterL1BulkDensityIntegral_eq_gate830
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain
      period hPeriod couplings NullFace) :
    programPT05SpinCMatterL1BulkDensityIntegral period hPeriod couplings
        density.bulk =
      (programPT05IntegrateGeometricStratifiedDensityCochain period hPeriod
        couplings
        (ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain.toGeometric
          period hPeriod couplings density)).bulkDensityAction +
      (programPT05IntegrateGeometricStratifiedDensityCochain period hPeriod
        couplings
        (ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain.toGeometric
          period hPeriod couplings density)).spinCFrontierAction +
      (programPT05IntegrateGeometricStratifiedDensityCochain period hPeriod
        couplings
        (ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain.toGeometric
          period hPeriod couplings density)).llAction := by
  unfold programPT05SpinCMatterL1BulkDensityIntegral
    programPT05IntegrateGeometricStratifiedDensityCochain
    ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain.toGeometric
  rw [ProgramPT05SpinCMatterL1BulkDensitySlot.integral_spinCDensityL1
    period hPeriod couplings density.bulk]

/-- Full sectorwise integration of the enriched carrier.  Its bulk slot
really integrates the stored SpinC L1 class. -/
def programPT05SpinCMatterL1GeometricDensityIntegrationMap
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain
      period hPeriod couplings NullFace) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0
  | .bulk =>
      (programPT05SpinCMatterL1BulkDensityIntegral period hPeriod couplings
        density.bulk, 0)
  | .nonNullBoundary =>
      (programPT05GeometricGHYDensityIntegral period hPeriod
        density.nonNullBoundaryDensity, 0)
  | .nullBoundary =>
      (programPT05GeometricNullBoundaryDensityIntegral density.nullFaceInterval
        density.nullBoundaryDensity, 0)
  | .joint =>
      (programPT05GeometricJointDensityIntegral density.jointDensity, 0)

/-- Enriched integration agrees exactly with Gate 833 after forgetting the
stored representative. -/
theorem programPT05SpinCMatterL1GeometricDensityIntegrationMap_eq_gate833
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain
      period hPeriod couplings NullFace) :
    programPT05SpinCMatterL1GeometricDensityIntegrationMap period hPeriod
        couplings density =
      programPT05GeometricDensityIntegrationMap period hPeriod couplings
        (ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain.toGeometric
          period hPeriod couplings density) := by
  funext stratum
  cases stratum with
  | bulk =>
      apply Prod.ext
      · exact programPT05SpinCMatterL1BulkDensityIntegral_eq_gate830
          period hPeriod couplings density
      · rfl
  | nonNullBoundary => rfl
  | nullBoundary => rfl
  | joint => rfl

/-- Contact-degree-one carrier with an actual SpinC L1 variation in place of
Gate 854's scalar SpinC coefficient. -/
structure ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity
    (period : Real) (hPeriod : period ≠ 0)
    (NullFace : Type*)
    (_nullFaceInterval : NullFace → OrientedNullInterval) where
  bulkVerticalDensity : C(EffectiveQuotient period hPeriod, Real)
  spinCVerticalDensityL1 : SpinCMatterL1 period hPeriod
  llVerticalDensity : C(EffectiveThroat period hPeriod, Real)
  nonNullBoundaryVerticalDensity :
    CandidateANormalBoundaryScalarField period hPeriod
  nullBoundaryVerticalDensity : NullFace → Real → Real
  jointVerticalDensity : NullFace → ProgramPT05NullJointEndpoint → Real

/-- Projection to Gate 854: only here is the SpinC L1 density replaced by its
integrated scalar coefficient. -/
def ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity.toGate854
    {NullFace : Type*}
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity period
      hPeriod NullFace nullFaceInterval) :
    ProgramPT05FixedCarrierStratifiedVerticalDensityCochain period hPeriod
      NullFace nullFaceInterval where
  bulkVerticalDensity := density.bulkVerticalDensity
  spinCVerticalCoefficient := L1.integralCLM density.spinCVerticalDensityL1
  llVerticalDensity := density.llVerticalDensity
  nonNullBoundaryVerticalDensity := density.nonNullBoundaryVerticalDensity
  nullBoundaryVerticalDensity := density.nullBoundaryVerticalDensity
  jointVerticalDensity := density.jointVerticalDensity

/-- Physical SpinC part of the local vertical differential.  Every other
stratified component is zero because its physical derivative is not supplied
by Gate 860. -/
def programPT05SpinCMatterL1PhysicalLocalDV
    {NullFace : Type*}
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain
      period hPeriod couplings NullFace)
    (direction : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      couplings.matterMassSquared) :
    ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity period hPeriod
      NullFace density.nullFaceInterval where
  bulkVerticalDensity := 0
  spinCVerticalDensityL1 :=
    programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential
      period hPeriod couplings.matterMassSquared
      density.bulk.spinCFrontier.graphState direction
  llVerticalDensity := 0
  nonNullBoundaryVerticalDensity := 0
  nullBoundaryVerticalDensity := 0
  jointVerticalDensity := 0

/-- The projected Gate-854 SpinC coefficient is the true graph Euler
covector evaluated on the direction. -/
theorem programPT05SpinCMatterL1PhysicalLocalDV_toGate854_spinC
    {NullFace : Type*}
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain
      period hPeriod couplings NullFace)
    (direction : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      couplings.matterMassSquared) :
    (ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity.toGate854
      period hPeriod
        (programPT05SpinCMatterL1PhysicalLocalDV period hPeriod couplings
          density direction)).spinCVerticalCoefficient =
      fderiv Real
        (programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared)
        density.bulk.spinCFrontier.graphState direction := by
  rw [programPPrimitiveSpinCMatterGraphAction_fderiv]
  exact
    programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential_integralCLM
      period hPeriod couplings.matterMassSquared
      density.bulk.spinCFrontier.graphState direction

/-- The stored vertical L1 class is the Frechet derivative of the stored
maximal SpinC density, evaluated on the graph direction. -/
theorem programPT05SpinCMatterL1PhysicalLocalDV_spinC_eq_fderiv
    {NullFace : Type*}
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain
      period hPeriod couplings NullFace)
    (direction : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      couplings.matterMassSquared) :
    (programPT05SpinCMatterL1PhysicalLocalDV period hPeriod couplings density
      direction).spinCVerticalDensityL1 =
      fderiv Real
        (programPT05SpinCMatterMaximalIntrinsicLocalDensityL1 period hPeriod
          couplings.matterMassSquared)
        density.bulk.spinCFrontier.graphState direction := by
  rw [programPT05SpinCMatterMaximalIntrinsicLocalDensityL1_fderiv]
  rfl

/-- Sectorwise integration is exactly Gate 854's integration after projecting
the L1 SpinC variation to its scalar integral. -/
def programPT05IntegrateSpinCMatterL1FixedCarrierVerticalDensity
    {NullFace : Type*} [Fintype NullFace]
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity period
      hPeriod NullFace nullFaceInterval) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 1 :=
  programPT05IntegrateFixedCarrierStratifiedVerticalDensity period hPeriod 4
    nullFaceInterval
      (ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity.toGate854
        period hPeriod density)

/-- The bulk coordinate obtained by integrating the physical SpinC local
vertical density is the exact SpinC graph-action derivative. -/
theorem programPT05SpinCMatterL1PhysicalLocalDV_integration_bulk
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05SpinCMatterL1GeometricStratifiedDensityCochain
      period hPeriod couplings NullFace)
    (direction : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      couplings.matterMassSquared) :
    (programPT05IntegrateSpinCMatterL1FixedCarrierVerticalDensity period
      hPeriod density.nullFaceInterval
      (programPT05SpinCMatterL1PhysicalLocalDV period hPeriod couplings density
        direction) .bulk).2 =
      fderiv Real
        (programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared)
        density.bulk.spinCFrontier.graphState direction := by
  change
    (programPT05GeometricBulkDensityIntegral period hPeriod 0 +
        L1.integralCLM
          (programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential
            period hPeriod couplings.matterMassSquared
            density.bulk.spinCFrontier.graphState direction)) +
      programPT05GeometricLLDensityIntegral period hPeriod 0 = _
  rw [show programPT05GeometricBulkDensityIntegral period hPeriod 0 = 0 by
      unfold programPT05GeometricBulkDensityIntegral
      exact map_zero _]
  rw [show programPT05GeometricLLDensityIntegral period hPeriod 0 = 0 by
      unfold programPT05GeometricLLDensityIntegral
        programPT05LLDensityIntegral
      exact map_zero _]
  simp only [zero_add, add_zero]
  rw [programPPrimitiveSpinCMatterGraphAction_fderiv]
  exact
    programPT05SpinCMatterMaximalIntrinsicLocalDensityL1Differential_integralCLM
      period hPeriod couplings.matterMassSquared
      density.bulk.spinCFrontier.graphState direction

end
end P0EFTJanusProgramPT05SpinCMatterL1StratifiedVerticalBridge4D
end JanusFormal
