import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03MetricBoundaryGHYDensityJetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05SpinCMatterL1StratifiedVerticalBridge4D

/-!
# T05 GHY stratified vertical bridge

Gate 858 supplies the genuine Frechet derivative of the completed GHY
integrand.  The mobile action has two boundary sheets, while Gate 854's
non-null integration slot integrates one sheet.  This module therefore puts
twice the density derivative in that slot.  Its integration is exactly the
two-sheet jet and the mobile GHY Euler covector.

All other stratified components are zero.  No geometric trace contract is
needed until one asks to identify this completed derivative with an explicit
Einstein--Hilbert boundary flux.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05GHYStratifiedVerticalBridge4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

open Set
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusProgramPT05FixedCarrierStratifiedVerticalDifferential4D
open P0EFTJanusProgramPT05SpinCMatterL1StratifiedVerticalBridge4D
open P0EFTJanusProgramPT04T03MetricBoundaryGHYDensityJetBridge4D

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
  (metric : RegularGeneralLorentzMetric period hPeriod)

private abbrev GHYCore :=
  CandidateANormalBoundaryFunctionalCore period hPeriod metric

private abbrev GHYInput := GHYCore period hPeriod metric × Real

private abbrev BoundaryField :=
  CandidateANormalBoundaryScalarField period hPeriod

local instance ghyCoreNormedAddCommGroup :
    NormedAddCommGroup (GHYCore period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance ghyCoreNormedSpace :
    NormedSpace Real (GHYCore period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedSpace
    period hPeriod metric

local instance : NormedSpace Real (GHYInput period hPeriod metric) :=
  Prod.normedSpace

/-- The local density whose first-sheet integral is the completed two-sheet
GHY action. -/
def programPT05GHYTwoSheetLocalDensityFiberEvaluation
    (einsteinScale : Real) :
    GHYInput period hPeriod metric → BoundaryField period hPeriod :=
  fun current ↦
    (2 : Real) • candidateANormalBoundaryGHYIntegrandFiberEvaluation
      period hPeriod einsteinScale metric current

/-- Gate 858's genuine integrand jet differentiates the two-sheet density
after applying the established multiplicity two. -/
theorem programPT05GHYTwoSheetLocalDensity_hasFDerivAt
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput period hPeriod metric)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    HasFDerivAt
      (programPT05GHYTwoSheetLocalDensityFiberEvaluation period hPeriod metric
        einsteinScale)
      ((2 : Real) •
        (programPT04T03GHYIntegrandSecondJetAt period hPeriod metric
          einsteinScale hTransverse current hCurrent).firstDerivative)
      current := by
  have hIntegrand :=
    programPT04T03GHYIntegrand_hasFDerivAt_factorized period hPeriod metric
      einsteinScale hTransverse current hCurrent
  rw [← programPT04T03GHYIntegrandSecondJet_firstDerivative_eq_factorized
    period hPeriod metric einsteinScale hTransverse current hCurrent] at hIntegrand
  exact hIntegrand.const_smul (2 : Real)

/-- Frechet derivative of the two-sheet local density. -/
theorem programPT05GHYTwoSheetLocalDensity_fderiv
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput period hPeriod metric)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric) :
    fderiv Real
        (programPT05GHYTwoSheetLocalDensityFiberEvaluation period hPeriod
          metric einsteinScale) current =
      (2 : Real) •
        (programPT04T03GHYIntegrandSecondJetAt period hPeriod metric
          einsteinScale hTransverse current hCurrent).firstDerivative :=
  (programPT05GHYTwoSheetLocalDensity_hasFDerivAt period hPeriod metric
    einsteinScale hTransverse current hCurrent).fderiv

/-- Physical GHY local vertical differential in the enriched Gate-861
carrier.  The non-null slot contains the two-sheet density derivative and all
other slots vanish. -/
def programPT05GHYTwoSheetPhysicalLocalDV
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput period hPeriod metric)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (direction : GHYInput period hPeriod metric) :
    ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity period hPeriod
      NullFace nullFaceInterval where
  bulkVerticalDensity := 0
  spinCVerticalDensityL1 := 0
  llVerticalDensity := 0
  nonNullBoundaryVerticalDensity :=
    (2 : Real) •
      (programPT04T03GHYIntegrandSecondJetAt period hPeriod metric
        einsteinScale hTransverse current hCurrent).firstDerivative direction
  nullBoundaryVerticalDensity := 0
  jointVerticalDensity := 0

/-- The non-null slot is exactly the derivative of the two-sheet local
density evaluated on the chosen direction. -/
theorem programPT05GHYTwoSheetPhysicalLocalDV_nonNull_eq_fderiv
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput period hPeriod metric)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (direction : GHYInput period hPeriod metric) :
    (programPT05GHYTwoSheetPhysicalLocalDV period hPeriod metric
      nullFaceInterval einsteinScale hTransverse current hCurrent direction).nonNullBoundaryVerticalDensity =
      fderiv Real
        (programPT05GHYTwoSheetLocalDensityFiberEvaluation period hPeriod
          metric einsteinScale) current direction := by
  rw [programPT05GHYTwoSheetLocalDensity_fderiv period hPeriod metric
    einsteinScale hTransverse current hCurrent]
  rfl

/-- Projection to Gate 854 preserves the actual GHY density derivative. -/
@[simp]
theorem programPT05GHYTwoSheetPhysicalLocalDV_toGate854_nonNull
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput period hPeriod metric)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (direction : GHYInput period hPeriod metric) :
    (ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity.toGate854
      period hPeriod
        (programPT05GHYTwoSheetPhysicalLocalDV period hPeriod metric
          nullFaceInterval einsteinScale hTransverse current hCurrent
          direction)).nonNullBoundaryVerticalDensity =
      (2 : Real) •
        (programPT04T03GHYIntegrandSecondJetAt period hPeriod metric
          einsteinScale hTransverse current hCurrent).firstDerivative
            direction := by
  rfl

/-- Sectorwise integration of the GHY-only carrier is exactly the two-sheet
density jet. -/
theorem programPT05GHYTwoSheetPhysicalLocalDV_integration_nonNull_eq_jet
    {NullFace : Type*} [Fintype NullFace]
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput period hPeriod metric)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (direction : GHYInput period hPeriod metric) :
    (programPT05IntegrateSpinCMatterL1FixedCarrierVerticalDensity period
      hPeriod nullFaceInterval
        (programPT05GHYTwoSheetPhysicalLocalDV period hPeriod metric
          nullFaceInterval einsteinScale hTransverse current hCurrent direction)
      .nonNullBoundary).2 =
      programPT04T03GHYTwoSheetJetEulerAt period hPeriod metric einsteinScale
        hTransverse current hCurrent direction := by
  change
    candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod
        ((2 : Real) •
          (programPT04T03GHYIntegrandSecondJetAt period hPeriod metric
            einsteinScale hTransverse current hCurrent).firstDerivative
              direction) = _
  simp only [map_smul, programPT04T03GHYTwoSheetJetEulerAt,
    programPT04T03GHYFirstSheetJetEulerAt, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]

/-- The same integrated non-null slot is the established mobile GHY Euler
covector evaluated on the boundary direction. -/
theorem programPT05GHYTwoSheetPhysicalLocalDV_integration_nonNull_eq_mobileEuler
    {NullFace : Type*} [Fintype NullFace]
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (current : GHYInput period hPeriod metric)
    (hCurrent : current ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric)
    (direction : GHYInput period hPeriod metric) :
    (programPT05IntegrateSpinCMatterL1FixedCarrierVerticalDensity period
      hPeriod nullFaceInterval
        (programPT05GHYTwoSheetPhysicalLocalDV period hPeriod metric
          nullFaceInterval einsteinScale hTransverse current hCurrent direction)
      .nonNullBoundary).2 =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
        period hPeriod metric einsteinScale current direction := by
  rw [programPT05GHYTwoSheetPhysicalLocalDV_integration_nonNull_eq_jet
    period hPeriod metric nullFaceInterval einsteinScale hTransverse current
    hCurrent direction]
  rw [programPT04T03MobileGHYBoundaryEuler_eq_twoSheetJet period hPeriod
    metric einsteinScale hTransverse current hCurrent]

end
end P0EFTJanusProgramPT05GHYStratifiedVerticalBridge4D
end JanusFormal
