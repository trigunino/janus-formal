import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D

/-!
# Total seven-physical quadratic action from one H11 extension or bound

A single common-domain extension of the total seven-block Hessian descends to
the minimal physical reduced Hilbert completion.  Its quadratic action has the
exact Frechet derivative and strong Riesz representative.  A single dense-core
product bound supplies the extension through the canonical H11 constructor.

This is the total base-point quadratic endpoint parallel to the blockwise
construction.  It does not separate the GHY block from the other six blocks,
and therefore does not replace the genuine Robin decomposition of Gate 193.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedSevenPhysicalQuadraticActionOfBound4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMaxwellQuadraticAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction4D

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

private abbrev MinimalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev SameAction :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis chartData

private abbrev Core :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev Reduced :=
  GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
    data analysis

/-- Regard the aggregate seven-physical extension as one common-domain block. -/
def globalCandidateASevenPhysicalCommonDomainExtensionAsBlock
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)) :
    GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
      configuration data analysis
        (diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period
          hPeriod configuration data analysis
          (MinimalChart period hPeriod configuration data analysis chartData)
          (SameAction period hPeriod configuration data analysis
            chartData).chartBridge) where
  form := physical.form
  symmetric := physical.symmetric
  smooth_agreement := physical.smooth_agreement

private theorem sevenPhysicalTotal_core_left_zero
    (first second : Core period hPeriod configuration analysis)
    (hFirst : first ∈
      globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
        configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis
          chartData).chartBridge first second = 0 := by
  have hTangent := LinearMap.mem_ker.mp hFirst
  unfold diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
  simp [hTangent]

/-- Total seven-physical Hessian obtained from one aggregate extension. -/
def globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)) :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis →L[Real] Real :=
  reducedBlockForm period hPeriod configuration data analysis
    (globalCandidateASevenPhysicalCommonDomainExtensionAsBlock period hPeriod
      configuration data analysis chartData physical)

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension_symmetric
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData))
    (first second : Reduced period hPeriod configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension
        period hPeriod configuration data analysis chartData physical first second =
      globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension
        period hPeriod configuration data analysis chartData physical second first := by
  change physical.form _ _ = physical.form _ _
  exact physical.symmetric _ _

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension_core
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData))
    (first second : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension
        period hPeriod configuration data analysis chartData physical
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk first))
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk second)) =
      diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
        configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis
          chartData).chartBridge first second := by
  exact reducedBlockForm_core period hPeriod configuration data analysis
    (diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
      configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis
        chartData).chartBridge)
    (globalCandidateASevenPhysicalCommonDomainExtensionAsBlock period hPeriod
      configuration data analysis chartData physical)
    (sevenPhysicalTotal_core_left_zero period hPeriod configuration data analysis
      chartData) first second

/-- Total base-point quadratic action supplied by an aggregate extension. -/
def globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)) :
    Reduced period hPeriod configuration data analysis → Real :=
  fun state => (1 / 2 : Real) *
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension
      period hPeriod configuration data analysis chartData physical state state

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension_contDiff
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)) :
    ContDiff Real ⊤
      (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension
        period hPeriod configuration data analysis chartData physical) := by
  unfold globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension
  exact contDiff_const.mul
    ((globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension
      period hPeriod configuration data analysis chartData physical
      ).contDiff.clm_apply contDiff_id)

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension_contDiff_two
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)) :
    ContDiff Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension
        period hPeriod configuration data analysis chartData physical) :=
  (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension_contDiff
    period hPeriod configuration data analysis chartData physical).of_le (by simp)

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension_fderiv
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData))
    (state : Reduced period hPeriod configuration data analysis) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension
          period hPeriod configuration data analysis chartData physical) state =
      globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension
        period hPeriod configuration data analysis chartData physical state := by
  exact (symmetricQuadratic_hasFDerivAt
    (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension
      period hPeriod configuration data analysis chartData physical)
    (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension_symmetric
      period hPeriod configuration data analysis chartData physical) state).fderiv

/-- Strong Riesz representative of the aggregate seven-physical Hessian. -/
def globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_commonExtension
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)) :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis :=
  @InnerProductSpace.continuousLinearMapOfBilin
    Real (Reduced period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance inferInstance
    (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension
      period hPeriod configuration data analysis chartData physical)

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_commonExtension_pairing
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData))
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_commonExtension
          period hPeriod configuration data analysis chartData physical state) test =
      globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension
        period hPeriod configuration data analysis chartData physical state test := by
  exact @InnerProductSpace.continuousLinearMapOfBilin_apply
    Real (Reduced period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance inferInstance
    (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension
      period hPeriod configuration data analysis chartData physical) state test

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_commonExtension_gradient_pairing
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData))
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_commonExtension
          period hPeriod configuration data analysis chartData physical state) test =
      fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension
          period hPeriod configuration data analysis chartData physical) state test := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_commonExtension_pairing,
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension_fderiv]

/-- Strong criticality for the aggregate seven-physical quadratic action. -/
def GlobalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticIsCritical_of_commonExtension
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData))
    (state : Reduced period hPeriod configuration data analysis) : Prop :=
  globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_commonExtension
    period hPeriod configuration data analysis chartData physical state = 0

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticIsCritical_of_commonExtension_iff_fderiv_eq_zero
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData))
    (state : Reduced period hPeriod configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticIsCritical_of_commonExtension
        period hPeriod configuration data analysis chartData physical state ↔
      fderiv Real
          (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension
            period hPeriod configuration data analysis chartData physical) state =
        0 := by
  constructor
  · intro hCritical
    rw [globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension_fderiv]
    apply ContinuousLinearMap.ext
    intro test
    rw [← globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_commonExtension_pairing,
      hCritical]
    simp
  · intro hDerivative
    unfold GlobalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticIsCritical_of_commonExtension
    apply (inner_self_eq_zero (𝕜 := Real)).mp
    rw [globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_commonExtension_gradient_pairing,
      hDerivative]
    simp

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension_core
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData))
    (core : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension
        period hPeriod configuration data analysis chartData physical
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      (1 / 2 : Real) *
        diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
          configuration data analysis
          (MinimalChart period hPeriod configuration data analysis chartData)
          (SameAction period hPeriod configuration data analysis
            chartData).chartBridge core core := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension,
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension_core]

/-! ## Canonical wrappers from one dense-core product bound -/

variable
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData))

private abbrev PhysicalOfBound :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_bound period hPeriod
    configuration data analysis
    (MinimalChart period hPeriod configuration data analysis chartData)
    (SameAction period hPeriod configuration data analysis chartData) bound

/-- Total reduced Hessian canonically constructed from one H11 bound. -/
def globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_bound :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis →L[Real] Real :=
  globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension
    period hPeriod configuration data analysis chartData
      (PhysicalOfBound period hPeriod configuration data analysis chartData bound)

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_bound_symmetric
    (first second : Reduced period hPeriod configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_bound
        period hPeriod configuration data analysis chartData bound first second =
      globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_bound
        period hPeriod configuration data analysis chartData bound second first := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_commonExtension_symmetric
      period hPeriod configuration data analysis chartData
        (PhysicalOfBound period hPeriod configuration data analysis chartData bound)
        first second

/-- Total quadratic action canonically constructed from one H11 bound. -/
def globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_bound :
    Reduced period hPeriod configuration data analysis → Real :=
  globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension
    period hPeriod configuration data analysis chartData
      (PhysicalOfBound period hPeriod configuration data analysis chartData bound)

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_bound_contDiff_two :
    ContDiff Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_bound
        period hPeriod configuration data analysis chartData bound) := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension_contDiff_two
      period hPeriod configuration data analysis chartData
        (PhysicalOfBound period hPeriod configuration data analysis chartData bound)

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_bound_fderiv
    (state : Reduced period hPeriod configuration data analysis) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_bound
          period hPeriod configuration data analysis chartData bound) state =
      globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_bound
        period hPeriod configuration data analysis chartData bound state := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension_fderiv
      period hPeriod configuration data analysis chartData
        (PhysicalOfBound period hPeriod configuration data analysis chartData bound)
        state

/-- Strong Riesz representative canonically constructed from one H11 bound. -/
def globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_bound :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis :=
  globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_commonExtension
    period hPeriod configuration data analysis chartData
      (PhysicalOfBound period hPeriod configuration data analysis chartData bound)

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_bound_pairing
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_bound
          period hPeriod configuration data analysis chartData bound state) test =
      globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalHessian_of_bound
        period hPeriod configuration data analysis chartData bound state test := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_commonExtension_pairing
      period hPeriod configuration data analysis chartData
        (PhysicalOfBound period hPeriod configuration data analysis chartData bound)
        state test

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_bound_gradient_pairing
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_bound
          period hPeriod configuration data analysis chartData bound state) test =
      fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_bound
          period hPeriod configuration data analysis chartData bound) state test := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_commonExtension_gradient_pairing
      period hPeriod configuration data analysis chartData
        (PhysicalOfBound period hPeriod configuration data analysis chartData bound)
        state test

/-- Strong criticality for the quadratic action canonically built from one
dense-core product bound. -/
def GlobalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticIsCritical_of_bound
    (state : Reduced period hPeriod configuration data analysis) : Prop :=
  globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalRieszOperator_of_bound
    period hPeriod configuration data analysis chartData bound state = 0

theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticIsCritical_of_bound_iff_fderiv_eq_zero
    (state : Reduced period hPeriod configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticIsCritical_of_bound
        period hPeriod configuration data analysis chartData bound state ↔
      fderiv Real
          (globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_bound
            period hPeriod configuration data analysis chartData bound) state = 0 := by
  change
    GlobalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticIsCritical_of_commonExtension
        period hPeriod configuration data analysis chartData
          (PhysicalOfBound period hPeriod configuration data analysis chartData bound)
          state ↔ _
  exact
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticIsCritical_of_commonExtension_iff_fderiv_eq_zero
      period hPeriod configuration data analysis chartData
        (PhysicalOfBound period hPeriod configuration data analysis chartData bound)
        state

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_bound_core
    (core : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_bound
        period hPeriod configuration data analysis chartData bound
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      (1 / 2 : Real) *
        diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
          configuration data analysis
          (MinimalChart period hPeriod configuration data analysis chartData)
          (SameAction period hPeriod configuration data analysis
            chartData).chartBridge core core := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction_of_commonExtension_core
      period hPeriod configuration data analysis chartData
        (PhysicalOfBound period hPeriod configuration data analysis chartData bound)
        core

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedSevenPhysicalQuadraticActionOfBound4D
end JanusFormal
