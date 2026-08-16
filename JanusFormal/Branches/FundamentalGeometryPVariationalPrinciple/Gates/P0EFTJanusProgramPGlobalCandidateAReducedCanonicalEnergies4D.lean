import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPKernelComplementAmbientForms4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D

/-!
# Canonical Candidate-A energies on the actual zero-mode complement

The augmented Candidate-A Hessian is definitionally the sum of

* the diagonal BRST--SpinC--LL graph Hessian;
* the seven retained H11 physical blocks.

This file restricts those two genuine ambient forms to `(ker H_actual)ᗮ`.  The
principal, physical and total energies are therefore definitions, not extra
inputs.  Their exact sum follows from the unchanged augmented action, the H11
form norm controls the physical quadratic energy, and the total energy satisfies
the standard upper estimate against the reduced actual operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAReducedCanonicalEnergies4D

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option synthInstance.maxHeartbeats 2600000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPKernelComplementAmbientForms4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

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

private abbrev CandidateAHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) candidateAHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

private abbrev ActualOperator
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :=
  globalCandidateAActualKernelOperator period hPeriod configuration data analysis
    chart sameAction physical

private abbrev ActualComplement
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :=
  SelfAdjointKernelComplement
    (ActualOperator period hPeriod configuration data analysis chart sameAction
      physical)

/-- The canonical BRST--SpinC--LL principal form restricted to the actual
zero-mode complement. -/
def globalCandidateAReducedPrincipalForm
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    ActualComplement period hPeriod configuration data analysis chart sameAction
        physical →L[Real]
      ActualComplement period hPeriod configuration data analysis chart
        sameAction physical →L[Real] Real :=
  restrictBilinearToKernelComplement
    (ActualOperator period hPeriod configuration data analysis chart sameAction
      physical)
    (diagonalExtendedBulkL2Hessian period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)

/-- The canonical seven-block H11 form restricted to the actual complement. -/
def globalCandidateAReducedPhysicalForm
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    ActualComplement period hPeriod configuration data analysis chart sameAction
        physical →L[Real]
      ActualComplement period hPeriod configuration data analysis chart
        sameAction physical →L[Real] Real :=
  restrictBilinearToKernelComplement
    (ActualOperator period hPeriod configuration data analysis chart sameAction
      physical)
    physical.form

/-- The genuine augmented Hessian restricted to the actual complement. -/
def globalCandidateAReducedTotalForm
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    ActualComplement period hPeriod configuration data analysis chart sameAction
        physical →L[Real]
      ActualComplement period hPeriod configuration data analysis chart
        sameAction physical →L[Real] Real :=
  restrictBilinearToKernelComplement
    (ActualOperator period hPeriod configuration data analysis chart sameAction
      physical)
    (globalCandidateACommonAugmentedHessian period hPeriod configuration data
      analysis chart sameAction physical)

/-- The restricted total form is exactly principal plus physical. -/
theorem globalCandidateAReducedTotalForm_eq_add
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    globalCandidateAReducedTotalForm period hPeriod configuration data analysis
        chart sameAction physical =
      globalCandidateAReducedPrincipalForm period hPeriod configuration data
          analysis chart sameAction physical +
        globalCandidateAReducedPhysicalForm period hPeriod configuration data
          analysis chart sameAction physical := by
  ext first second
  rfl

/-- Symmetry of the canonical reduced principal form. -/
theorem globalCandidateAReducedPrincipalForm_symmetric
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (first second : ActualComplement period hPeriod configuration data analysis
      chart sameAction physical) :
    globalCandidateAReducedPrincipalForm period hPeriod configuration data
        analysis chart sameAction physical first second =
      globalCandidateAReducedPrincipalForm period hPeriod configuration data
        analysis chart sameAction physical second first := by
  exact restrictBilinearToKernelComplement_symmetric
    (ActualOperator period hPeriod configuration data analysis chart sameAction
      physical)
    (diagonalExtendedBulkL2Hessian period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    (diagonalExtendedBulkL2Hessian_comm period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    first second

/-- Canonical quadratic energies on the actual complement. -/
def globalCandidateAReducedPrincipalEnergy
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (vector : ActualComplement period hPeriod configuration data analysis chart
      sameAction physical) : Real :=
  globalCandidateAReducedPrincipalForm period hPeriod configuration data analysis
    chart sameAction physical vector vector

def globalCandidateAReducedPhysicalEnergy
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (vector : ActualComplement period hPeriod configuration data analysis chart
      sameAction physical) : Real :=
  globalCandidateAReducedPhysicalForm period hPeriod configuration data analysis
    chart sameAction physical vector vector

def globalCandidateAReducedTotalEnergy
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (vector : ActualComplement period hPeriod configuration data analysis chart
      sameAction physical) : Real :=
  globalCandidateAReducedTotalForm period hPeriod configuration data analysis
    chart sameAction physical vector vector

/-- Exact principal-plus-H11 identity. -/
theorem globalCandidateAReducedTotalEnergy_eq
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (vector : ActualComplement period hPeriod configuration data analysis chart
      sameAction physical) :
    globalCandidateAReducedTotalEnergy period hPeriod configuration data analysis
        chart sameAction physical vector =
      globalCandidateAReducedPrincipalForm period hPeriod configuration data
          analysis chart sameAction physical vector vector +
        globalCandidateAReducedPhysicalEnergy period hPeriod configuration data
          analysis chart sameAction physical vector := by
  rfl

/-- The H11 form norm controls the physical energy after restriction. -/
theorem globalCandidateAReducedPhysicalEnergy_bound
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (vector : ActualComplement period hPeriod configuration data analysis chart
      sameAction physical) :
    |globalCandidateAReducedPhysicalEnergy period hPeriod configuration data
        analysis chart sameAction physical vector| ≤
      ‖physical.form‖ * ‖vector‖ ^ 2 :=
  restrictBilinearToKernelComplement_quadratic_bound
    (ActualOperator period hPeriod configuration data analysis chart sameAction
      physical) physical.form vector

/-- The genuine total energy has the standard upper bound against the reduced
actual Hessian. -/
theorem globalCandidateAReducedTotalEnergy_upper
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (vector : ActualComplement period hPeriod configuration data analysis chart
      sameAction physical) :
    globalCandidateAReducedTotalEnergy period hPeriod configuration data analysis
        chart sameAction physical vector ≤
      ‖vector‖ *
        ‖selfAdjointKernelComplementOperator
          (ActualOperator period hPeriod configuration data analysis chart
            sameAction physical)
          (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
            configuration data analysis chart sameAction physical) vector‖ := by
  let operator := ActualOperator period hPeriod configuration data analysis chart
    sameAction physical
  let hSelfAdjoint := globalCandidateAActualKernelOperator_isSelfAdjoint period
    hPeriod configuration data analysis chart sameAction physical
  calc
    globalCandidateAReducedTotalEnergy period hPeriod configuration data analysis
        chart sameAction physical vector =
      inner Real (operator vector.1) vector.1 := by
        exact (globalCandidateACommonAugmentedRieszOperator_pairing period hPeriod
          configuration data analysis chart sameAction physical vector.1
            vector.1).symm
    _ = inner Real vector
        (selfAdjointKernelComplementOperator operator hSelfAdjoint vector) := by
      change inner Real (operator vector.1) vector.1 =
        inner Real vector.1 (operator vector.1)
      exact real_inner_comm _ _
    _ ≤ ‖vector‖ *
        ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ :=
      selfAdjointKernelComplement_energy_upper operator hSelfAdjoint vector

/-- A scalar majorant for the canonical H11 form. -/
structure GlobalCandidateAReducedPhysicalFormBound4D
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) : Prop where
  constant : Real
  constant_nonneg : 0 ≤ constant
  form_norm_le : ‖physical.form‖ ≤ constant

/-- The scalar majorant controls the reduced physical energy. -/
theorem GlobalCandidateAReducedPhysicalFormBound4D.energy_bound
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    (bound : GlobalCandidateAReducedPhysicalFormBound4D period hPeriod
      configuration data analysis chart sameAction physical)
    (vector : ActualComplement period hPeriod configuration data analysis chart
      sameAction physical) :
    |globalCandidateAReducedPhysicalEnergy period hPeriod configuration data
        analysis chart sameAction physical vector| ≤
      bound.constant * ‖vector‖ ^ 2 := by
  calc
    |globalCandidateAReducedPhysicalEnergy period hPeriod configuration data
        analysis chart sameAction physical vector| ≤
      ‖physical.form‖ * ‖vector‖ ^ 2 :=
        globalCandidateAReducedPhysicalEnergy_bound period hPeriod configuration
          data analysis chart sameAction physical vector
    _ ≤ bound.constant * ‖vector‖ ^ 2 :=
      mul_le_mul_of_nonneg_right bound.form_norm_le (sq_nonneg ‖vector‖)

/-- Public canonical-energy checkpoint. -/
theorem global_candidateA_reduced_canonical_energies_gate
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    (∀ first second,
      globalCandidateAReducedPrincipalForm period hPeriod configuration data
          analysis chart sameAction physical first second =
        globalCandidateAReducedPrincipalForm period hPeriod configuration data
          analysis chart sameAction physical second first) ∧
    (∀ vector,
      globalCandidateAReducedTotalEnergy period hPeriod configuration data
          analysis chart sameAction physical vector =
        globalCandidateAReducedPrincipalForm period hPeriod configuration data
            analysis chart sameAction physical vector vector +
          globalCandidateAReducedPhysicalEnergy period hPeriod configuration data
            analysis chart sameAction physical vector) ∧
    (∀ vector,
      |globalCandidateAReducedPhysicalEnergy period hPeriod configuration data
          analysis chart sameAction physical vector| ≤
        ‖physical.form‖ * ‖vector‖ ^ 2) ∧
    (∀ vector,
      globalCandidateAReducedTotalEnergy period hPeriod configuration data
          analysis chart sameAction physical vector ≤
        ‖vector‖ *
          ‖selfAdjointKernelComplementOperator
            (ActualOperator period hPeriod configuration data analysis chart
              sameAction physical)
            (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
              configuration data analysis chart sameAction physical) vector‖) :=
  ⟨globalCandidateAReducedPrincipalForm_symmetric period hPeriod configuration
      data analysis chart sameAction physical,
    globalCandidateAReducedTotalEnergy_eq period hPeriod configuration data
      analysis chart sameAction physical,
    globalCandidateAReducedPhysicalEnergy_bound period hPeriod configuration data
      analysis chart sameAction physical,
    globalCandidateAReducedTotalEnergy_upper period hPeriod configuration data
      analysis chart sameAction physical⟩

end
end P0EFTJanusProgramPGlobalCandidateAReducedCanonicalEnergies4D
end JanusFormal
