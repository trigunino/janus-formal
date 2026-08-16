import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorActualHessianCommutation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorCommutingActualKernelGap4D

/-!
# Concrete Candidate-A gap from the one commuting five-sector decomposition

This file specializes the generic commuting five-sector Gårding mechanism to
the genuine augmented Candidate-A Hessian.  The geometry is no longer supplied
as an unrelated complement decomposition: it is the completion-derived
resolution constrained on the H10 smooth core, and its commutation is obtained
from the exact off-diagonal block statement of the preceding file.

The remaining analytic input is irreducible:

* finite actual kernel;
* five diagonal principal lower bounds on the automatically restricted sectors;
* one norm bound for the complete off-diagonal principal remainder;
* one bounded H11 physical energy and its explicit smallness inequality;
* the standard energy upper bound against the reduced actual operator.

These data now produce `GlobalCandidateAActualKernelGap4D` directly, so the
existing closed-range, Fredholm, reduced-Green and H14 routes apply without a
second projection family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFiveSectorCommutingActualKernelGap4D

set_option autoImplicit false
set_option maxHeartbeats 7600000
set_option synthInstance.maxHeartbeats 3800000

noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorActualHessianCommutation4D
open P0EFTJanusProgramPCandidateAFiveSectorCommutingActualKernelGap4D
open P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D
open P0EFTJanusProgramPFiniteCommutingProjectionKernelComplement4D
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

/-- Concrete analytic packet on the actual complement generated by the one
completion-derived commuting sector resolution. -/
structure GlobalCandidateAFiveSectorCommutingActualKernelGapData4D
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
    (Metric Abelian Matter Longitudinal Boundary : Type*)
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary] : Prop where
  geometry : GlobalCandidateAFiveSectorActualHessianOffDiagonalZero4D period
    hPeriod configuration data analysis chart sameAction physical Metric Abelian
      Matter Longitudinal Boundary
  kernel_finite : FiniteDimensional Real
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical).ker
  principalForm : SelfAdjointKernelComplement
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical) →L[Real]
    SelfAdjointKernelComplement
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical) →L[Real] Real
  principal_symmetric : ∀ first second,
    principalForm first second = principalForm second first
  diagonalConstants : CandidateAFiveSectorDiagonalConstants
  diagonal_lower : ∀ sector vector,
    diagonalConstants.sectorConstant sector *
        ‖geometry.reducedResolution.projection sector vector‖ ^ 2 ≤
      principalForm
        (geometry.reducedResolution.projection sector vector)
        (geometry.reducedResolution.projection sector vector)
  offDiagonal_small :
    ‖principalForm -
      ∑ sector : CandidateAZeroModeSector,
        principalForm.bilinearComp
          (geometry.reducedResolution.projection sector)
          (geometry.reducedResolution.projection sector)‖ <
      diagonalConstants.sectorFloor
  physicalEnergy : SelfAdjointKernelComplement
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical) → Real
  physicalConstant : Real
  physicalConstant_nonneg : 0 ≤ physicalConstant
  physical_bound : ∀ vector,
    |physicalEnergy vector| ≤ physicalConstant * ‖vector‖ ^ 2
  physical_small : physicalConstant <
    diagonalConstants.sectorFloor -
      ‖principalForm -
        ∑ sector : CandidateAZeroModeSector,
          principalForm.bilinearComp
            (geometry.reducedResolution.projection sector)
            (geometry.reducedResolution.projection sector)‖
  totalEnergy : SelfAdjointKernelComplement
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical) → Real
  total_eq : ∀ vector,
    totalEnergy vector = principalForm vector vector + physicalEnergy vector
  energy_upper : ∀ vector,
    totalEnergy vector ≤ ‖vector‖ *
      ‖selfAdjointKernelComplementOperator
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical)
        (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
          configuration data analysis chart sameAction physical) vector‖
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

namespace GlobalCandidateAFiveSectorCommutingActualKernelGapData4D

/-- Forget only the global geometric spelling and obtain the established
generic commuting five-sector gap packet. -/
def toGeneric
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
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (input : GlobalCandidateAFiveSectorCommutingActualKernelGapData4D period
      hPeriod configuration data analysis chart sameAction physical Metric Abelian
        Matter Longitudinal Boundary) :
    CandidateAFiveSectorCommutingActualKernelGapData
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical)
      (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
        configuration data analysis chart sameAction physical)
      Metric Abelian Matter Longitudinal Boundary where
  kernel_finite := input.kernel_finite
  coordinates := input.geometry.orthogonalResolution.toGeneric
  commute := input.geometry.toCommutingResolution.commute
  principalForm := input.principalForm
  principal_symmetric := input.principal_symmetric
  diagonalConstants := input.diagonalConstants
  diagonal_lower := input.diagonal_lower
  offDiagonal_small := input.offDiagonal_small
  physicalEnergy := input.physicalEnergy
  physicalConstant := input.physicalConstant
  physicalConstant_nonneg := input.physicalConstant_nonneg
  physical_bound := input.physical_bound
  physical_small := input.physical_small
  totalEnergy := input.totalEnergy
  total_eq := input.total_eq
  energy_upper := input.energy_upper

/-- The concrete five-sector estimates produce the genuine Candidate-A H12 gap
packet consumed by all downstream analytic gates. -/
def toActualKernelGap
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
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (input : GlobalCandidateAFiveSectorCommutingActualKernelGapData4D period
      hPeriod configuration data analysis chart sameAction physical Metric Abelian
        Matter Longitudinal Boundary) :
    GlobalCandidateAActualKernelGap4D period hPeriod configuration data analysis
      chart sameAction physical where
  gapData := input.toGeneric.toGapData
  ll_stationary := input.ll_stationary

/-- Public checkpoint: the six concrete analytic inputs now close H12 for the
actual Candidate-A operator and expose its canonical reduced Green route. -/
theorem global_candidateA_five_sector_commuting_actual_kernel_gap_gate
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
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (input : GlobalCandidateAFiveSectorCommutingActualKernelGapData4D period
      hPeriod configuration data analysis chart sameAction physical Metric Abelian
        Matter Longitudinal Boundary) :
    GlobalCandidateAActualKernelGap4D period hPeriod configuration data analysis
      chart sameAction physical :=
  input.toActualKernelGap

end GlobalCandidateAFiveSectorCommutingActualKernelGapData4D

end
end P0EFTJanusProgramPGlobalCandidateAFiveSectorCommutingActualKernelGap4D
end JanusFormal
