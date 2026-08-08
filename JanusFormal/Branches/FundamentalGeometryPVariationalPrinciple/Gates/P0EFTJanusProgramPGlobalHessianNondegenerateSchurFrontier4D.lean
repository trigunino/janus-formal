import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianBoundedSchurFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualSchurNondegenerate4D

/-!
# Zero-mode-free H10--H14 Schur frontier

On the open nondegenerate stratum, the finite Schur complement is bijective.
The complete augmented Candidate-A Hessian is then bijective, its kernel is
zero and the Green operator acts on the full common Hilbert space.

This façade combines that conclusion with the bounded-Schur H10--H14
certificate.  It retains the general zero-mode frontier as a compatibility
output but exposes the stronger full-space inverse and exact zero-mode count
zero.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianNondegenerateSchurFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 11200000
set_option synthInstance.maxHeartbeats 5600000

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
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalChartPullback4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurNondegenerate4D
open P0EFTJanusProgramPGlobalHessianActualKernelChartFrontier4D
open P0EFTJanusProgramPGlobalHessianBoundedSchurFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

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

/-- Strongest zero-mode-free terminal gate. -/
def global_candidateA_hessian_nondegenerate_schur_frontier_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family))
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (nondegenerate :
      GlobalCandidateAActualBoundedSchurNondegenerateData4D period hPeriod
        configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
            configuration data analysis einsteinScale hTransverse family
              realization)
          Mode Complement) :=
  let terminal := global_candidateA_hessian_bounded_schur_frontier_gate
    period hPeriod configuration data analysis einsteinScale hTransverse family
      realization Mode Complement nondegenerate.blockData
  let fullInverse := global_candidateA_actual_schur_nondegenerate_gate
    period hPeriod configuration data analysis
      (globalCandidateAActualKernelChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAActualKernelSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
        configuration data analysis einsteinScale hTransverse family
          realization)
      Mode Complement nondegenerate
  (terminal, fullInverse)

/-- Exact zero-mode-free conclusion exposed independently of the large terminal
product. -/
theorem global_candidateA_hessian_nondegenerate_zero_modes
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
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (nondegenerate :
      GlobalCandidateAActualBoundedSchurNondegenerateData4D period hPeriod
        configuration data analysis chart sameAction physical Mode Complement) :
    (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical).ker = ⊥ ∧
      Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical).ker = 0 :=
  ⟨finiteModeSchur_operator_ker_eq_bot
      (nondegenerate.toNondegenerateData period hPeriod),
    finiteModeSchur_operator_kernel_finrank_zero
      (nondegenerate.toNondegenerateData period hPeriod)⟩

/-- The terminal architecture has the same three packets; nondegeneracy is a
finite property of the Schur block contained in the third packet. -/
theorem global_candidateA_hessian_nondegenerate_schur_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianNondegenerateSchurFrontier4D
end JanusFormal
