import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurExplicitGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualSchurDeterminant4D

/-!
# Explicit Candidate-A Green operator from the finite Schur blocks

The finite determinant packet already proves that the augmented Candidate-A
Hessian is invertible.  This file exposes the stronger block formula for that
inverse and proves its two exact inverse identities against the actual Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActualSchurExplicitGreen4D

set_option autoImplicit false
set_option maxHeartbeats 8600000
set_option synthInstance.maxHeartbeats 4300000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurDeterminant4D
open P0EFTJanusProgramPFiniteModeSchurExplicitGreen4D

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

/-- Generic explicit-Green packet underlying one Candidate-A determinant
certificate. -/
def GlobalCandidateAActualSchurDeterminantData4D.toExplicitGreenData
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
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (determinantData : GlobalCandidateAActualSchurDeterminantData4D period
      hPeriod configuration data analysis chart sameAction physical Mode
        Complement) :
    FiniteModeSchurExplicitGreenData
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical)
      Mode Complement where
  blocks := determinantData.blockData.blocks
  determinant_ne_zero := determinantData.determinant_ne_zero

/-- Explicit Candidate-A propagator obtained from the Schur formula. -/
noncomputable def globalCandidateAActualSchurExplicitGreen
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
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (determinantData : GlobalCandidateAActualSchurDeterminantData4D period
      hPeriod configuration data analysis chart sameAction physical Mode
        Complement) :=
  finiteModeSchurExplicitGreen
    (determinantData.toExplicitGreenData period hPeriod)

@[simp]
theorem globalCandidateAActualSchurExplicitGreen_hessian
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
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (determinantData : GlobalCandidateAActualSchurDeterminantData4D period
      hPeriod configuration data analysis chart sameAction physical Mode
        Complement)
    (state : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    globalCandidateAActualSchurExplicitGreen period hPeriod determinantData
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical state) = state :=
  finiteModeSchurExplicitGreen_operator
    (determinantData.toExplicitGreenData period hPeriod) state

@[simp]
theorem globalCandidateAActualHessian_schurExplicitGreen
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
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (determinantData : GlobalCandidateAActualSchurDeterminantData4D period
      hPeriod configuration data analysis chart sameAction physical Mode
        Complement)
    (state : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical
        (globalCandidateAActualSchurExplicitGreen period hPeriod determinantData
          state) = state :=
  finiteModeSchur_operator_explicitGreen
    (determinantData.toExplicitGreenData period hPeriod) state

/-- Public Candidate-A explicit propagator checkpoint. -/
theorem global_candidateA_actual_schur_explicit_green_gate
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
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (determinantData : GlobalCandidateAActualSchurDeterminantData4D period
      hPeriod configuration data analysis chart sameAction physical Mode
        Complement) :
    (∀ state,
      globalCandidateAActualSchurExplicitGreen period hPeriod determinantData
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical state) = state) ∧
      (∀ state,
        globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical
            (globalCandidateAActualSchurExplicitGreen period hPeriod
              determinantData state) = state) :=
  ⟨globalCandidateAActualSchurExplicitGreen_hessian period hPeriod
      determinantData,
    globalCandidateAActualHessian_schurExplicitGreen period hPeriod
      determinantData⟩

end
end P0EFTJanusProgramPGlobalCandidateAActualSchurExplicitGreen4D
end JanusFormal
