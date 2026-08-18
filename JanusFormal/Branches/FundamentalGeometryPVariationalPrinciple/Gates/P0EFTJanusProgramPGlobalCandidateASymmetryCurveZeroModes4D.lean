import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSymmetryCurveHessianKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeAutomaticSplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D

/-!
# Candidate-A zero modes from genuine symmetry curves

The affine translation route is convenient for linearized gauge parameters,
but genuine gauge and diffeomorphism actions can trace nonlinear curves in a
configuration chart.  This file specializes the general symmetry-curve Noether
lemma to the actual augmented Candidate-A action.

The tangent of each curve is proved to lie in the kernel of the displayed
Riesz operator.  Independence and one global Gårding estimate then identify the
complete kernel and produce the H12 actual-kernel gap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASymmetryCurveZeroModes4D

set_option autoImplicit false
set_option maxHeartbeats 10800000
set_option synthInstance.maxHeartbeats 5400000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
open P0EFTJanusProgramPFiniteKernelNamedModeNoHidden4D
open P0EFTJanusProgramPFiniteKernelNamedModeAutomaticSplit4D
open P0EFTJanusProgramPSymmetryCurveHessianKernel4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

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

private abbrev CurveHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  ActualKernelHilbert period hPeriod configuration data analysis

/-- Finite family of genuine symmetry curves through the origin of the common
Hilbert chart. -/
structure GlobalCandidateASymmetryCurveModes4D
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
    (ZeroMode : Type*) [Fintype ZeroMode] where
  vector : ZeroMode → CurveHilbert period hPeriod configuration data analysis
  orbit : ∀ mode,
    SymmetryCurveAt
      (0 : CurveHilbert period hPeriod configuration data analysis)
      (vector mode)
  gradient_curve_invariant : ∀ mode,
    ActionGradientCurveEventuallyInvariantAt
      (globalCandidateACommonAugmentedAction period hPeriod configuration data
        analysis chart sameAction physical)
      (orbit mode)

/-- General-curve Noether identity for the actual Candidate-A Hessian form. -/
theorem GlobalCandidateASymmetryCurveModes4D.hessian_apply_eq_zero
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
    {ZeroMode : Type*} [Fintype ZeroMode]
    (modes : GlobalCandidateASymmetryCurveModes4D period hPeriod configuration
      data analysis chart sameAction physical ZeroMode)
    (mode : ZeroMode) :
    globalCandidateACommonAugmentedHessian period hPeriod configuration data
        analysis chart sameAction physical (modes.vector mode) = 0 := by
  have hGradient : DifferentiableAt Real
      (fun state => fderiv Real
        (globalCandidateACommonAugmentedAction period hPeriod configuration data
          analysis chart sameAction physical) state)
      (0 : CurveHilbert period hPeriod configuration data analysis) := by
    have hFunction :
        (fun state => fderiv Real
          (globalCandidateACommonAugmentedAction period hPeriod configuration
            data analysis chart sameAction physical) state) =
        fun state => globalCandidateACommonAugmentedHessian period hPeriod
          configuration data analysis chart sameAction physical state := by
      funext state
      exact globalCandidateACommonAugmentedAction_fderiv period hPeriod
        configuration data analysis chart sameAction physical state
    rw [hFunction]
    exact (globalCandidateACommonAugmentedHessian period hPeriod configuration
      data analysis chart sameAction physical).differentiableAt
  have hNoether := secondFrechet_apply_eq_zero_of_gradientCurveInvariant
    (globalCandidateACommonAugmentedAction period hPeriod configuration data
      analysis chart sameAction physical)
    (0 : CurveHilbert period hPeriod configuration data analysis)
    (modes.vector mode) (modes.orbit mode) hGradient
    (modes.gradient_curve_invariant mode)
  have hSecond := congrArg
    (fun derivative : CurveHilbert period hPeriod configuration data analysis →L[Real]
        (CurveHilbert period hPeriod configuration data analysis →L[Real] Real) =>
      derivative (modes.vector mode))
    (globalCandidateACommonAugmentedAction_second_fderiv period hPeriod
      configuration data analysis chart sameAction physical 0)
  exact hSecond.symm.trans hNoether

/-- General-curve symmetry vectors lie in the actual Riesz kernel. -/
theorem GlobalCandidateASymmetryCurveModes4D.vector_annihilated
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
    {ZeroMode : Type*} [Fintype ZeroMode]
    (modes : GlobalCandidateASymmetryCurveModes4D period hPeriod configuration
      data analysis chart sameAction physical ZeroMode)
    (mode : ZeroMode) :
    globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical (modes.vector mode) = 0 := by
  let operator := globalCandidateAActualKernelOperator period hPeriod
    configuration data analysis chart sameAction physical
  have hForm := modes.hessian_apply_eq_zero period hPeriod mode
  have hPair : inner Real (operator (modes.vector mode))
      (operator (modes.vector mode)) = 0 := by
    calc
      inner Real (operator (modes.vector mode))
          (operator (modes.vector mode)) =
        globalCandidateACommonAugmentedHessian period hPeriod configuration data
          analysis chart sameAction physical (modes.vector mode)
            (operator (modes.vector mode)) := by
          change inner Real
              (globalCandidateACommonAugmentedRieszOperator period hPeriod
                configuration data analysis chart sameAction physical
                  (modes.vector mode))
              (globalCandidateACommonAugmentedRieszOperator period hPeriod
                configuration data analysis chart sameAction physical
                  (modes.vector mode)) = _
          exact globalCandidateACommonAugmentedRieszOperator_pairing period
            hPeriod configuration data analysis chart sameAction physical
              (modes.vector mode)
              (globalCandidateACommonAugmentedRieszOperator period hPeriod
                configuration data analysis chart sameAction physical
                  (modes.vector mode))
      _ = 0 := by rw [hForm]; simp
  have hNormSq : ‖operator (modes.vector mode)‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hPair
  have hNorm : ‖operator (modes.vector mode)‖ = 0 := by
    nlinarith [norm_nonneg (operator (modes.vector mode))]
  exact norm_eq_zero.mp hNorm

/-- Complete curve-symmetry/Gårding packet. -/
structure GlobalCandidateASymmetryCurveAutomaticSplit4D
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
    (ZeroMode : Type*) [Fintype ZeroMode] where
  curves : GlobalCandidateASymmetryCurveModes4D period hPeriod configuration
    data analysis chart sameAction physical ZeroMode
  linearIndependent : LinearIndependent Real
    (finiteKernelNamedVector
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical)
      curves.vector (curves.vector_annihilated period hPeriod))
  constant : Real
  constant_pos : 0 < constant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  garding : ∀ current : CurveHilbert period hPeriod configuration data analysis,
    constant * ‖current‖ ^ 2 ≤
      inner Real current
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical current) +
        defectConstant *
          ∑ mode : ZeroMode, (inner Real current (curves.vector mode)) ^ 2
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Convert curve symmetries to the generic automatic split. -/
def GlobalCandidateASymmetryCurveAutomaticSplit4D.toAutomaticSplit
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
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateASymmetryCurveAutomaticSplit4D period hPeriod
      configuration data analysis chart sameAction physical ZeroMode) :
    FiniteKernelNamedModeAutomaticSplitData
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical) ZeroMode where
  vector := input.curves.vector
  annihilated := input.curves.vector_annihilated period hPeriod
  linearIndependent := input.linearIndependent
  constant := input.constant
  constant_pos := input.constant_pos
  defectConstant := input.defectConstant
  defectConstant_nonneg := input.defectConstant_nonneg
  garding := input.garding

/-- Curve symmetries construct the actual-kernel gap. -/
def GlobalCandidateASymmetryCurveAutomaticSplit4D.toActualKernelGap
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
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateASymmetryCurveAutomaticSplit4D period hPeriod
      configuration data analysis chart sameAction physical ZeroMode) :
    GlobalCandidateAActualKernelGap4D period hPeriod configuration data analysis
      chart sameAction physical where
  gapData := input.toAutomaticSplit.toNoHidden.toNamedGarding.toGapData
    (hSelfAdjoint := globalCandidateAActualKernelOperator_isSelfAdjoint period
      hPeriod configuration data analysis chart sameAction physical)
  ll_stationary := input.ll_stationary

/-- Public general-orbit Candidate-A checkpoint. -/
def global_candidateA_symmetry_curve_zero_mode_gate
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
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateASymmetryCurveAutomaticSplit4D period hPeriod
      configuration data analysis chart sameAction physical ZeroMode) :
    PSigma fun _ : GlobalCandidateAActualKernelGap4D period hPeriod
        configuration data analysis chart sameAction physical =>
      Module.finrank Real
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical).ker = Fintype.card ZeroMode := by
  let named := input.toAutomaticSplit.toNoHidden.toNamedGarding
  exact ⟨input.toActualKernelGap period hPeriod,
    named.spanning.kernel_finrank_eq_card⟩

end
end P0EFTJanusProgramPGlobalCandidateASymmetryCurveZeroModes4D
end JanusFormal
