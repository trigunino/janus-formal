import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCompactIdentityFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFiniteKernel4D
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Fredholm stability of the physical Friedrichs family

The reference D11 operator is stabilized by its finite kernel projection.
Factoring the compact physical perturbation through that stabilization reduces
each physical fibre to identity plus a compact operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFredholm4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalRealFredholm4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusLinearPMapProdIdentityFredholm4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPCompactIdentityFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszCompact4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFiniteKernel4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

local instance programPT12GaugeFixedSpectralModeDecidableEq
    (iota : Type*) [DecidableEq iota] :
    DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode iota) :=
  Classical.decEq _

/-- The kernel projection complementary to the existing range projection. -/
def programPT12GaugeFixedLLFriedrichsD11KernelProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  ContinuousLinearMap.id Real _ -
    programPT12GaugeFixedLLFriedrichsD11RangeProjection
      period hPeriod covector matterMass analysis

@[simp]
theorem programPT12GaugeFixedLLFriedrichsD11KernelProjection_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis) :
    programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector matterMass analysis state =
      state - programPT12GaugeFixedLLFriedrichsD11RangeProjection
      period hPeriod covector matterMass analysis state := by
  rfl

theorem programPT12GaugeFixedLLFriedrichsD11KernelProjection_compact
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector matterMass analysis) := by
  have hProjection :
      programPT12GaugeFixedLLFriedrichsD11KernelProjection
          period hPeriod covector matterMass analysis =
        P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFiniteKernel4D.programPT12GaugeFixedLLFriedrichsD11KernelProjection
            period hPeriod covector matterMass analysis := by
    ext state
    rw [programPT12GaugeFixedLLFriedrichsD11KernelProjection_apply,
      P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFiniteKernel4D.programPT12GaugeFixedLLFriedrichsD11KernelProjection_apply]
  rw [hProjection]
  exact
    P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFiniteKernel4D.programPT12GaugeFixedLLFriedrichsD11KernelProjection_compact
        period hPeriod d9Ellipticity matterMass analysis

def complexDiagonalZeroProjectionDomainElement
    {Mode : Type*} [DecidableEq Mode]
    (weight : Mode → Real)
    (state : ComplexDiagonalHilbert Mode) :
    (complexDiagonalRealOperator Mode weight).domain := by
  let kernelState :=
    state - complexDiagonalZeroComplementProjectionCLM weight state
  refine ⟨kernelState, ?_⟩
  change kernelState ∈ complexDiagonalDomain _ weight
  refine ⟨0, ?_⟩
  intro mode
  by_cases hZero : weight mode = 0
  · simp [kernelState, complexDiagonalZeroComplementProjectionCLM_apply,
      complexDiagonalZeroComplementImage_apply, hZero]
  · simp [kernelState, complexDiagonalZeroComplementProjectionCLM_apply,
      complexDiagonalZeroComplementImage_apply, hZero]

@[simp]
theorem complexDiagonalZeroProjectionDomainElement_coe
    {Mode : Type*} [DecidableEq Mode]
    (weight : Mode → Real)
    (state : ComplexDiagonalHilbert Mode) :
    (complexDiagonalZeroProjectionDomainElement weight state :
      ComplexDiagonalHilbert Mode) =
      state - complexDiagonalZeroComplementProjectionCLM weight state :=
  rfl

theorem complexDiagonalZeroProjectionDomainElement_kernel
    {Mode : Type*} [DecidableEq Mode]
    (weight : Mode → Real)
    (state : ComplexDiagonalHilbert Mode) :
    complexDiagonalRealOperator Mode weight
      (complexDiagonalZeroProjectionDomainElement weight state) = 0 := by
  ext mode
  rw [complexDiagonalRealOperator_apply,
    complexDiagonalZeroProjectionDomainElement_coe]
  by_cases hZero : weight mode = 0
  · simp [hZero]
  · simp [complexDiagonalZeroComplementProjectionCLM_apply,
      complexDiagonalZeroComplementImage_apply, hZero]

/-- The kernel projection, regarded as an element of the common graph domain. -/
def programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (state : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis) :
    (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector matterMass analysis parameter).domain := by
  let weight := programPGlobalGaugeFixedSpectralHessianWeight
    period hPeriod covector matterMass
  let spectralState := (WithLp.ofLp state).1
  let spectralKernel :=
    complexDiagonalZeroProjectionDomainElement weight spectralState
  refine ⟨WithLp.toLp 2 ((spectralKernel : _), 0), ?_⟩
  change (spectralKernel : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota) ∈
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).domain ∧
    (0 : CanonicalLLL2 period hPeriod analysis) ∈
      (programPT12GaugeFixedLLFriedrichsD11LLOperator
        period hPeriod analysis parameter).domain
  exact ⟨spectralKernel.property, Submodule.zero_mem _⟩

@[simp]
theorem programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement_coe
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (state : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis) :
    (programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement
        period hPeriod covector matterMass analysis parameter state :
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis) =
      programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector matterMass analysis state := by
  rw [programPT12GaugeFixedLLFriedrichsD11KernelProjection,
    programPT12GaugeFixedLLFriedrichsD11RangeProjection]
  apply (WithLp.prodContinuousLinearEquiv 2 Real
    (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
    (CanonicalLLL2 period hPeriod analysis)).injective
  apply Prod.ext
  · rfl
  · simp [programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement,
      withLpTwoProdMap_apply]

theorem programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement_kernel
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (state : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis) :
    programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis parameter
        (programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement
          period hPeriod covector matterMass analysis parameter state) = 0 := by
  change linearPMapProd _ _
      (programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement
        period hPeriod covector matterMass analysis parameter state) = 0
  rw [linearPMapProd_apply]
  change WithLp.toLp 2
      (complexDiagonalRealOperator _ _
          (complexDiagonalZeroProjectionDomainElement
            (programPGlobalGaugeFixedSpectralHessianWeight
              period hPeriod covector matterMass) (WithLp.ofLp state).1),
        programPT12GaugeFixedLLFriedrichsD11LLOperator
          period hPeriod analysis parameter 0) = 0
  rw [complexDiagonalZeroProjectionDomainElement_kernel]
  have hLLZero :
      programPT12GaugeFixedLLFriedrichsD11LLOperator
          period hPeriod analysis parameter 0 = 0 :=
    (programPT12GaugeFixedLLFriedrichsD11LLOperator
      period hPeriod analysis parameter).toFun.map_zero
  rw [hLLZero]
  rfl

@[simp]
theorem programPT12GaugeFixedLLFriedrichsD11GreenDomainElement_coe
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (state : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis) :
    (programPT12GaugeFixedLLFriedrichsD11GreenDomainElement
        period hPeriod d9Ellipticity matterMass analysis parameter state :
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis) =
      programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity matterMass analysis parameter state := by
  rfl

def programPT12GaugeFixedLLFriedrichsD11GreenDomainLift
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →ₗ[Real]
      (programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis parameter).domain where
  toFun := fun state =>
    ⟨programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity matterMass analysis parameter state, by
      rw [← programPT12GaugeFixedLLFriedrichsD11GreenDomainElement_coe
        period hPeriod d9Ellipticity matterMass analysis parameter state]
      exact (programPT12GaugeFixedLLFriedrichsD11GreenDomainElement
        period hPeriod d9Ellipticity matterMass analysis parameter state).property⟩
  map_add' := by
    intro first second
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' := by
    intro scalar state
    apply Subtype.ext
    exact map_smul _ _ _

def programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainLift
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →ₗ[Real]
      (programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis parameter).domain where
  toFun := fun state =>
    ⟨programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector matterMass analysis state, by
      rw [← programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement_coe
        period hPeriod covector matterMass analysis parameter state]
      exact (programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement
        period hPeriod covector matterMass analysis parameter state).property⟩
  map_add' := by
    intro first second
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' := by
    intro scalar state
    apply Subtype.ext
    exact map_smul _ _ _

/-- Algebraic core of the stabilization `A + Q`, with inverse `G + Q`. -/
theorem linearPMap_stabilization_twoSidedInverse
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    (operator : E →ₗ.[Real] E)
    (green rangeProjection kernelProjection : E →L[Real] E)
    (greenLift kernelLift : E →ₗ[Real] operator.domain)
    (hGreenLift : ∀ state, (greenLift state).1 = green state)
    (hKernelLift : ∀ state, (kernelLift state).1 = kernelProjection state)
    (hRight : ∀ state, operator (greenLift state) = rangeProjection state)
    (hLeft : ∀ state : operator.domain,
      green (operator state) = rangeProjection state.1)
    (hKernel : ∀ state, operator (kernelLift state) = 0)
    (hComplement : ∀ state,
      kernelProjection state = state - rangeProjection state)
    (hGreenKernel : ∀ state, green (kernelProjection state) = 0) :
    Function.LeftInverse (greenLift + kernelLift)
        (kernelProjection.toLinearMap +ᵥ operator).toFun ∧
      Function.RightInverse (greenLift + kernelLift)
        (kernelProjection.toLinearMap +ᵥ operator).toFun := by
  have hRangeKernel : ∀ state,
      rangeProjection (kernelProjection state) = 0 := by
    intro state
    calc
      rangeProjection (kernelProjection state) =
          rangeProjection (kernelLift state).1 := by rw [hKernelLift]
      _ = green (operator (kernelLift state)) := (hLeft _).symm
      _ = 0 := by rw [hKernel, map_zero]
  have hKernelIdem : ∀ state,
      kernelProjection (kernelProjection state) = kernelProjection state := by
    intro state
    rw [hComplement, hRangeKernel, sub_zero]
  have hRangeGreen : ∀ state,
      rangeProjection (green state) = green state := by
    intro state
    calc
      rangeProjection (green state) =
          rangeProjection (greenLift state).1 := by rw [hGreenLift]
      _ = green (operator (greenLift state)) := (hLeft _).symm
      _ = green (rangeProjection state) := by rw [hRight]
      _ = green (state - kernelProjection state) := by
        rw [hComplement]
        abel
      _ = green state - green (kernelProjection state) := by rw [map_sub]
      _ = green state := by rw [hGreenKernel, sub_zero]
  have hKernelGreen : ∀ state,
      kernelProjection (green state) = 0 := by
    intro state
    rw [hComplement, hRangeGreen, sub_self]
  have hLiftLeft : ∀ state : operator.domain,
      greenLift (operator state) = state - kernelLift state := by
    intro state
    apply Subtype.ext
    change (greenLift (operator state)).1 =
      state.1 - (kernelLift state.1).1
    rw [hGreenLift, hKernelLift, hLeft, hComplement]
    abel
  have hKernelImage : ∀ state : operator.domain,
      kernelProjection (operator state) = 0 := by
    intro state
    calc
      kernelProjection (operator state) =
          operator state - rangeProjection (operator state) :=
        hComplement _
      _ = operator state - operator (greenLift (operator state)) := by
        rw [hRight]
      _ = operator state - operator (state - kernelLift state.1) := by
        rw [hLiftLeft]
      _ = operator state -
          (operator state - operator (kernelLift state.1)) := by
        apply congrArg (fun value : E => operator state - value)
        exact operator.toFun.map_sub state (kernelLift state.1)
      _ = 0 := by rw [hKernel]; abel
  constructor
  · intro state
    apply Subtype.ext
    change
      (greenLift
          ((kernelProjection.toLinearMap +ᵥ operator).toFun state)).1 +
        (kernelLift
          ((kernelProjection.toLinearMap +ᵥ operator).toFun state)).1 =
        state.1
    rw [hGreenLift, hKernelLift]
    change green (kernelProjection state.1 + operator state) +
      kernelProjection (kernelProjection state.1 + operator state) = state.1
    rw [map_add, map_add, hGreenKernel, hLeft, hKernelIdem,
      hKernelImage, zero_add, add_zero, hComplement]
    abel
  · intro state
    change kernelProjection ((greenLift + kernelLift) state).1 +
      operator ((greenLift + kernelLift) state) = state
    change kernelProjection ((greenLift state).1 + (kernelLift state).1) +
      operator (greenLift state + kernelLift state) = state
    have hOperatorAdd :
        operator (greenLift state + kernelLift state) =
          operator (greenLift state) + operator (kernelLift state) :=
      operator.toFun.map_add _ _
    rw [hGreenLift, hKernelLift, map_add, hOperatorAdd,
      hKernelGreen, hKernelIdem, hRight, hKernel,
      zero_add, add_zero, hComplement]
    abel

def programPT12GaugeFixedLLFriedrichsD11StabilizedOperator
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →ₗ.[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  (programPT12GaugeFixedLLFriedrichsD11KernelProjection
      period hPeriod covector matterMass analysis).toLinearMap +ᵥ
    programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector matterMass analysis parameter

def programPT12GaugeFixedLLFriedrichsD11StabilizedInverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →ₗ[Real]
      (programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis parameter).domain :=
  programPT12GaugeFixedLLFriedrichsD11GreenDomainLift
      period hPeriod d9Ellipticity matterMass analysis parameter +
    programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainLift
      period hPeriod covector matterMass analysis parameter

def programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  programPT12GaugeFixedLLFriedrichsD11GreenOperator
      period hPeriod d9Ellipticity matterMass analysis parameter +
    programPT12GaugeFixedLLFriedrichsD11KernelProjection
      period hPeriod covector matterMass analysis

@[simp]
theorem programPT12GaugeFixedLLFriedrichsD11StabilizedInverse_coe
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (state : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis) :
    (programPT12GaugeFixedLLFriedrichsD11StabilizedInverse
        period hPeriod d9Ellipticity matterMass analysis parameter state :
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis) =
      programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
        period hPeriod d9Ellipticity matterMass analysis parameter state :=
  rfl

theorem programPT12GaugeFixedLLFriedrichsD11Stabilization_twoSidedInverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    Function.LeftInverse
        (programPT12GaugeFixedLLFriedrichsD11StabilizedInverse
          period hPeriod d9Ellipticity matterMass analysis parameter)
        (programPT12GaugeFixedLLFriedrichsD11StabilizedOperator
          period hPeriod covector matterMass analysis parameter).toFun ∧
      Function.RightInverse
        (programPT12GaugeFixedLLFriedrichsD11StabilizedInverse
          period hPeriod d9Ellipticity matterMass analysis parameter)
        (programPT12GaugeFixedLLFriedrichsD11StabilizedOperator
          period hPeriod covector matterMass analysis parameter).toFun := by
  apply linearPMap_stabilization_twoSidedInverse
    (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector matterMass analysis parameter)
    (programPT12GaugeFixedLLFriedrichsD11GreenOperator
      period hPeriod d9Ellipticity matterMass analysis parameter)
    (programPT12GaugeFixedLLFriedrichsD11RangeProjection
      period hPeriod covector matterMass analysis)
    (programPT12GaugeFixedLLFriedrichsD11KernelProjection
      period hPeriod covector matterMass analysis)
    (programPT12GaugeFixedLLFriedrichsD11GreenDomainLift
      period hPeriod d9Ellipticity matterMass analysis parameter)
    (programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainLift
      period hPeriod covector matterMass analysis parameter)
  · intro state
    rfl
  · intro state
    rfl
  · intro state
    have hDomain :
        programPT12GaugeFixedLLFriedrichsD11GreenDomainLift
            period hPeriod d9Ellipticity matterMass analysis parameter state =
          programPT12GaugeFixedLLFriedrichsD11GreenDomainElement
            period hPeriod d9Ellipticity matterMass analysis parameter state := by
      apply Subtype.ext
      rfl
    rw [hDomain]
    exact programPT12GaugeFixedLLFriedrichsD11Green_right_identity
      period hPeriod d9Ellipticity matterMass analysis parameter state
  · exact programPT12GaugeFixedLLFriedrichsD11Green_left_identity
      period hPeriod d9Ellipticity matterMass analysis parameter
  · intro state
    have hDomain :
        programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainLift
            period hPeriod covector matterMass analysis parameter state =
          programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement
            period hPeriod covector matterMass analysis parameter state := by
      apply Subtype.ext
      exact
        (programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement_coe
          period hPeriod covector matterMass analysis parameter state).symm
    rw [hDomain]
    exact
      programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement_kernel
        period hPeriod covector matterMass analysis parameter state
  · exact programPT12GaugeFixedLLFriedrichsD11KernelProjection_apply
      period hPeriod covector matterMass analysis
  · intro state
    simpa only [
      programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement_coe]
      using
        (programPT12GaugeFixedLLFriedrichsD11Green_eq_zero_of_kernel
          period hPeriod d9Ellipticity matterMass analysis parameter
          (programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement
            period hPeriod covector matterMass analysis parameter state)
          (programPT12GaugeFixedLLFriedrichsD11KernelProjectionDomainElement_kernel
            period hPeriod covector matterMass analysis parameter state))

theorem programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse_left
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (state : (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector matterMass analysis parameter).domain) :
    programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
        period hPeriod d9Ellipticity matterMass analysis parameter
        ((programPT12GaugeFixedLLFriedrichsD11StabilizedOperator
          period hPeriod covector matterMass analysis parameter).toFun state) =
      state.1 := by
  have hDomain :=
    (programPT12GaugeFixedLLFriedrichsD11Stabilization_twoSidedInverse
      period hPeriod d9Ellipticity matterMass analysis parameter).1 state
  calc
    programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
        period hPeriod d9Ellipticity matterMass analysis parameter
        ((programPT12GaugeFixedLLFriedrichsD11StabilizedOperator
          period hPeriod covector matterMass analysis parameter).toFun state) =
      ((programPT12GaugeFixedLLFriedrichsD11StabilizedInverse
          period hPeriod d9Ellipticity matterMass analysis parameter
          ((programPT12GaugeFixedLLFriedrichsD11StabilizedOperator
            period hPeriod covector matterMass analysis parameter).toFun state) :
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter).domain) :
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis) :=
      (programPT12GaugeFixedLLFriedrichsD11StabilizedInverse_coe
        period hPeriod d9Ellipticity matterMass analysis parameter _).symm
    _ = state.1 := congrArg Subtype.val hDomain

theorem programPT12GaugeFixedLLFriedrichsD11StabilizedOperator_surjective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    Function.Surjective
      (programPT12GaugeFixedLLFriedrichsD11StabilizedOperator
        period hPeriod covector matterMass analysis parameter).toFun :=
  (programPT12GaugeFixedLLFriedrichsD11Stabilization_twoSidedInverse
    period hPeriod d9Ellipticity matterMass analysis parameter).2.surjective

def linearPMap_compactPerturbation_boundedFactor
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    (perturbation kernelProjection inverse : E →L[Real] E) :
    E →L[Real] E :=
  ContinuousLinearMap.id Real E +
    (perturbation - kernelProjection).comp inverse

theorem linearPMap_compactPerturbation_factorization_apply
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    (operator : E →ₗ.[Real] E)
    (perturbation kernelProjection inverse : E →L[Real] E)
    (hInverse : ∀ state : operator.domain,
      inverse
          ((kernelProjection.toLinearMap +ᵥ operator).toFun state) =
        state.1)
    (state : operator.domain) :
    (perturbation.toLinearMap +ᵥ operator).toFun state =
      linearPMap_compactPerturbation_boundedFactor
        perturbation kernelProjection inverse
        ((kernelProjection.toLinearMap +ᵥ operator).toFun state) := by
  have hInverse' := hInverse state
  change inverse (kernelProjection state.1 + operator state) = state.1 at hInverse'
  change perturbation state.1 + operator state =
    (kernelProjection state.1 + operator state) +
      (perturbation - kernelProjection)
        (inverse (kernelProjection state.1 + operator state))
  rw [hInverse']
  change perturbation state.1 + operator state =
    kernelProjection state.1 + operator state +
      (perturbation state.1 - kernelProjection state.1)
  abel

theorem linearPMap_compactPerturbation_range_eq
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    (operator : E →ₗ.[Real] E)
    (perturbation kernelProjection inverse : E →L[Real] E)
    (hInverse : ∀ state : operator.domain,
      inverse
          ((kernelProjection.toLinearMap +ᵥ operator).toFun state) =
        state.1)
    (hStabilizedSurjective : Function.Surjective
      (kernelProjection.toLinearMap +ᵥ operator).toFun) :
    LinearMap.range (perturbation.toLinearMap +ᵥ operator).toFun =
      (linearPMap_compactPerturbation_boundedFactor
        perturbation kernelProjection inverse).range := by
  apply le_antisymm
  · rintro output ⟨state, rfl⟩
    refine ⟨(kernelProjection.toLinearMap +ᵥ operator).toFun state, ?_⟩
    exact
      (linearPMap_compactPerturbation_factorization_apply
        operator perturbation kernelProjection inverse hInverse state).symm
  · rintro output ⟨source, rfl⟩
    obtain ⟨state, hState⟩ := hStabilizedSurjective source
    refine ⟨state, ?_⟩
    rw [linearPMap_compactPerturbation_factorization_apply
      operator perturbation kernelProjection inverse hInverse state, hState]
    rfl

theorem linearPMap_compactPerturbation_closedRange_finiteCokernel
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    (operator : E →ₗ.[Real] E)
    (perturbation kernelProjection inverse : E →L[Real] E)
    (hPerturbationCompact : IsCompactOperator perturbation)
    (hKernelProjectionCompact : IsCompactOperator kernelProjection)
    (hInverse : ∀ state : operator.domain,
      inverse
          ((kernelProjection.toLinearMap +ᵥ operator).toFun state) =
        state.1)
    (hStabilizedSurjective : Function.Surjective
      (kernelProjection.toLinearMap +ᵥ operator).toFun) :
    IsClosed
        (LinearMap.range
          (perturbation.toLinearMap +ᵥ operator).toFun : Set E) ∧
      FiniteDimensional Real
        (E ⧸ LinearMap.range
          (perturbation.toLinearMap +ᵥ operator).toFun) := by
  let compactFactor := (perturbation - kernelProjection).comp inverse
  let boundedFactor := ContinuousLinearMap.id Real E + compactFactor
  have hCompactFactor : IsCompactOperator compactFactor :=
    (hPerturbationCompact.sub hKernelProjectionCompact).comp_clm inverse
  have hFredholm := compact_identity_add_fredholm
    compactFactor hCompactFactor
  have hRange :
      LinearMap.range (perturbation.toLinearMap +ᵥ operator).toFun =
        boundedFactor.range := by
    simpa [compactFactor, boundedFactor,
      linearPMap_compactPerturbation_boundedFactor] using
      (linearPMap_compactPerturbation_range_eq
        operator perturbation kernelProjection inverse hInverse
        hStabilizedSurjective)
  have hBoundedRangeSet :
      (boundedFactor.range : Set E) = Set.range (boundedFactor : E → E) := by
    ext state
    constructor <;> rintro ⟨source, rfl⟩ <;> exact ⟨source, rfl⟩
  have hClosed : IsClosed
      (LinearMap.range
        (perturbation.toLinearMap +ᵥ operator).toFun : Set E) := by
    rw [hRange, hBoundedRangeSet]
    simpa [boundedFactor] using hFredholm.1
  have hOrthogonalFinite : FiniteDimensional Real
      (LinearMap.range
        (perturbation.toLinearMap +ᵥ operator).toFun)ᗮ := by
    rw [hRange]
    simpa [boundedFactor] using hFredholm.2.2
  let physicalRange :=
    LinearMap.range (perturbation.toLinearMap +ᵥ operator).toFun
  letI : CompleteSpace physicalRange := hClosed.completeSpace_coe
  letI : FiniteDimensional Real physicalRangeᗮ := hOrthogonalFinite
  exact ⟨hClosed,
    physicalRange.quotientEquivOrthogonal.symm.toLinearEquiv.finiteDimensional⟩

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

section Physical

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chart : GlobalCandidateALocalVariationalChart period hPeriod
  couplings NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)
variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis chart sameAction)

theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_factorization_apply
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real)
    (state : (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector couplings.matterMassSquared analysis
        parameter).domain) :
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod covector parameter).toFun state =
      linearPMap_compactPerturbation_boundedFactor
        (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              (iota := iota) period hPeriod)
        (programPT12GaugeFixedLLFriedrichsD11KernelProjection
          period hPeriod covector couplings.matterMassSquared analysis)
        (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            parameter)
        ((programPT12GaugeFixedLLFriedrichsD11StabilizedOperator
          period hPeriod covector couplings.matterMassSquared analysis
            parameter).toFun state) := by
  exact linearPMap_compactPerturbation_factorization_apply
    (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector couplings.matterMassSquared analysis parameter)
    (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod)
    (programPT12GaugeFixedLLFriedrichsD11KernelProjection
      period hPeriod covector couplings.matterMassSquared analysis)
    (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter)
    (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse_left
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter)
    state

theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_range_eq
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    LinearMap.range
        (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              period hPeriod covector parameter).toFun =
      (linearPMap_compactPerturbation_boundedFactor
        (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              (iota := iota) period hPeriod)
        (programPT12GaugeFixedLLFriedrichsD11KernelProjection
          period hPeriod covector couplings.matterMassSquared analysis)
        (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            parameter)).range := by
  exact linearPMap_compactPerturbation_range_eq
    (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector couplings.matterMassSquared analysis parameter)
    (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod)
    (programPT12GaugeFixedLLFriedrichsD11KernelProjection
      period hPeriod covector couplings.matterMassSquared analysis)
    (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter)
    (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse_left
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter)
    (programPT12GaugeFixedLLFriedrichsD11StabilizedOperator_surjective
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter)

theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_closedRange_finiteCokernel
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    IsClosed
        (LinearMap.range
          (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
            (configuration := configuration) (data := data)
              (analysis := analysis) (chart := chart)
                (sameAction := sameAction) (physical := physical)
                  period hPeriod covector parameter).toFun :
          Set (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis)) ∧
      FiniteDimensional Real
        (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis ⧸
          LinearMap.range
            (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
              (configuration := configuration) (data := data)
                (analysis := analysis) (chart := chart)
                  (sameAction := sameAction) (physical := physical)
                    period hPeriod covector parameter).toFun) := by
  apply linearPMap_compactPerturbation_closedRange_finiteCokernel
    (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector couplings.matterMassSquared analysis parameter)
    (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod)
    (programPT12GaugeFixedLLFriedrichsD11KernelProjection
      period hPeriod covector couplings.matterMassSquared analysis)
    (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter)
  · exact programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_compact
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod
  · exact programPT12GaugeFixedLLFriedrichsD11KernelProjection_compact
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis
  · exact programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse_left
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
  · exact programPT12GaugeFixedLLFriedrichsD11StabilizedOperator_surjective
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter

theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_fredholm
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    IsClosed
        (LinearMap.range
          (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
            (configuration := configuration) (data := data)
              (analysis := analysis) (chart := chart)
                (sameAction := sameAction) (physical := physical)
                  period hPeriod covector parameter).toFun :
          Set (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis)) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
            (configuration := configuration) (data := data)
              (analysis := analysis) (chart := chart)
                (sameAction := sameAction) (physical := physical)
                  period hPeriod covector parameter).toFun) ∧
      FiniteDimensional Real
        (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis ⧸
          LinearMap.range
            (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
              (configuration := configuration) (data := data)
                (analysis := analysis) (chart := chart)
                  (sameAction := sameAction) (physical := physical)
                    period hPeriod covector parameter).toFun) := by
  have hRange :=
    programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_closedRange_finiteCokernel
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter
  exact ⟨hRange.1,
    P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFiniteKernel4D.programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_kernel_finiteDimensional
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter,
    hRange.2⟩

end Physical

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFredholm4D
end JanusFormal
