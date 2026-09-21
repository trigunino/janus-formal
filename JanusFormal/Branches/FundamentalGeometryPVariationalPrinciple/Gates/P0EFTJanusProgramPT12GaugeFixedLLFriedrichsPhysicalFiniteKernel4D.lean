import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszCompact4D
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Finite kernel of the compactly perturbed physical Friedrichs family

The complement of the fixed D11 range projection is finite rank and compact.
Together with the compact physical Riesz perturbation and the D11 Green
identity, this embeds every physical fibre kernel into a nonzero eigenspace of
a compact operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFiniteKernel4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra
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
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszCompact4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

local instance programPGlobalGaugeFixedSpectralHessianModeDecidableEq
    (iota : Type*) [DecidableEq iota] :
    DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode iota) :=
  Classical.decEq _

variable {Mode : Type*} [DecidableEq Mode]

def complexDiagonalZeroProjectionCLM
    (weight : Mode → Real) :
    ComplexDiagonalHilbert Mode →L[Complex] ComplexDiagonalHilbert Mode :=
  ContinuousLinearMap.id Complex _ -
    complexDiagonalZeroComplementProjectionCLM weight

def complexDiagonalComplementKernelRestriction
    (weight : Mode → Real) :
    (complexDiagonalZeroComplementProjectionCLM weight).ker →ₗ[Complex]
      (ComplexDiagonalZeroMode Mode weight → Complex) where
  toFun state mode := state.1 mode.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem complexDiagonalComplementKernelRestriction_injective
    (weight : Mode → Real) :
    Function.Injective (complexDiagonalComplementKernelRestriction weight) := by
  intro first second hCoordinates
  apply Subtype.ext
  ext mode
  by_cases hZero : weight mode = 0
  · exact congrFun hCoordinates
      (⟨mode, hZero⟩ : ComplexDiagonalZeroMode Mode weight)
  · have hFirstProjection :
        complexDiagonalZeroComplementProjectionCLM weight first.1 = 0 :=
      first.property
    have hSecondProjection :
        complexDiagonalZeroComplementProjectionCLM weight second.1 = 0 :=
      second.property
    have hFirst := congrArg
      (fun state : ComplexDiagonalHilbert Mode => state mode) hFirstProjection
    have hSecond := congrArg
      (fun state : ComplexDiagonalHilbert Mode => state mode) hSecondProjection
    have hFirstZero : first.1 mode = 0 := by
      change (if weight mode = 0 then 0 else first.1 mode) = 0 at hFirst
      rw [if_neg hZero] at hFirst
      exact hFirst
    have hSecondZero : second.1 mode = 0 := by
      change (if weight mode = 0 then 0 else second.1 mode) = 0 at hSecond
      rw [if_neg hZero] at hSecond
      exact hSecond
    rw [hFirstZero, hSecondZero]

theorem complexDiagonalComplementKernel_finiteDimensional
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    FiniteDimensional Complex
      (complexDiagonalZeroComplementProjectionCLM weight).ker := by
  letI : Finite (ComplexDiagonalZeroMode Mode weight) := data.zeroModeFinite
  exact FiniteDimensional.of_injective
    (complexDiagonalComplementKernelRestriction weight)
    (complexDiagonalComplementKernelRestriction_injective weight)

theorem complexDiagonalZeroProjection_mem_complementKernel
    (weight : Mode → Real)
    (state : ComplexDiagonalHilbert Mode) :
    complexDiagonalZeroProjectionCLM weight state ∈
      (complexDiagonalZeroComplementProjectionCLM weight).ker := by
  rw [LinearMap.mem_ker]
  ext mode
  by_cases hZero : weight mode = 0 <;>
    simp [complexDiagonalZeroProjectionCLM,
      complexDiagonalZeroComplementProjectionCLM_apply,
      complexDiagonalZeroComplementImage_apply, hZero]

theorem complexDiagonalZeroProjection_compact
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    IsCompactOperator (complexDiagonalZeroProjectionCLM weight) := by
  letI : FiniteDimensional Complex
      (complexDiagonalZeroComplementProjectionCLM weight).ker :=
    complexDiagonalComplementKernel_finiteDimensional weight data
  let restricted : ComplexDiagonalHilbert Mode →L[Complex]
      (complexDiagonalZeroComplementProjectionCLM weight).ker :=
    (complexDiagonalZeroProjectionCLM weight).codRestrict
      (complexDiagonalZeroComplementProjectionCLM weight).ker
      (complexDiagonalZeroProjection_mem_complementKernel weight)
  have hRestricted : IsCompactOperator restricted :=
    isCompactOperator_of_locallyCompactSpace_dom restricted
  simpa [restricted, Function.comp_def] using
    hRestricted.clm_comp
      (complexDiagonalZeroComplementProjectionCLM weight).ker.subtypeL

theorem withLpTwoProdMap_compact_of_first
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (first : E →L[Real] E) (hFirst : IsCompactOperator first) :
    IsCompactOperator (withLpTwoProdMap first (0 : F →L[Real] F)) := by
  let fstMap : E × F →L[Real] E := ContinuousLinearMap.fst Real E F
  let inlMap : E →L[Real] E × F := ContinuousLinearMap.inl Real E F
  have hFst : IsCompactOperator (fun state : E × F => first state.1) := by
    change IsCompactOperator (fun state : E × F => first (fstMap state))
    exact hFirst.comp_clm fstMap
  have hBlock : IsCompactOperator (fun state : E × F =>
      (first state.1, (0 : F))) := by
    simpa [inlMap, Function.comp_def] using hFst.clm_comp inlMap
  let toProduct :=
    (WithLp.prodContinuousLinearEquiv 2 Real E F).toContinuousLinearMap
  let fromProduct :=
    (WithLp.prodContinuousLinearEquiv 2 Real E F).symm.toContinuousLinearMap
  have hPre : IsCompactOperator (fun state : WithLp 2 (E × F) =>
      (first (WithLp.ofLp state).1, (0 : F))) := by
    change IsCompactOperator (fun state : WithLp 2 (E × F) =>
      (first (toProduct state).1, (0 : F)))
    exact hBlock.comp_clm toProduct
  have hPost : IsCompactOperator (fun state : WithLp 2 (E × F) =>
      WithLp.toLp 2 (first (WithLp.ofLp state).1, (0 : F))) := by
    simpa [fromProduct, Function.comp_def] using hPre.clm_comp fromProduct
  change IsCompactOperator (fun state : WithLp 2 (E × F) =>
    WithLp.toLp 2 (first (WithLp.ofLp state).1, (0 : F)))
  exact hPost

def programPT12GaugeFixedSpectralZeroProjection
    (period : Real) (hPeriod : period ≠ 0)
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real) :
    ProgramPGlobalGaugeFixedSpectralHessianHilbert iota →L[Real]
      ProgramPGlobalGaugeFixedSpectralHessianHilbert iota :=
  (complexDiagonalZeroProjectionCLM
    (programPGlobalGaugeFixedSpectralHessianWeight
      period hPeriod covector matterMass)).restrictScalars Real

theorem programPT12GaugeFixedSpectralZeroProjection_compact
    (period : Real) (hPeriod : period ≠ 0)
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real) :
    IsCompactOperator
      (programPT12GaugeFixedSpectralZeroProjection
        period hPeriod covector matterMass) := by
  exact complexDiagonalZeroProjection_compact
    (programPGlobalGaugeFixedSpectralHessianWeight
      period hPeriod covector matterMass)
    (programPGlobalGaugeFixedSpectralHessianFiniteZeroGap
      period hPeriod d9Ellipticity matterMass)

def programPT12GaugeFixedLLFriedrichsD11KernelProjection
    (period : Real) (hPeriod : period ≠ 0)
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  withLpTwoProdMap
    (programPT12GaugeFixedSpectralZeroProjection
      period hPeriod covector matterMass)
    (0 : CanonicalLLL2 period hPeriod analysis →L[Real]
      CanonicalLLL2 period hPeriod analysis)

theorem programPT12GaugeFixedLLFriedrichsD11KernelProjection_compact
    (period : Real) (hPeriod : period ≠ 0)
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsD11KernelProjection
        period hPeriod covector matterMass analysis) := by
  exact withLpTwoProdMap_compact_of_first _
    (programPT12GaugeFixedSpectralZeroProjection_compact
      period hPeriod d9Ellipticity matterMass)

theorem programPT12GaugeFixedLLFriedrichsD11KernelProjection_apply
    (period : Real) (hPeriod : period ≠ 0)
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
  rw [programPT12GaugeFixedLLFriedrichsD11KernelProjection,
    programPT12GaugeFixedLLFriedrichsD11RangeProjection,
    withLpTwoProdMap_apply, withLpTwoProdMap_apply]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · rfl
  · simp

/-- A compact bounded perturbation has finite-dimensional kernel whenever a
generalized inverse has compact defect projection. -/
theorem linearPMap_compactPerturbation_kernel_finiteDimensional
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    (operator : E →ₗ.[Real] E)
    (perturbation green rangeProjection kernelProjection : E →L[Real] E)
    (hLeft : ∀ state : operator.domain,
      green (operator state) = rangeProjection state.1)
    (hKernelProjection : ∀ state,
      kernelProjection state = state - rangeProjection state)
    (hKernelProjectionCompact : IsCompactOperator kernelProjection)
    (hPerturbationCompact : IsCompactOperator perturbation) :
    FiniteDimensional Real
      (LinearMap.ker (perturbation.toLinearMap +ᵥ operator).toFun) := by
  let control : E →L[Real] E :=
    kernelProjection - green.comp perturbation
  have hControlCompact : IsCompactOperator control := by
    exact hKernelProjectionCompact.sub
      (hPerturbationCompact.clm_comp green)
  let kernelToEigenspace :
      LinearMap.ker (perturbation.toLinearMap +ᵥ operator).toFun →ₗ[Real]
        Module.End.eigenspace control.toLinearMap 1 :=
    { toFun := fun state :
          LinearMap.ker (perturbation.toLinearMap +ᵥ operator).toFun =>
        (⟨state.1.1, by
          rw [Module.End.mem_eigenspace_iff]
          have hSum : perturbation state.1.1 + operator state.1 = 0 :=
            state.property
          have hOperator : operator state.1 = -perturbation state.1.1 :=
            eq_neg_of_add_eq_zero_right hSum
          have hRange : rangeProjection state.1.1 =
              -(green (perturbation state.1.1)) := by
            calc
              rangeProjection state.1.1 = green (operator state.1) :=
                (hLeft state.1).symm
              _ = green (-perturbation state.1.1) := by rw [hOperator]
              _ = -(green (perturbation state.1.1)) := by simp
          change kernelProjection state.1.1 -
              green (perturbation state.1.1) = (1 : Real) • state.1.1
          rw [hKernelProjection, hRange, one_smul]
          abel⟩ : Module.End.eigenspace control.toLinearMap 1)
      map_add' := by
        intro first second
        apply Subtype.ext
        rfl
      map_smul' := by
        intro scalar state
        apply Subtype.ext
        rfl }
  have hInjective : Function.Injective kernelToEigenspace := by
    intro first second hEqual
    apply Subtype.ext
    apply Subtype.ext
    have hAmbient := congrArg Subtype.val hEqual
    change first.1.1 = second.1.1 at hAmbient
    exact hAmbient
  letI : FiniteDimensional Real
      (Module.End.eigenspace control.toLinearMap 1) :=
    ContinuousLinearMap.finite_dimensional_eigenspace
      hControlCompact 1 one_ne_zero
  exact FiniteDimensional.of_injective kernelToEigenspace hInjective

private abbrev EffectiveQuotient (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace
    (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold
    (period : Real) (hPeriod : period ≠ 0) :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace
    (period : Real) (hPeriod : period ≠ 0) :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace
    (period : Real) (hPeriod : period ≠ 0) :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace

/-- Concrete finite-kernel consequence for every compactly perturbed physical
T12 Friedrichs fibre. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_kernel_finiteDimensional
    (period : Real) (hPeriod : period ≠ 0)
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod
      couplings NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
      period hPeriod configuration data analysis chart sameAction)
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (parameter : Real) :
    FiniteDimensional Real
      (LinearMap.ker
        (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              period hPeriod covector parameter).toFun) := by
  apply linearPMap_compactPerturbation_kernel_finiteDimensional
    (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector couplings.matterMassSquared analysis parameter)
    (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod)
    (programPT12GaugeFixedLLFriedrichsD11GreenOperator
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter)
    (programPT12GaugeFixedLLFriedrichsD11RangeProjection
      period hPeriod covector couplings.matterMassSquared analysis)
    (programPT12GaugeFixedLLFriedrichsD11KernelProjection
      period hPeriod covector couplings.matterMassSquared analysis)
  · exact programPT12GaugeFixedLLFriedrichsD11Green_left_identity
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis parameter
  · exact programPT12GaugeFixedLLFriedrichsD11KernelProjection_apply
      period hPeriod covector couplings.matterMassSquared analysis
  · exact programPT12GaugeFixedLLFriedrichsD11KernelProjection_compact
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis
  · exact programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_compact
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFiniteKernel4D
end JanusFormal
