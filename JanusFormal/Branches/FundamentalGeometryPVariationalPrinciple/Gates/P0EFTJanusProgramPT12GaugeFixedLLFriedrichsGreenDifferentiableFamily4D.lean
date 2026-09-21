import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenFamily4D

/-!
# Norm-differentiable spectral--LL Green family

The first resolvent identity upgrades the norm-continuous LL resolvent family
to an operator-norm differentiable family.  For the squared D11 parameter its
derivative is `-2a R(a)^2`.  The fixed spectral block then transports this
derivative to the full Green family.  Both derivative operators are compact.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenDifferentiableFamily4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Filter Set
open scoped ENNReal lp Topology
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusLinearPMapProdIdentityFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenFamily4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLFriedrichsNormResolventFamily4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

local instance programPT12GaugeFixedDifferentiableSpectralModeDecidableEq
    (iota : Type*) [DecidableEq iota] :
    DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode iota) :=
  Classical.decEq _

/-! ## LL derivative -/

/-- The operator-norm derivative predicted by the first resolvent identity. -/
def programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    CanonicalLLL2 period hPeriod analysis →L[Real]
      CanonicalLLL2 period hPeriod analysis :=
  (-2 * parameter) •
    ((programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter).comp
      (programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter))

@[simp]
theorem programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative_formula
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative
        period hPeriod analysis parameter =
      (-2 * parameter) •
        ((programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis parameter).comp
          (programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis parameter)) :=
  rfl

/-- Exact punctured slope formula for the squared-parameter resolvent. -/
theorem programPT12GaugeFixedLLFriedrichsD11LLResolvent_slope
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter other : Real) (hOther : other ≠ parameter) :
    slope
        (fun value => programPT12GaugeFixedLLFriedrichsD11LLResolvent
          period hPeriod analysis value)
        parameter other =
      (-(parameter + other)) •
        ((programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis other).comp
          (programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis parameter)) := by
  rw [slope_def_module,
    programPT12GaugeFixedLLFriedrichsD11LLResolvent_identity
      period hPeriod analysis other parameter,
    smul_smul]
  apply congrArg (fun scalar : Real => scalar •
    ((programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis other).comp
      (programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter)))
  simp only [programPT12GaugeFixedLLFriedrichsD11Shift]
  field_simp [sub_ne_zero.mpr hOther]
  ring

/-- The LL resolvent is differentiable in operator norm, with derivative
`-2a R(a)^2`. -/
theorem programPT12GaugeFixedLLFriedrichsD11LLResolvent_hasDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    HasDerivAt
      (fun value => programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis value)
      (programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative
        period hPeriod analysis parameter)
      parameter := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hResolvent :=
    programPT12GaugeFixedLLFriedrichsD11LLResolvent_continuous
      period hPeriod analysis
  have hScalar : ContinuousAt
      (fun other : Real => -(parameter + other)) parameter := by
    fun_prop
  have hComposition : ContinuousAt
      (fun other =>
        (programPT12GaugeFixedLLFriedrichsD11LLResolvent
          period hPeriod analysis other).comp
        (programPT12GaugeFixedLLFriedrichsD11LLResolvent
          period hPeriod analysis parameter)) parameter :=
    hResolvent.continuousAt.clm_comp continuousAt_const
  have hAux : ContinuousAt
      (fun other => (-(parameter + other)) •
        ((programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis other).comp
          (programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis parameter))) parameter :=
    hScalar.smul hComposition
  have hLimit : Tendsto
      (fun other => (-(parameter + other)) •
        ((programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis other).comp
          (programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis parameter)))
      (𝓝[≠] parameter)
      (𝓝 (programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative
        period hPeriod analysis parameter)) := by
    simpa [programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative,
      show -(parameter + parameter) = -2 * parameter by ring] using
      hAux.tendsto.mono_left nhdsWithin_le_nhds
  refine hLimit.congr' ?_
  have hNe : ∀ᶠ other : Real in 𝓝[≠] parameter,
      other ≠ parameter := by
    filter_upwards [self_mem_nhdsWithin] with other hOther
    simpa only [mem_compl_iff, mem_singleton_iff] using hOther
  filter_upwards [hNe] with other hOther
  exact (programPT12GaugeFixedLLFriedrichsD11LLResolvent_slope
    period hPeriod analysis parameter other hOther).symm

theorem programPT12GaugeFixedLLFriedrichsD11LLResolvent_differentiable
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Differentiable Real (fun parameter =>
      programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter) :=
  fun parameter =>
    (programPT12GaugeFixedLLFriedrichsD11LLResolvent_hasDerivAt
      period hPeriod analysis parameter).differentiableAt

/-- The derivative of the compact LL resolvent remains compact. -/
theorem programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative_compact
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative
        period hPeriod analysis parameter) := by
  have hResolvent :=
    programPT12GaugeFixedLLFriedrichsD11LLResolvent_compact
      period hPeriod analysis parameter
  have hSquare : IsCompactOperator (fun state =>
      programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter
        (programPT12GaugeFixedLLFriedrichsD11LLResolvent
          period hPeriod analysis parameter state)) :=
    hResolvent.comp_clm
      (programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter)
  change IsCompactOperator (fun state =>
    (-2 * parameter) •
      programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter
        (programPT12GaugeFixedLLFriedrichsD11LLResolvent
          period hPeriod analysis parameter state))
  exact hSquare.smul (-2 * parameter)

/-! ## Product transport -/

/-- A block map with zero first block and compact second block is compact on
the `WithLp` product. -/
theorem withLpTwoProdMap_compact_of_second
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (second : F →L[Real] F) (hSecond : IsCompactOperator second) :
    IsCompactOperator
      (withLpTwoProdMap (0 : E →L[Real] E) second) := by
  let sndMap : E × F →L[Real] F :=
    ContinuousLinearMap.snd Real E F
  let inrMap : F →L[Real] E × F :=
    ContinuousLinearMap.inr Real E F
  have hSnd : IsCompactOperator (fun state : E × F =>
      second state.2) := by
    change IsCompactOperator (fun state : E × F => second (sndMap state))
    exact hSecond.comp_clm sndMap
  have hBlock : IsCompactOperator (fun state : E × F =>
      ((0 : E), second state.2)) := by
    simpa [inrMap, Function.comp_def] using hSnd.clm_comp inrMap
  let toProduct :=
    (WithLp.prodContinuousLinearEquiv 2 Real E F).toContinuousLinearMap
  let fromProduct :=
    (WithLp.prodContinuousLinearEquiv 2 Real E F).symm.toContinuousLinearMap
  have hPre : IsCompactOperator (fun state : WithLp 2 (E × F) =>
      ((0 : E), second (WithLp.ofLp state).2)) := by
    change IsCompactOperator (fun state : WithLp 2 (E × F) =>
      ((0 : E), second (toProduct state).2))
    exact hBlock.comp_clm toProduct
  have hPost : IsCompactOperator (fun state : WithLp 2 (E × F) =>
      WithLp.toLp 2 ((0 : E), second (WithLp.ofLp state).2)) := by
    simpa [fromProduct, Function.comp_def] using hPre.clm_comp fromProduct
  change IsCompactOperator (fun state : WithLp 2 (E × F) =>
    WithLp.toLp 2 ((0 : E), second (WithLp.ofLp state).2))
  exact hPost

/-! ## Bounded variation of the common-domain family -/

/-- The bounded variation of the common-domain operator family: zero on the
fixed spectral block and `2a` times the identity on the LL block. -/
def programPT12GaugeFixedLLFriedrichsD11VariationOperator
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  withLpTwoProdMap
    (0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota →L[Real]
      ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
    ((2 * parameter) •
      ContinuousLinearMap.id Real
        (CanonicalLLL2 period hPeriod analysis))

@[simp]
theorem programPT12GaugeFixedLLFriedrichsD11VariationOperator_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (state : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis) :
    programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter state =
      WithLp.toLp 2
        ((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota),
          (2 * parameter) • (WithLp.ofLp state).2) := by
  simp [programPT12GaugeFixedLLFriedrichsD11VariationOperator,
    withLpTwoProdMap_apply]

/-- Pointwise derivative of the unbounded family on its common graph domain. -/
theorem programPT12GaugeFixedLLFriedrichsD11Operator_apply_hasDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (state : ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain
      period hPeriod covector matterMass analysis) :
    HasDerivAt
      (fun value => programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis value state)
      (programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter state.1)
      parameter := by
  let spectralState :
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).domain :=
    ⟨(WithLp.ofLp state.1).1, state.2.1⟩
  let llState :
      (canonicalLLFriedrichsJacobi period hPeriod analysis).domain :=
    ⟨(WithLp.ofLp state.1).2, state.2.2⟩
  let spectralValue :=
    programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
      period hPeriod covector matterMass spectralState
  let llBaseValue :=
    canonicalLLFriedrichsJacobi period hPeriod analysis llState
  let llValue : CanonicalLLL2 period hPeriod analysis := llState.1
  let fromProduct :=
    (WithLp.prodContinuousLinearEquiv 2 Real
      (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
      (CanonicalLLL2 period hPeriod analysis)).symm.toContinuousLinearMap
  have hSquare : HasDerivAt (fun value : Real => value ^ 2)
      (2 * parameter) parameter := by
    simpa using hasDerivAt_pow 2 parameter
  have hLL :=
    (hasDerivAt_const parameter llBaseValue).add
      (hSquare.smul_const llValue)
  have hPair :=
    (hasDerivAt_const parameter spectralValue).prodMk hLL
  have hExplicit :=
    fromProduct.hasFDerivAt.comp_hasDerivAt parameter hPair
  have hExplicit' : HasDerivAt
      (fun value => fromProduct
        (spectralValue, llBaseValue + value ^ 2 • llValue))
      (fromProduct
        ((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota),
          (2 * parameter) • llValue)) parameter := by
    simpa [Function.comp_def] using
      hExplicit
  have hOperatorValue : ∀ value,
      programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis value state =
        fromProduct
          (spectralValue, llBaseValue + value ^ 2 • llValue) := by
    intro value
    rfl
  have hMain := hExplicit'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall hOperatorValue)
  apply hMain.congr_deriv
  rfl

/-- Derivative of the full Green family: zero on the fixed spectral block and
the LL resolvent derivative on the moving block. -/
def programPT12GaugeFixedLLFriedrichsD11GreenDerivative
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis :=
  withLpTwoProdMap
    (0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota →L[Real]
      ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
    (programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative
      period hPeriod analysis parameter)

/-- The full bounded Green family is differentiable in operator norm. -/
theorem programPT12GaugeFixedLLFriedrichsD11Green_hasDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    HasDerivAt
      (fun value => programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity matterMass analysis value)
      (programPT12GaugeFixedLLFriedrichsD11GreenDerivative
        period hPeriod analysis parameter)
      parameter := by
  let spectralGreen := programPT12GaugeFixedSpectralGreenOperator
    (period := period) (hPeriod := hPeriod) d9Ellipticity matterMass
  let llResolvent := fun value =>
    programPT12GaugeFixedLLFriedrichsD11LLResolvent
      period hPeriod analysis value
  let llDerivative :=
    programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative
      period hPeriod analysis parameter
  let toProduct :=
    (WithLp.prodContinuousLinearEquiv 2 Real
      (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
      (CanonicalLLL2 period hPeriod analysis)).toContinuousLinearMap
  let fromProduct :=
    (WithLp.prodContinuousLinearEquiv 2 Real
      (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
      (CanonicalLLL2 period hPeriod analysis)).symm.toContinuousLinearMap
  change HasDerivAt
    (fun value => fromProduct.comp
      ((spectralGreen.prodMap (llResolvent value)).comp toProduct))
    (fromProduct.comp
      (((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota →L[Real]
          ProgramPGlobalGaugeFixedSpectralHessianHilbert iota).prodMap
        llDerivative).comp toProduct)) parameter
  have hLL : HasDerivAt llResolvent llDerivative parameter := by
    simpa [llResolvent, llDerivative] using
      (programPT12GaugeFixedLLFriedrichsD11LLResolvent_hasDerivAt
        period hPeriod analysis parameter)
  have hPair : HasDerivAt
      (fun value => (spectralGreen, llResolvent value))
      ((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota →L[Real]
          ProgramPGlobalGaugeFixedSpectralHessianHilbert iota), llDerivative)
      parameter :=
    (hasDerivAt_const parameter spectralGreen).prodMk hLL
  have hProduct : HasDerivAt
      (fun value => spectralGreen.prodMap (llResolvent value))
      ((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota →L[Real]
          ProgramPGlobalGaugeFixedSpectralHessianHilbert iota).prodMap
        llDerivative) parameter := by
    simpa [Function.comp_def] using
      (ContinuousLinearMap.prodMapL Real
        (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
        (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
        (CanonicalLLL2 period hPeriod analysis)
        (CanonicalLLL2 period hPeriod analysis)).hasFDerivAt.comp_hasDerivAt
          parameter hPair
  have hInner : HasDerivAt
      (fun value =>
        (spectralGreen.prodMap (llResolvent value)).comp toProduct)
      (((0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota →L[Real]
          ProgramPGlobalGaugeFixedSpectralHessianHilbert iota).prodMap
        llDerivative).comp toProduct) parameter := by
    simpa using
      hProduct.clm_comp (hasDerivAt_const parameter toProduct)
  simpa using
    (hasDerivAt_const parameter fromProduct).clm_comp hInner

/-- The Bismut--Freed logarithmic derivative candidate `G(a) A'(a)`. -/
def programPT12GaugeFixedLLFriedrichsD11GreenLogarithmicDerivative
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
  (programPT12GaugeFixedLLFriedrichsD11GreenOperator
    period hPeriod d9Ellipticity matterMass analysis parameter).comp
      (programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter)

/-- Resolvent differential identity `G'(a) = -G(a) A'(a) G(a)`. -/
theorem programPT12GaugeFixedLLFriedrichsD11GreenDerivative_eq_neg_comp
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    programPT12GaugeFixedLLFriedrichsD11GreenDerivative
        (iota := iota) period hPeriod analysis parameter =
      -((programPT12GaugeFixedLLFriedrichsD11GreenOperator
          period hPeriod d9Ellipticity matterMass analysis parameter).comp
        ((programPT12GaugeFixedLLFriedrichsD11VariationOperator
            (iota := iota) period hPeriod analysis parameter).comp
          (programPT12GaugeFixedLLFriedrichsD11GreenOperator
            period hPeriod d9Ellipticity matterMass analysis parameter))) := by
  apply ContinuousLinearMap.ext
  intro state
  apply (WithLp.prodContinuousLinearEquiv 2 Real
    (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
    (CanonicalLLL2 period hPeriod analysis)).injective
  apply Prod.ext <;>
    simp [programPT12GaugeFixedLLFriedrichsD11GreenDerivative,
      programPT12GaugeFixedLLFriedrichsD11GreenOperator,
      programPT12GaugeFixedLLFriedrichsD11VariationOperator,
      withLpTwoProdMap_apply, ContinuousLinearMap.comp_apply]

/-- `G(a) A'(a)` has only the compact LL block `2a R(a)`. -/
theorem programPT12GaugeFixedLLFriedrichsD11GreenLogarithmicDerivative_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    programPT12GaugeFixedLLFriedrichsD11GreenLogarithmicDerivative
        period hPeriod d9Ellipticity matterMass analysis parameter =
      withLpTwoProdMap
        (0 : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota →L[Real]
          ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
        ((2 * parameter) •
          programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis parameter) := by
  apply ContinuousLinearMap.ext
  intro state
  apply (WithLp.prodContinuousLinearEquiv 2 Real
    (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
    (CanonicalLLL2 period hPeriod analysis)).injective
  apply Prod.ext <;>
    simp [programPT12GaugeFixedLLFriedrichsD11GreenLogarithmicDerivative,
      programPT12GaugeFixedLLFriedrichsD11GreenOperator,
      programPT12GaugeFixedLLFriedrichsD11VariationOperator,
      withLpTwoProdMap_apply, ContinuousLinearMap.comp_apply]

/-- Compactness of the logarithmic derivative candidate `G(a) A'(a)`. -/
theorem programPT12GaugeFixedLLFriedrichsD11GreenLogarithmicDerivative_compact
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsD11GreenLogarithmicDerivative
        period hPeriod d9Ellipticity matterMass analysis parameter) := by
  rw [programPT12GaugeFixedLLFriedrichsD11GreenLogarithmicDerivative_eq]
  apply withLpTwoProdMap_compact_of_second
  have hResolvent :=
    programPT12GaugeFixedLLFriedrichsD11LLResolvent_compact
      period hPeriod analysis parameter
  change IsCompactOperator (fun state =>
    (2 * parameter) •
      programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter state)
  exact hResolvent.smul (2 * parameter)

theorem programPT12GaugeFixedLLFriedrichsD11Green_differentiable
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Differentiable Real (fun parameter =>
      programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity matterMass analysis parameter) :=
  fun parameter =>
    (programPT12GaugeFixedLLFriedrichsD11Green_hasDerivAt
      period hPeriod d9Ellipticity matterMass analysis parameter).differentiableAt

/-- The derivative of the full Green family is compact. -/
theorem programPT12GaugeFixedLLFriedrichsD11GreenDerivative_compact
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsD11GreenDerivative
        (iota := iota) period hPeriod analysis parameter) :=
  withLpTwoProdMap_compact_of_second
    (programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative
      period hPeriod analysis parameter)
    (programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative_compact
      period hPeriod analysis parameter)

/-- Auditable differentiable Green-family package. -/
structure ProgramPT12GaugeFixedLLFriedrichsD11GreenDifferentiableFamilyCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) : Prop where
  llHasDerivative : ∀ parameter,
    HasDerivAt
      (fun value => programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis value)
      (programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative
        period hPeriod analysis parameter) parameter
  llDerivativeCompact : ∀ parameter,
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative
        period hPeriod analysis parameter)
  operatorHasDerivative : ∀ parameter
      (state : ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain
        period hPeriod covector matterMass analysis),
    HasDerivAt
      (fun value => programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis value state)
      (programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter state.1)
      parameter
  greenHasDerivative : ∀ parameter,
    HasDerivAt
      (fun value => programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity matterMass analysis value)
      (programPT12GaugeFixedLLFriedrichsD11GreenDerivative
        period hPeriod analysis parameter) parameter
  greenDerivativeCompact : ∀ parameter,
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsD11GreenDerivative
        (iota := iota) period hPeriod analysis parameter)
  greenDerivativeIdentity : ∀ parameter,
    programPT12GaugeFixedLLFriedrichsD11GreenDerivative
        (iota := iota) period hPeriod analysis parameter =
      -((programPT12GaugeFixedLLFriedrichsD11GreenOperator
          period hPeriod d9Ellipticity matterMass analysis parameter).comp
        ((programPT12GaugeFixedLLFriedrichsD11VariationOperator
            (iota := iota) period hPeriod analysis parameter).comp
          (programPT12GaugeFixedLLFriedrichsD11GreenOperator
            period hPeriod d9Ellipticity matterMass analysis parameter)))
  logarithmicDerivativeCompact : ∀ parameter,
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsD11GreenLogarithmicDerivative
        period hPeriod d9Ellipticity matterMass analysis parameter)

theorem programPT12GaugeFixedLLFriedrichsD11GreenDifferentiableFamily_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPT12GaugeFixedLLFriedrichsD11GreenDifferentiableFamilyCertificate4D
      period hPeriod d9Ellipticity matterMass analysis where
  llHasDerivative :=
    programPT12GaugeFixedLLFriedrichsD11LLResolvent_hasDerivAt
      period hPeriod analysis
  llDerivativeCompact :=
    programPT12GaugeFixedLLFriedrichsD11LLResolventDerivative_compact
      period hPeriod analysis
  operatorHasDerivative :=
    programPT12GaugeFixedLLFriedrichsD11Operator_apply_hasDerivAt
      period hPeriod matterMass analysis
  greenHasDerivative :=
    programPT12GaugeFixedLLFriedrichsD11Green_hasDerivAt
      period hPeriod d9Ellipticity matterMass analysis
  greenDerivativeCompact :=
    programPT12GaugeFixedLLFriedrichsD11GreenDerivative_compact
      period hPeriod analysis
  greenDerivativeIdentity :=
    programPT12GaugeFixedLLFriedrichsD11GreenDerivative_eq_neg_comp
      period hPeriod d9Ellipticity matterMass analysis
  logarithmicDerivativeCompact :=
    programPT12GaugeFixedLLFriedrichsD11GreenLogarithmicDerivative_compact
      period hPeriod d9Ellipticity matterMass analysis

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenDifferentiableFamily4D
end JanusFormal
