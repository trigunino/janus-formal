import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsConstantDefectFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFriedrichsNormResolventFamily4D

/-!
# Bounded Green family for the spectral--LL Friedrichs realization

The existing diagonal graph pseudoinverse uses a harmless regularized value on
the zero modes.  Precomposition with the bounded zero-mode-complement
projection turns it into the genuine generalized inverse, zero on the kernel.
Its product with the shifted LL resolvent gives a norm-continuous bounded Green
family for the whole common-domain realization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenFamily4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusComplexDiagonalRealFredholm4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusLinearPMapProdIdentityFredholm4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsConstantDefectFamily4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsShiftedResolvent4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLFriedrichsNormResolventFamily4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

variable {Mode : Type*} [DecidableEq Mode]

/-! ## Genuine diagonal Green operator -/

/-- Delete exactly the zero-weight coordinates. -/
def complexDiagonalZeroComplementImage
    (weight : Mode → Real)
    (state : ComplexDiagonalHilbert Mode) :
    ComplexDiagonalHilbert Mode := by
  let projected : Mode → Complex := fun mode =>
    if weight mode = 0 then 0 else state mode
  have hProjected : Memℓp projected 2 :=
    (lp.memℓp state).mono' (fun mode => by
      by_cases hZero : weight mode = 0
      · simp [projected, hZero]
      · simp [projected, hZero])
  exact ⟨projected, hProjected⟩

omit [DecidableEq Mode] in
@[simp]
theorem complexDiagonalZeroComplementImage_apply
    (weight : Mode → Real)
    (state : ComplexDiagonalHilbert Mode)
    (mode : Mode) :
    complexDiagonalZeroComplementImage weight state mode =
      if weight mode = 0 then 0 else state mode :=
  rfl

/-- Complex-linear zero-mode-complement projection. -/
def complexDiagonalZeroComplementProjectionCLM
    (weight : Mode → Real) :
    ComplexDiagonalHilbert Mode →L[Complex]
      ComplexDiagonalHilbert Mode :=
  LinearMap.mkContinuous
    { toFun := complexDiagonalZeroComplementImage weight
      map_add' := by
        intro first second
        ext mode
        by_cases hZero : weight mode = 0 <;>
          simp [complexDiagonalZeroComplementImage_apply, hZero]
      map_smul' := by
        intro scalar state
        ext mode
        by_cases hZero : weight mode = 0 <;>
          simp [complexDiagonalZeroComplementImage_apply, hZero] }
    1 (by
      intro state
      rw [one_mul]
      apply lp.norm_mono (p := (2 : ENNReal)) (by norm_num)
      intro mode
      by_cases hZero : weight mode = 0 <;>
        simp [complexDiagonalZeroComplementImage_apply, hZero])

omit [DecidableEq Mode] in
@[simp]
theorem complexDiagonalZeroComplementProjectionCLM_apply
    (weight : Mode → Real)
    (state : ComplexDiagonalHilbert Mode) :
    complexDiagonalZeroComplementProjectionCLM weight state =
      complexDiagonalZeroComplementImage weight state :=
  rfl

omit [DecidableEq Mode] in
theorem complexDiagonalZeroRestriction_projection
    (weight : Mode → Real)
    (state : ComplexDiagonalHilbert Mode) :
    complexDiagonalZeroRestriction Mode weight
        (complexDiagonalZeroComplementProjectionCLM weight state) = 0 := by
  ext mode
  change complexDiagonalZeroComplementImage weight state mode.1 = 0
  simp [complexDiagonalZeroComplementImage_apply, mode.property]

omit [DecidableEq Mode] in
theorem complexDiagonalZeroComplementProjection_eq_self
    (weight : Mode → Real)
    (state : ComplexDiagonalHilbert Mode)
    (hRestriction : complexDiagonalZeroRestriction Mode weight state = 0) :
    complexDiagonalZeroComplementProjectionCLM weight state = state := by
  ext mode
  by_cases hZero : weight mode = 0
  · have hAt := congrFun hRestriction
      (⟨mode, hZero⟩ : ComplexDiagonalZeroMode Mode weight)
    change state mode = 0 at hAt
    simp [complexDiagonalZeroComplementImage_apply, hZero, hAt]
  · simp [complexDiagonalZeroComplementImage_apply, hZero]

omit [DecidableEq Mode] in
theorem complexDiagonalZeroComplementProjection_eq_zero_of_kernel
    (weight : Mode → Real)
    (state : ComplexDiagonalHilbert Mode)
    (hKernel : ∀ mode, (weight mode : Complex) * state mode = 0) :
    complexDiagonalZeroComplementProjectionCLM weight state = 0 := by
  ext mode
  by_cases hZero : weight mode = 0
  · simp [complexDiagonalZeroComplementImage_apply, hZero]
  · have hWeight : (weight mode : Complex) ≠ 0 := by
      exact_mod_cast hZero
    have hState : state mode = 0 :=
      (mul_eq_zero.mp (hKernel mode)).resolve_left hWeight
    simp [complexDiagonalZeroComplementImage_apply, hZero, hState]

/-- Genuine diagonal Green operator: the existing bounded extension, restricted
to the complement of the finite zero-mode space. -/
def complexDiagonalGraphGreenOperator
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight) :
    ComplexDiagonalHilbert Mode →L[Complex]
      ComplexDiagonalHilbert Mode :=
  (complexDiagonalGraphPseudoinverse Mode weight data).comp
    (complexDiagonalZeroComplementProjectionCLM weight)

/-- Domain-valued Green solution for every ambient source. -/
def complexDiagonalGraphGreenDomainElement
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight)
    (state : ComplexDiagonalHilbert Mode) :
    (complexDiagonalOperator Mode weight).domain := by
  let projected := complexDiagonalZeroComplementProjectionCLM weight state
  let preimage := complexDiagonalGraphPseudoinverse Mode weight data projected
  have hRestriction :
      complexDiagonalZeroRestriction Mode weight projected = 0 :=
    complexDiagonalZeroRestriction_projection weight state
  have hRelation : ∀ mode,
      projected mode = (weight mode : Complex) * preimage mode :=
    fun mode => (complexDiagonal_mul_pseudoinverse_of_zeroRestriction
      Mode weight data projected hRestriction mode).symm
  exact ⟨preimage, ⟨projected, hRelation⟩⟩

@[simp]
theorem complexDiagonalGraphGreenDomainElement_coe
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight)
    (state : ComplexDiagonalHilbert Mode) :
    (complexDiagonalGraphGreenDomainElement weight data state :
        ComplexDiagonalHilbert Mode) =
      complexDiagonalGraphGreenOperator weight data state :=
  rfl

/-- `A G` is the zero-mode-complement projection. -/
theorem complexDiagonalGraphGreenOperator_right_identity
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight)
    (state : ComplexDiagonalHilbert Mode) :
    complexDiagonalOperator Mode weight
        (complexDiagonalGraphGreenDomainElement weight data state) =
      complexDiagonalZeroComplementProjectionCLM weight state := by
  ext mode
  rw [complexDiagonalOperator_apply,
    complexDiagonalGraphGreenDomainElement_coe,
    complexDiagonalGraphGreenOperator,
    ContinuousLinearMap.comp_apply]
  exact complexDiagonal_mul_pseudoinverse_of_zeroRestriction
    Mode weight data
    (complexDiagonalZeroComplementProjectionCLM weight state)
    (complexDiagonalZeroRestriction_projection weight state) mode

/-- `G A` is the same projection on the maximal domain. -/
theorem complexDiagonalGraphGreenOperator_left_identity
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight)
    (state : (complexDiagonalOperator Mode weight).domain) :
    complexDiagonalGraphGreenOperator weight data
        (complexDiagonalOperator Mode weight state) =
      complexDiagonalZeroComplementProjectionCLM weight state.1 := by
  ext mode
  rw [complexDiagonalGraphGreenOperator,
    ContinuousLinearMap.comp_apply,
    complexDiagonalGraphPseudoinverse,
    complexDiagonalInverseCLM_apply,
    complexDiagonalInverseImage_apply,
    complexDiagonalInverseCoefficient]
  rw [complexDiagonalZeroComplementProjectionCLM_apply,
    complexDiagonalZeroComplementProjectionCLM_apply]
  by_cases hZero : weight mode = 0
  · simp [complexDiagonalZeroComplementImage_apply, hZero]
  · rw [complexDiagonalZeroComplementImage_apply, if_neg hZero,
      complexDiagonalOperator_apply,
      complexDiagonalRegularizedWeight, if_neg hZero]
    have hWeight : (weight mode : Complex) ≠ 0 := by
      exact_mod_cast hZero
    field_simp
    simp [complexDiagonalZeroComplementImage_apply, hZero]

theorem complexDiagonalGraphGreenOperator_eq_zero_of_kernel
    (weight : Mode → Real)
    (data : ComplexDiagonalFiniteZeroGap Mode weight)
    (state : (complexDiagonalOperator Mode weight).domain)
    (hKernel : complexDiagonalOperator Mode weight state = 0) :
    complexDiagonalGraphGreenOperator weight data state.1 = 0 := by
  have hPointwise : ∀ mode, (weight mode : Complex) * state.1 mode = 0 := by
    intro mode
    rw [← complexDiagonalOperator_apply Mode weight state mode]
    exact congrArg
      (fun output : ComplexDiagonalHilbert Mode => output mode) hKernel
  rw [complexDiagonalGraphGreenOperator,
    ContinuousLinearMap.comp_apply,
    complexDiagonalZeroComplementProjection_eq_zero_of_kernel
      weight state.1 hPointwise,
    map_zero]

/-! ## Spectral--LL product Green family -/

variable (period : Real) (hPeriod : period ≠ 0)

local instance programPT12GaugeFixedSpectralModeDecidableEq
    (iota : Type*) [DecidableEq iota] :
    DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode iota) :=
  Classical.decEq _

/-- Fixed real spectral Green operator. -/
def programPT12GaugeFixedSpectralGreenOperator
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real) :
    ProgramPGlobalGaugeFixedSpectralHessianHilbert iota →L[Real]
      ProgramPGlobalGaugeFixedSpectralHessianHilbert iota :=
  (complexDiagonalGraphGreenOperator
    (programPGlobalGaugeFixedSpectralHessianWeight
      period hPeriod covector matterMass)
    (programPGlobalGaugeFixedSpectralHessianFiniteZeroGap
      period hPeriod d9Ellipticity matterMass)).restrictScalars Real

/-- Fixed projection onto the complement of the spectral zero modes. -/
def programPT12GaugeFixedSpectralComplementProjection
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (matterMass : Real) :
    ProgramPGlobalGaugeFixedSpectralHessianHilbert iota →L[Real]
      ProgramPGlobalGaugeFixedSpectralHessianHilbert iota :=
  (complexDiagonalZeroComplementProjectionCLM
    (programPGlobalGaugeFixedSpectralHessianWeight
      period hPeriod covector matterMass)).restrictScalars Real

/-- Block-diagonal continuous map on the Hilbert `L²` product. -/
def withLpTwoProdMap
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (first : E →L[Real] E) (second : F →L[Real] F) :
    WithLp 2 (E × F) →L[Real] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 Real E F).symm.toContinuousLinearMap.comp
    ((first.prodMap second).comp
      (WithLp.prodContinuousLinearEquiv 2 Real E F).toContinuousLinearMap)

@[simp]
theorem withLpTwoProdMap_apply
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (first : E →L[Real] E) (second : F →L[Real] F)
    (state : WithLp 2 (E × F)) :
    withLpTwoProdMap first second state =
      WithLp.toLp 2
        (first (WithLp.ofLp state).1, second (WithLp.ofLp state).2) :=
  rfl

/-- Bounded Green operator for one fibre of the full T12 family. -/
def programPT12GaugeFixedLLFriedrichsD11GreenOperator
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
  withLpTwoProdMap
    (programPT12GaugeFixedSpectralGreenOperator
      (period := period) (hPeriod := hPeriod) d9Ellipticity matterMass)
    (programPT12GaugeFixedLLFriedrichsD11LLResolvent
      period hPeriod analysis parameter)

/-- Projection onto the fixed spectral complement, with identity on the LL
factor. -/
def programPT12GaugeFixedLLFriedrichsD11RangeProjection
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
    (programPT12GaugeFixedSpectralComplementProjection
      (period := period) (hPeriod := hPeriod) covector matterMass)
    (ContinuousLinearMap.id Real _)

/-- Domain-valued Green solution for one full fibre. -/
def programPT12GaugeFixedLLFriedrichsD11GreenDomainElement
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (source : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis) :
    (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector matterMass analysis parameter).domain := by
  let spectralSource := (WithLp.ofLp source).1
  let llSource := (WithLp.ofLp source).2
  let spectralDomain := complexDiagonalGraphGreenDomainElement
    (programPGlobalGaugeFixedSpectralHessianWeight
      period hPeriod covector matterMass)
    (programPGlobalGaugeFixedSpectralHessianFiniteZeroGap
      period hPeriod d9Ellipticity matterMass)
    spectralSource
  let llDomain := canonicalLLFriedrichsShiftedWeakDomainElement
    period hPeriod analysis
    (programPT12GaugeFixedLLFriedrichsD11Shift parameter)
    (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative parameter)
    llSource
  refine ⟨WithLp.toLp 2 ((spectralDomain : _), (llDomain : _)), ?_⟩
  change spectralDomain.1 ∈
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).domain ∧
    llDomain.1 ∈
      (programPT12GaugeFixedLLFriedrichsD11LLOperator
        period hPeriod analysis parameter).domain
  exact ⟨spectralDomain.property, llDomain.property⟩

/-- `A(a) G(a)` is the fixed projection onto the family range. -/
theorem programPT12GaugeFixedLLFriedrichsD11Green_right_identity
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (source : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis) :
    programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis parameter
        (programPT12GaugeFixedLLFriedrichsD11GreenDomainElement
          period hPeriod d9Ellipticity matterMass analysis parameter source) =
      programPT12GaugeFixedLLFriedrichsD11RangeProjection
        period hPeriod covector matterMass analysis source := by
  change linearPMapProd _ _
      (programPT12GaugeFixedLLFriedrichsD11GreenDomainElement
        period hPeriod d9Ellipticity matterMass analysis parameter source) =
    withLpTwoProdMap _ _ source
  rw [linearPMapProd_apply, withLpTwoProdMap_apply]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · change complexDiagonalOperator _ _
        (complexDiagonalGraphGreenDomainElement
          (programPGlobalGaugeFixedSpectralHessianWeight
            period hPeriod covector matterMass)
          (programPGlobalGaugeFixedSpectralHessianFiniteZeroGap
            period hPeriod d9Ellipticity matterMass)
          (WithLp.ofLp source).1) =
        complexDiagonalZeroComplementProjectionCLM
          (programPGlobalGaugeFixedSpectralHessianWeight
            period hPeriod covector matterMass)
          (WithLp.ofLp source).1
    exact complexDiagonalGraphGreenOperator_right_identity
      (programPGlobalGaugeFixedSpectralHessianWeight
        period hPeriod covector matterMass)
      (programPGlobalGaugeFixedSpectralHessianFiniteZeroGap
        period hPeriod d9Ellipticity matterMass)
      (WithLp.ofLp source).1
  · simpa [programPT12GaugeFixedLLFriedrichsD11GreenDomainElement] using
      (programPT12GaugeFixedLLFriedrichsD11LLResolvent_right_inverse
        period hPeriod analysis parameter (WithLp.ofLp source).2)

/-- `G(a) A(a)` is the same fixed projection on the common domain. -/
theorem programPT12GaugeFixedLLFriedrichsD11Green_left_identity
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (state : (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector matterMass analysis parameter).domain) :
    programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity matterMass analysis parameter
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter state) =
      programPT12GaugeFixedLLFriedrichsD11RangeProjection
        period hPeriod covector matterMass analysis state.1 := by
  change withLpTwoProdMap _ _ (linearPMapProd _ _ state) =
    withLpTwoProdMap _ _ state.1
  rw [withLpTwoProdMap_apply, linearPMapProd_apply,
    withLpTwoProdMap_apply]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · change complexDiagonalGraphGreenOperator
        (programPGlobalGaugeFixedSpectralHessianWeight
          period hPeriod covector matterMass)
        (programPGlobalGaugeFixedSpectralHessianFiniteZeroGap
          period hPeriod d9Ellipticity matterMass)
        (complexDiagonalOperator _ _
          ⟨(WithLp.ofLp state.1).1, state.2.1⟩) =
        complexDiagonalZeroComplementProjectionCLM
          (programPGlobalGaugeFixedSpectralHessianWeight
            period hPeriod covector matterMass)
          (WithLp.ofLp state.1).1
    exact complexDiagonalGraphGreenOperator_left_identity
      (programPGlobalGaugeFixedSpectralHessianWeight
        period hPeriod covector matterMass)
      (programPGlobalGaugeFixedSpectralHessianFiniteZeroGap
        period hPeriod d9Ellipticity matterMass)
      ⟨(WithLp.ofLp state.1).1, state.2.1⟩
  · exact programPT12GaugeFixedLLFriedrichsD11LLResolvent_left_inverse
      period hPeriod analysis parameter
      ⟨(WithLp.ofLp state.1).2, state.2.2⟩

/-- On the spectral complement, `A(a) G(a)` is the identity. -/
theorem programPT12GaugeFixedLLFriedrichsD11Green_right_inverse_of_zeroRestriction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (source : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis)
    (hRestriction :
      complexDiagonalZeroRestriction
          (ProgramPGlobalGaugeFixedSpectralHessianMode iota)
          (programPGlobalGaugeFixedSpectralHessianWeight
            period hPeriod covector matterMass)
          (WithLp.ofLp source).1 = 0) :
    programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis parameter
        (programPT12GaugeFixedLLFriedrichsD11GreenDomainElement
          period hPeriod d9Ellipticity matterMass analysis parameter source) =
      source := by
  rw [programPT12GaugeFixedLLFriedrichsD11Green_right_identity]
  apply (WithLp.prodContinuousLinearEquiv 2 Real
    (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
    (CanonicalLLL2 period hPeriod analysis)).injective
  apply Prod.ext
  · exact complexDiagonalZeroComplementProjection_eq_self
      (programPGlobalGaugeFixedSpectralHessianWeight
        period hPeriod covector matterMass)
      (WithLp.ofLp source).1 hRestriction
  · rfl

/-- On the spectral complement of the common domain, `G(a) A(a)` is the
identity. -/
theorem programPT12GaugeFixedLLFriedrichsD11Green_left_inverse_of_zeroRestriction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (state : (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector matterMass analysis parameter).domain)
    (hRestriction :
      complexDiagonalZeroRestriction
          (ProgramPGlobalGaugeFixedSpectralHessianMode iota)
          (programPGlobalGaugeFixedSpectralHessianWeight
            period hPeriod covector matterMass)
          (WithLp.ofLp state.1).1 = 0) :
    programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity matterMass analysis parameter
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter state) =
      state.1 := by
  rw [programPT12GaugeFixedLLFriedrichsD11Green_left_identity]
  apply (WithLp.prodContinuousLinearEquiv 2 Real
    (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
    (CanonicalLLL2 period hPeriod analysis)).injective
  apply Prod.ext
  · exact complexDiagonalZeroComplementProjection_eq_self
      (programPGlobalGaugeFixedSpectralHessianWeight
        period hPeriod covector matterMass)
      (WithLp.ofLp state.1).1 hRestriction
  · rfl

/-- The genuine Green operator annihilates every fibre kernel. -/
theorem programPT12GaugeFixedLLFriedrichsD11Green_eq_zero_of_kernel
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real)
    (state : (programPT12GaugeFixedLLFriedrichsD11Operator
      period hPeriod covector matterMass analysis parameter).domain)
    (hKernel :
      programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis parameter state = 0) :
    programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity matterMass analysis parameter state.1 = 0 := by
  let spectralState :
      (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
        period hPeriod covector matterMass).domain :=
    ⟨(WithLp.ofLp state.1).1, state.2.1⟩
  let spectralComplexState :
      (complexDiagonalOperator
        (ProgramPGlobalGaugeFixedSpectralHessianMode iota)
        (programPGlobalGaugeFixedSpectralHessianWeight
          period hPeriod covector matterMass)).domain :=
    ⟨spectralState.1, spectralState.property⟩
  let llState :
      (programPT12GaugeFixedLLFriedrichsD11LLOperator
        period hPeriod analysis parameter).domain :=
    ⟨(WithLp.ofLp state.1).2, state.2.2⟩
  change linearPMapProd _ _ state = 0 at hKernel
  rw [linearPMapProd_apply] at hKernel
  have hSpectralRaw := congrArg
    (fun output : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis => (WithLp.ofLp output).1) hKernel
  have hSpectralComplex :
      complexDiagonalOperator
          (ProgramPGlobalGaugeFixedSpectralHessianMode iota)
          (programPGlobalGaugeFixedSpectralHessianWeight
            period hPeriod covector matterMass) spectralComplexState = 0 := by
    ext mode
    have hAt := congrArg
      (fun output : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota =>
        output mode) hSpectralRaw
    simp only [WithLp.ofLp_zero] at hAt
    change complexDiagonalRealOperator
        (ProgramPGlobalGaugeFixedSpectralHessianMode iota)
        (programPGlobalGaugeFixedSpectralHessianWeight
          period hPeriod covector matterMass)
        ⟨(WithLp.ofLp state.1).1, state.2.1⟩ mode = 0 at hAt
    rw [complexDiagonalRealOperator_apply] at hAt
    rw [complexDiagonalOperator_apply]
    simpa [spectralState, spectralComplexState] using hAt
  have hLLImage :
      programPT12GaugeFixedLLFriedrichsD11LLOperator
        period hPeriod analysis parameter llState = 0 :=
    by
      have hLLRaw := congrArg
        (fun output : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
            period hPeriod iota analysis => (WithLp.ofLp output).2) hKernel
      simpa [llState] using hLLRaw
  have hLLInjective : Function.Injective
      (programPT12GaugeFixedLLFriedrichsD11LLOperator
        period hPeriod analysis parameter).toFun :=
    LinearMap.ker_eq_bot.mp
      (programPT12GaugeFixedLLFriedrichsD11LLOperator_ker_eq_bot
        period hPeriod analysis parameter)
  have hLLState : llState = 0 := by
    apply hLLInjective
    simpa using hLLImage
  apply (WithLp.prodContinuousLinearEquiv 2 Real
    (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
    (CanonicalLLL2 period hPeriod analysis)).injective
  apply Prod.ext
  · exact complexDiagonalGraphGreenOperator_eq_zero_of_kernel
      (programPGlobalGaugeFixedSpectralHessianWeight
        period hPeriod covector matterMass)
      (programPGlobalGaugeFixedSpectralHessianFiniteZeroGap
        period hPeriod d9Ellipticity matterMass)
      spectralComplexState hSpectralComplex
  · have hLLValue : (llState : CanonicalLLL2 period hPeriod analysis) = 0 :=
      congrArg Subtype.val hLLState
    change programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter (WithLp.ofLp state.1).2 = 0
    rw [show (WithLp.ofLp state.1).2 = 0 by exact hLLValue, map_zero]

/-- The Green family is continuous in operator norm. -/
theorem programPT12GaugeFixedLLFriedrichsD11Green_continuous
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Continuous (fun parameter =>
      programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity matterMass analysis parameter) := by
  have hLL := programPT12GaugeFixedLLFriedrichsD11LLResolvent_continuous
    period hPeriod analysis
  have hProduct : Continuous (fun parameter =>
      (programPT12GaugeFixedSpectralGreenOperator
        (period := period) (hPeriod := hPeriod)
        d9Ellipticity matterMass).prodMap
          (programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis parameter)) :=
    continuous_const.prod_mapL Real hLL
  have hInner : Continuous (fun parameter =>
      ((programPT12GaugeFixedSpectralGreenOperator
        (period := period) (hPeriod := hPeriod)
        d9Ellipticity matterMass).prodMap
          (programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis parameter)).comp
        (WithLp.prodContinuousLinearEquiv 2 Real
          (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
          (CanonicalLLL2 period hPeriod analysis)).toContinuousLinearMap) :=
    hProduct.clm_comp continuous_const
  have hOuter : Continuous (fun parameter =>
      (WithLp.prodContinuousLinearEquiv 2 Real
        (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
        (CanonicalLLL2 period hPeriod analysis)).symm.toContinuousLinearMap.comp
          (((programPT12GaugeFixedSpectralGreenOperator
            (period := period) (hPeriod := hPeriod)
            d9Ellipticity matterMass).prodMap
              (programPT12GaugeFixedLLFriedrichsD11LLResolvent
                period hPeriod analysis parameter)).comp
            (WithLp.prodContinuousLinearEquiv 2 Real
              (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
              (CanonicalLLL2 period hPeriod analysis)).toContinuousLinearMap)) :=
    continuous_const.clm_comp hInner
  exact hOuter

/-- Auditable Green-family package: two-sided generalized inverse identities,
operator-norm continuity and the already proved constant Fredholm defect. -/
structure ProgramPT12GaugeFixedLLFriedrichsD11GreenFamilyCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) : Prop where
  rightIdentity : ∀ parameter source,
    programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis parameter
        (programPT12GaugeFixedLLFriedrichsD11GreenDomainElement
          period hPeriod d9Ellipticity matterMass analysis parameter source) =
      programPT12GaugeFixedLLFriedrichsD11RangeProjection
        period hPeriod covector matterMass analysis source
  leftIdentity : ∀ parameter state,
    programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity matterMass analysis parameter
        (programPT12GaugeFixedLLFriedrichsD11Operator
          period hPeriod covector matterMass analysis parameter state) =
      programPT12GaugeFixedLLFriedrichsD11RangeProjection
        period hPeriod covector matterMass analysis state.1
  annihilatesKernel : ∀ parameter state,
    programPT12GaugeFixedLLFriedrichsD11Operator
        period hPeriod covector matterMass analysis parameter state = 0 →
      programPT12GaugeFixedLLFriedrichsD11GreenOperator
        period hPeriod d9Ellipticity matterMass analysis parameter state.1 = 0
  operatorNormContinuous : Continuous (fun parameter =>
    programPT12GaugeFixedLLFriedrichsD11GreenOperator
      period hPeriod d9Ellipticity matterMass analysis parameter)
  constantDefect :
    ProgramPT12GaugeFixedLLFriedrichsD11ConstantDefectCertificate4D
      period hPeriod d9Ellipticity matterMass analysis

theorem programPT12GaugeFixedLLFriedrichsD11GreenFamily_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (matterMass : Real)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPT12GaugeFixedLLFriedrichsD11GreenFamilyCertificate4D
      period hPeriod d9Ellipticity matterMass analysis where
  rightIdentity :=
    programPT12GaugeFixedLLFriedrichsD11Green_right_identity
      period hPeriod d9Ellipticity matterMass analysis
  leftIdentity :=
    programPT12GaugeFixedLLFriedrichsD11Green_left_identity
      period hPeriod d9Ellipticity matterMass analysis
  annihilatesKernel :=
    programPT12GaugeFixedLLFriedrichsD11Green_eq_zero_of_kernel
      period hPeriod d9Ellipticity matterMass analysis
  operatorNormContinuous :=
    programPT12GaugeFixedLLFriedrichsD11Green_continuous
      period hPeriod d9Ellipticity matterMass analysis
  constantDefect :=
    programPT12GaugeFixedLLFriedrichsD11ConstantDefectFamily_gate
      period hPeriod d9Ellipticity matterMass analysis

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenFamily4D
end JanusFormal
