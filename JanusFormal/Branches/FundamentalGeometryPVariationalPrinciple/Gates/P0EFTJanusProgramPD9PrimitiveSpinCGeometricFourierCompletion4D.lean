import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Module.Completion
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierBridge4D

/-!
# Completion of geometric primitive SpinC Fourier analysis

Once the missing all-level geometric Fourier realization is supplied, its
dense analysis range has a canonical Hilbert completion.  This file proves,
without an additional hypothesis, that this completion is unitarily
equivalent to the complete coefficient `L²` space.  It also transports the
maximal squared-Dirac domain and operator and proves exact agreement on the
smooth geometric core.

Thus completion is not an independent Dirac frontier: only construction of
the all-level smooth geometric eigenspinors remains.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierCompletion4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierBridge4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev GeometricFourierRealization :=
  ProgramPD9PrimitiveSpinCGeometricFourierRealization4D period hPeriod

/-- The actual range of smooth geometric Fourier analysis. -/
abbrev PrimitiveSpinCGeometricFourierRange
    (realization : GeometricFourierRealization period hPeriod) :=
  LinearMap.range realization.analysis

/-- Intrinsic Hilbert completion of the smooth geometric Fourier range. -/
abbrev PrimitiveSpinCGeometricFourierCompletion
    (realization : GeometricFourierRealization period hPeriod) :=
  UniformSpace.Completion
    (PrimitiveSpinCGeometricFourierRange period hPeriod realization)

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierCompletion4D

namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierBridge4D

set_option autoImplicit false

open Set
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

noncomputable section

variable (period : Real) (hPeriod : period ≠ 0)

namespace ProgramPD9PrimitiveSpinCGeometricFourierRealization4D

variable
  (realization : GeometricFourierRealization period hPeriod)

/-- Inclusion of the geometric analysis range into its completion. -/
def completionInclusion :
    PrimitiveSpinCGeometricFourierRange
        period hPeriod realization →ₗ[Real]
      PrimitiveSpinCGeometricFourierCompletion
        period hPeriod realization :=
  (UniformSpace.Completion.toComplₗᵢ
    (𝕜 := Real)
    (E := PrimitiveSpinCGeometricFourierRange
      period hPeriod realization)).toLinearMap

/-- Inclusion of the geometric analysis range into coefficient `L²`. -/
def coefficientInclusion :
    PrimitiveSpinCGeometricFourierRange
        period hPeriod realization →ₗ[Real]
      PrimitiveSpinCGeometricL2 :=
  (PrimitiveSpinCGeometricFourierRange
    period hPeriod realization).subtypeₗᵢ.toLinearMap

private theorem completionInclusion_denseRange :
    DenseRange
      (completionInclusion period hPeriod realization) :=
  UniformSpace.Completion.denseRange_coe

private theorem coefficientInclusion_denseRange :
    DenseRange
      (coefficientInclusion period hPeriod realization) := by
  have hRange :
      Set.range
          (coefficientInclusion period hPeriod realization) =
        Set.range realization.analysis := by
    ext state
    constructor
    · rintro ⟨rangeState, rfl⟩
      rcases rangeState.property with ⟨smoothState, hSmoothState⟩
      exact ⟨smoothState, hSmoothState⟩
    · rintro ⟨smoothState, rfl⟩
      exact
        ⟨⟨realization.analysis smoothState,
            ⟨smoothState, rfl⟩⟩, rfl⟩
  rw [DenseRange, hRange]
  exact realization.analysis_denseRange

private theorem inclusion_norm
    (state : PrimitiveSpinCGeometricFourierRange
      period hPeriod realization) :
    ‖coefficientInclusion period hPeriod realization state‖ =
      ‖completionInclusion period hPeriod realization state‖ := by
  change
    ‖(state : PrimitiveSpinCGeometricL2)‖ =
      ‖(state :
        PrimitiveSpinCGeometricFourierCompletion
          period hPeriod realization)‖
  simp

/-- Canonical unitary extension of smooth Fourier analysis to its intrinsic
completion. -/
def completionEquiv :
    PrimitiveSpinCGeometricFourierCompletion
        period hPeriod realization ≃ₗᵢ[Real]
      PrimitiveSpinCGeometricL2 :=
  LinearEquiv.extendOfIsometry
    (E := PrimitiveSpinCGeometricFourierRange
      period hPeriod realization)
    (F := PrimitiveSpinCGeometricFourierRange
      period hPeriod realization)
    (Eₗ := PrimitiveSpinCGeometricFourierCompletion
      period hPeriod realization)
    (Fₗ := PrimitiveSpinCGeometricL2)
    (LinearEquiv.refl Real
      (PrimitiveSpinCGeometricFourierRange
        period hPeriod realization))
    (completionInclusion period hPeriod realization)
    (coefficientInclusion period hPeriod realization)
    (completionInclusion_denseRange period hPeriod realization)
    (coefficientInclusion_denseRange period hPeriod realization)
    (inclusion_norm period hPeriod realization)

private theorem completionEquiv_range
    (state : PrimitiveSpinCGeometricFourierRange
      period hPeriod realization) :
    realization.completionEquiv period hPeriod
        (state :
          PrimitiveSpinCGeometricFourierCompletion
            period hPeriod realization) =
      (state : PrimitiveSpinCGeometricL2) := by
  change
    completionEquiv period hPeriod realization
        (completionInclusion period hPeriod realization state) =
      coefficientInclusion period hPeriod realization state
  unfold completionEquiv
  rw [LinearEquiv.extendOfIsometry_eq]
  rfl

/-- The smooth geometric core embedded in its intrinsic Fourier
completion. -/
def smoothCoreEmbedding :
    PrimitiveSpinCGeometricSmoothCore period hPeriod →ₗ[Real]
      PrimitiveSpinCGeometricFourierCompletion
        period hPeriod realization :=
  (completionInclusion period hPeriod realization).comp
    realization.analysis.rangeRestrict

/-- The completed unitary is exactly the original Fourier analysis on
smooth sections. -/
@[simp]
theorem completionEquiv_smoothCoreEmbedding
    (state : PrimitiveSpinCGeometricSmoothCore period hPeriod) :
    realization.completionEquiv period hPeriod
        (realization.smoothCoreEmbedding period hPeriod state) =
      realization.analysis state := by
  exact completionEquiv_range period hPeriod realization
    (realization.analysis.rangeRestrict state)

theorem smoothCoreEmbedding_injective :
    Function.Injective
      (realization.smoothCoreEmbedding period hPeriod) := by
  intro first second hEqual
  apply realization.analysis_injective
  simpa using congrArg
    (realization.completionEquiv period hPeriod) hEqual

/-- The original smooth section core remains dense in the intrinsic
completion. -/
theorem smoothCoreEmbedding_denseRange :
    DenseRange
      (realization.smoothCoreEmbedding period hPeriod) := by
  change DenseRange
    ((UniformSpace.Completion.toComplₗᵢ
        (𝕜 := Real)
      (E := PrimitiveSpinCGeometricFourierRange
          period hPeriod realization)) ∘
      realization.analysis.rangeRestrict)
  exact UniformSpace.Completion.denseRange_coe.comp
    realization.analysis.surjective_rangeRestrict.denseRange
    (UniformSpace.Completion.toComplₗᵢ
      (𝕜 := Real)
      (E := PrimitiveSpinCGeometricFourierRange
        period hPeriod realization)).continuous

/-- Pullback of the maximal coefficient `H²` domain to the completed
geometric Fourier space. -/
def completedH2 :
    Submodule Real
      (PrimitiveSpinCGeometricFourierCompletion
        period hPeriod realization) :=
  ((PrimitiveSpinCGeometricH2 period hPeriod).restrictScalars Real).comap
    (realization.completionEquiv period hPeriod).toLinearMap

/-- The completed geometric maximal domain is unitarily the coefficient
maximal domain. -/
def completedH2Equiv :
    realization.completedH2 period hPeriod ≃ₗᵢ[Real]
      (PrimitiveSpinCGeometricH2 period hPeriod).restrictScalars Real where
  toFun state :=
    ⟨realization.completionEquiv period hPeriod state.1, state.2⟩
  invFun state :=
    ⟨(realization.completionEquiv period hPeriod).symm state.1, by
      simpa [completedH2] using state.2⟩
  left_inv state := by
    apply Subtype.ext
    exact
      (realization.completionEquiv
        period hPeriod).symm_apply_apply state.1
  right_inv state := by
    apply Subtype.ext
    exact
      (realization.completionEquiv
        period hPeriod).apply_symm_apply state.1
  map_add' first second := by
    apply Subtype.ext
    exact map_add
      (realization.completionEquiv period hPeriod) first.1 second.1
  map_smul' scalar state := by
    apply Subtype.ext
    exact map_smul
      (realization.completionEquiv period hPeriod) scalar state.1
  norm_map' state :=
    (realization.completionEquiv period hPeriod).norm_map state.1

/-- Squared geometric Dirac transported to the completed smooth Fourier
space. -/
def completedSquaredOperator :
    realization.completedH2 period hPeriod →ₗ[Real]
      PrimitiveSpinCGeometricFourierCompletion
        period hPeriod realization :=
  (realization.completionEquiv period hPeriod).symm.toLinearMap.comp
    (((primitiveSpinCGeometricUnboundedSquared
        period hPeriod).toFun.restrictScalars Real).comp
      (realization.completedH2Equiv period hPeriod).toLinearMap)

/-- Exact conjugacy of the completed geometric and coefficient
realizations. -/
theorem completionEquiv_completedSquaredOperator
    (state : realization.completedH2 period hPeriod) :
    realization.completionEquiv period hPeriod
        (realization.completedSquaredOperator period hPeriod state) =
      primitiveSpinCGeometricUnboundedSquared period hPeriod
        (realization.completedH2Equiv period hPeriod state) := by
  exact
    (realization.completionEquiv
      period hPeriod).apply_symm_apply _

/-- Every smooth geometric section lies in the transported maximal
domain. -/
theorem smoothCoreEmbedding_mem_completedH2
    (state : PrimitiveSpinCGeometricSmoothCore period hPeriod) :
    realization.smoothCoreEmbedding period hPeriod state ∈
      realization.completedH2 period hPeriod := by
  change
    realization.completionEquiv period hPeriod
        (realization.smoothCoreEmbedding period hPeriod state) ∈
      PrimitiveSpinCGeometricH2 period hPeriod
  rw [realization.completionEquiv_smoothCoreEmbedding]
  exact realization.analysis_mem_h2 state

/-- The smooth squared Dirac is exactly the restriction of the transported
completed operator. -/
theorem completedSquaredOperator_smoothCore
    (state : PrimitiveSpinCGeometricSmoothCore period hPeriod) :
    realization.completedSquaredOperator period hPeriod
        ⟨realization.smoothCoreEmbedding period hPeriod state,
          realization.smoothCoreEmbedding_mem_completedH2
            period hPeriod state⟩ =
      realization.smoothCoreEmbedding period hPeriod
        (realization.smoothSquaredOperator state) := by
  apply (realization.completionEquiv period hPeriod).injective
  rw [realization.completionEquiv_completedSquaredOperator,
    realization.completionEquiv_smoothCoreEmbedding]
  have hDomain :
      realization.completedH2Equiv period hPeriod
          ⟨realization.smoothCoreEmbedding period hPeriod state,
            realization.smoothCoreEmbedding_mem_completedH2
              period hPeriod state⟩ =
        ⟨realization.analysis state,
          realization.analysis_mem_h2 state⟩ := by
    apply Subtype.ext
    exact
      realization.completionEquiv_smoothCoreEmbedding
        period hPeriod state
  rw [hDomain]
  exact (realization.analysis_intertwines state).symm

/-- Graph energy is preserved by the completed Fourier unitary. -/
theorem completedFourier_graphEnergy
    (state : realization.completedH2 period hPeriod) :
    ‖(state :
        PrimitiveSpinCGeometricFourierCompletion
          period hPeriod realization)‖ ^ 2 +
        ‖realization.completedSquaredOperator
          period hPeriod state‖ ^ 2 =
      ‖((realization.completedH2Equiv period hPeriod state :
          (PrimitiveSpinCGeometricH2
            period hPeriod).restrictScalars Real) :
          PrimitiveSpinCGeometricL2)‖ ^ 2 +
        ‖primitiveSpinCGeometricUnboundedSquared period hPeriod
          (realization.completedH2Equiv period hPeriod state)‖ ^ 2 := by
  rw [show
      ‖(state :
          PrimitiveSpinCGeometricFourierCompletion
            period hPeriod realization)‖ =
        ‖((realization.completedH2Equiv period hPeriod state :
            (PrimitiveSpinCGeometricH2
              period hPeriod).restrictScalars Real) :
            PrimitiveSpinCGeometricL2)‖ by
      exact
        (realization.completionEquiv
          period hPeriod).norm_map state.1 |>.symm,
    show
      ‖realization.completedSquaredOperator
          period hPeriod state‖ =
        ‖primitiveSpinCGeometricUnboundedSquared period hPeriod
          (realization.completedH2Equiv period hPeriod state)‖ by
      rw [← realization.completionEquiv_completedSquaredOperator,
        (realization.completionEquiv period hPeriod).norm_map]]

/-- The geometric completion inherits the coefficient spectral-gap
coercivity estimate exactly. -/
theorem completedSquaredOperator_coercive
    (state : realization.completedH2 period hPeriod) :
    ‖(state :
        PrimitiveSpinCGeometricFourierCompletion
          period hPeriod realization)‖ ≤
      (primitiveSpinCGeometricSpectralGap period)⁻¹ *
        ‖realization.completedSquaredOperator
          period hPeriod state‖ := by
  have hOperatorNorm :
      ‖realization.completedSquaredOperator period hPeriod state‖ =
        ‖primitiveSpinCGeometricUnboundedSquared period hPeriod
          (realization.completedH2Equiv period hPeriod state)‖ := by
    rw [← realization.completionEquiv_completedSquaredOperator,
      (realization.completionEquiv period hPeriod).norm_map]
  calc
    ‖(state :
        PrimitiveSpinCGeometricFourierCompletion
          period hPeriod realization)‖ =
        ‖((realization.completedH2Equiv period hPeriod state :
            (PrimitiveSpinCGeometricH2
              period hPeriod).restrictScalars Real) :
            PrimitiveSpinCGeometricL2)‖ := by
      exact
        (realization.completionEquiv
          period hPeriod).norm_map state.1 |>.symm
    _ ≤
        (primitiveSpinCGeometricSpectralGap period)⁻¹ *
          ‖primitiveSpinCGeometricUnboundedSquared period hPeriod
            (realization.completedH2Equiv period hPeriod state)‖ :=
      primitiveSpinCGeometricUnboundedSquared_coercive
        period hPeriod
        (realization.completedH2Equiv period hPeriod state)
    _ =
        (primitiveSpinCGeometricSpectralGap period)⁻¹ *
          ‖realization.completedSquaredOperator
            period hPeriod state‖ := by
      rw [hOperatorNorm]

/-- The completed geometric squared operator is bijective because its
coefficient representative has the proven positive spectral gap. -/
theorem completedSquaredOperator_bijective :
    Function.Bijective
      (realization.completedSquaredOperator period hPeriod) := by
  constructor
  · intro first second hEqual
    apply (realization.completedH2Equiv period hPeriod).injective
    apply
      (primitiveSpinCGeometricUnboundedSquared_bijective
        period hPeriod).1
    have hImages :=
      congrArg (realization.completionEquiv period hPeriod) hEqual
    simpa only
      [realization.completionEquiv_completedSquaredOperator] using hImages
  · intro output
    obtain ⟨coefficientState, hCoefficientState⟩ :=
      (primitiveSpinCGeometricUnboundedSquared_bijective
        period hPeriod).2
        (realization.completionEquiv period hPeriod output)
    refine
      ⟨(realization.completedH2Equiv period hPeriod).symm
          coefficientState, ?_⟩
    apply (realization.completionEquiv period hPeriod).injective
    rw [realization.completionEquiv_completedSquaredOperator,
      (realization.completedH2Equiv
        period hPeriod).apply_symm_apply,
      hCoefficientState]

/-- Completion/domain/operator closure follows from any all-level
geometric Fourier realization; it is not a second analytic assumption. -/
structure GeometricFourierCompletionCertificate : Prop where
  smoothCoreDense :
    DenseRange (realization.smoothCoreEmbedding period hPeriod)
  smoothCoreInjective :
    Function.Injective
      (realization.smoothCoreEmbedding period hPeriod)
  smoothOperatorAgreement :
    ∀ state,
      realization.completedSquaredOperator period hPeriod
          ⟨realization.smoothCoreEmbedding period hPeriod state,
            realization.smoothCoreEmbedding_mem_completedH2
              period hPeriod state⟩ =
        realization.smoothCoreEmbedding period hPeriod
          (realization.smoothSquaredOperator state)
  graphEnergyPreserved :
    ∀ state : realization.completedH2 period hPeriod, ‖(state :
        PrimitiveSpinCGeometricFourierCompletion
          period hPeriod realization)‖ ^ 2 +
        ‖realization.completedSquaredOperator period hPeriod state‖ ^ 2 =
      ‖((realization.completedH2Equiv period hPeriod state :
          (PrimitiveSpinCGeometricH2
            period hPeriod).restrictScalars Real) :
          PrimitiveSpinCGeometricL2)‖ ^ 2 +
        ‖primitiveSpinCGeometricUnboundedSquared period hPeriod
          (realization.completedH2Equiv period hPeriod state)‖ ^ 2
  coercive :
    ∀ state : realization.completedH2 period hPeriod,
      ‖(state :
          PrimitiveSpinCGeometricFourierCompletion
            period hPeriod realization)‖ ≤
        (primitiveSpinCGeometricSpectralGap period)⁻¹ *
          ‖realization.completedSquaredOperator
            period hPeriod state‖
  bijective :
    Function.Bijective
      (realization.completedSquaredOperator period hPeriod)

def geometricFourierCompletionCertificate :
    realization.GeometricFourierCompletionCertificate
      period hPeriod where
  smoothCoreDense :=
    realization.smoothCoreEmbedding_denseRange period hPeriod
  smoothCoreInjective :=
    realization.smoothCoreEmbedding_injective period hPeriod
  smoothOperatorAgreement :=
    realization.completedSquaredOperator_smoothCore period hPeriod
  graphEnergyPreserved :=
    realization.completedFourier_graphEnergy period hPeriod
  coercive :=
    realization.completedSquaredOperator_coercive period hPeriod
  bijective :=
    realization.completedSquaredOperator_bijective period hPeriod

end ProgramPD9PrimitiveSpinCGeometricFourierRealization4D

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierBridge4D
end JanusFormal
