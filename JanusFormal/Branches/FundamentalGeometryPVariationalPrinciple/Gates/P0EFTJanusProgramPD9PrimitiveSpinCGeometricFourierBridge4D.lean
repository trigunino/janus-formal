import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

/-!
# Geometric Fourier frontier for the primitive D9 SpinC bundle

The primitive bundle, its smooth section core and the complete coefficient
spectrum are now constructed.  The zero-sphere tower is realized by actual
global smooth Hopf eigenspinors, with first-order Dirac and squared-Hilbert
intertwining, in
`P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D`.
What remains here is the positive-sphere eigenspinor tower, Fourier
completeness on the whole smooth core and the identification of the full
geometric squared Dirac operator with the maximal diagonal realization.

This gate records precisely that datum and proves all formal consequences.
It deliberately has no unconditional inhabitant: completing one requires
the positive global monopole eigenspinors, which are not presently available
in Mathlib or elsewhere in this repository.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierBridge4D

set_option autoImplicit false
noncomputable section

open Filter Set Topology
open scoped BigOperators ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

/-- Smooth real section core of one primitive doubled SpinC bundle. -/
abbrev PrimitiveSpinCGeometricSmoothCore :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

/-- Finite coordinate projection in the complete primitive spectrum. -/
def primitiveSpinCGeometricFiniteProjection
    (modes : Finset PrimitiveSpinCGeometricFullMode)
    (state : PrimitiveSpinCGeometricL2) :
    PrimitiveSpinCGeometricL2 :=
  ∑ mode ∈ modes, lp.single 2 mode (state mode)

theorem primitiveSpinCGeometricFiniteProjection_tendsto
    (state : PrimitiveSpinCGeometricL2) :
    Tendsto
      (fun modes : Finset PrimitiveSpinCGeometricFullMode =>
        primitiveSpinCGeometricFiniteProjection modes state)
      atTop (𝓝 state) := by
  change HasSum
    (fun mode : PrimitiveSpinCGeometricFullMode =>
      lp.single 2 mode (state mode)) state
  exact lp.hasSum_single ENNReal.ofNat_ne_top state

private theorem real_imaginary_single_decomposition
    (mode : PrimitiveSpinCGeometricFullMode)
    (value : Complex) :
    value.re •
          (lp.single 2 mode (1 : Complex) :
            PrimitiveSpinCGeometricL2) +
        value.im •
          (lp.single 2 mode Complex.I :
            PrimitiveSpinCGeometricL2) =
      lp.single 2 mode value := by
  ext coordinate
  by_cases hCoordinate : coordinate = mode
  · subst coordinate
    simp [lp.single_apply]
  · simp [lp.single_apply, hCoordinate]

/-- Exact missing geometric input.  Two smooth mode sections are needed per
complex coordinate because the geometric section core is a real module. -/
structure ProgramPD9PrimitiveSpinCGeometricFourierRealization4D where
  analysis :
    PrimitiveSpinCGeometricSmoothCore period hPeriod →ₗ[Real]
      PrimitiveSpinCGeometricL2
  realModeSection :
    PrimitiveSpinCGeometricFullMode →
      PrimitiveSpinCGeometricSmoothCore period hPeriod
  imaginaryModeSection :
    PrimitiveSpinCGeometricFullMode →
      PrimitiveSpinCGeometricSmoothCore period hPeriod
  analysis_realModeSection :
    ∀ mode, analysis (realModeSection mode) =
      lp.single 2 mode (1 : Complex)
  analysis_imaginaryModeSection :
    ∀ mode, analysis (imaginaryModeSection mode) =
      lp.single 2 mode Complex.I
  analysis_injective : Function.Injective analysis
  smoothSquaredOperator :
    PrimitiveSpinCGeometricSmoothCore period hPeriod →ₗ[Real]
      PrimitiveSpinCGeometricSmoothCore period hPeriod
  analysis_mem_h2 :
    ∀ state, analysis state ∈
      PrimitiveSpinCGeometricH2 period hPeriod
  analysis_intertwines :
    ∀ state,
      analysis (smoothSquaredOperator state) =
        primitiveSpinCGeometricUnboundedSquared period hPeriod
          ⟨analysis state, analysis_mem_h2 state⟩

namespace ProgramPD9PrimitiveSpinCGeometricFourierRealization4D

variable
  (realization :
    ProgramPD9PrimitiveSpinCGeometricFourierRealization4D
      period hPeriod)

/-- Smooth synthesis of an arbitrary finite complex mode packet. -/
def finiteSynthesis
    (modes : Finset PrimitiveSpinCGeometricFullMode)
    (state : PrimitiveSpinCGeometricL2) :
    PrimitiveSpinCGeometricSmoothCore period hPeriod :=
  ∑ mode ∈ modes,
    (((state mode).re • realization.realModeSection mode) +
      ((state mode).im • realization.imaginaryModeSection mode))

/-- Geometric finite synthesis is exactly spectral finite projection. -/
theorem analysis_finiteSynthesis
    (modes : Finset PrimitiveSpinCGeometricFullMode)
    (state : PrimitiveSpinCGeometricL2) :
    realization.analysis
        (finiteSynthesis period hPeriod realization modes state) =
      primitiveSpinCGeometricFiniteProjection modes state := by
  classical
  rw [finiteSynthesis, primitiveSpinCGeometricFiniteProjection, map_sum]
  apply Finset.sum_congr rfl
  intro mode _
  rw [map_add, map_smul, map_smul,
    realization.analysis_realModeSection,
    realization.analysis_imaginaryModeSection]
  exact real_imaginary_single_decomposition mode (state mode)

theorem finiteProjection_mem_analysis_range
    (modes : Finset PrimitiveSpinCGeometricFullMode)
    (state : PrimitiveSpinCGeometricL2) :
    primitiveSpinCGeometricFiniteProjection modes state ∈
      Set.range realization.analysis :=
  ⟨finiteSynthesis period hPeriod realization modes state,
    analysis_finiteSynthesis period hPeriod realization modes state⟩

/-- Global mode sections force dense geometric Fourier range. -/
theorem analysis_denseRange :
    DenseRange realization.analysis := by
  intro state
  apply mem_closure_of_tendsto
    (primitiveSpinCGeometricFiniteProjection_tendsto state)
  exact Filter.Eventually.of_forall fun modes =>
    finiteProjection_mem_analysis_range
      period hPeriod realization modes state

/-- The geometric `L²` norm induced by Fourier analysis on the smooth
section core. -/
def inducedL2Norm
    (state : PrimitiveSpinCGeometricSmoothCore period hPeriod) :
    Real :=
  ‖realization.analysis state‖

theorem inducedL2Norm_eq_zero_iff
    (state : PrimitiveSpinCGeometricSmoothCore period hPeriod) :
    inducedL2Norm period hPeriod realization state = 0 ↔
      state = 0 := by
  rw [inducedL2Norm, norm_eq_zero]
  rw [← map_zero realization.analysis]
  exact realization.analysis_injective.eq_iff

/-- Coercivity on the genuine smooth bundle core follows solely from the
proven spectral gap and the intertwining theorem. -/
theorem smoothSquaredOperator_coercive
    (state : PrimitiveSpinCGeometricSmoothCore period hPeriod) :
    inducedL2Norm period hPeriod realization state ≤
      (primitiveSpinCGeometricSpectralGap period)⁻¹ *
        inducedL2Norm period hPeriod realization
          (realization.smoothSquaredOperator state) := by
  unfold inducedL2Norm
  rw [realization.analysis_intertwines]
  exact primitiveSpinCGeometricUnboundedSquared_coercive
    period hPeriod
    ⟨realization.analysis state, realization.analysis_mem_h2 state⟩

/-- The smooth geometric squared operator has the advertised coefficient
multiplier on every state. -/
theorem analysis_smoothSquaredOperator_apply
    (state : PrimitiveSpinCGeometricSmoothCore period hPeriod)
    (mode : PrimitiveSpinCGeometricFullMode) :
    realization.analysis (realization.smoothSquaredOperator state) mode =
      (primitiveSpinCGeometricSquaredEigenvalue
          period hPeriod mode : Complex) *
        realization.analysis state mode := by
  rw [realization.analysis_intertwines]
  exact complexDiagonalOperator_apply
    PrimitiveSpinCGeometricFullMode
    (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)
    ⟨realization.analysis state, realization.analysis_mem_h2 state⟩ mode

/-- The real representative of every complex mode is a genuine smooth
eigenvector of the geometric squared operator. -/
theorem smoothSquaredOperator_realModeSection
    (mode : PrimitiveSpinCGeometricFullMode) :
    realization.smoothSquaredOperator
        (realization.realModeSection mode) =
      primitiveSpinCGeometricSquaredEigenvalue period hPeriod mode •
        realization.realModeSection mode := by
  apply realization.analysis_injective
  ext coordinate
  rw [realization.analysis_smoothSquaredOperator_apply, map_smul,
    realization.analysis_realModeSection]
  by_cases hCoordinate : coordinate = mode
  · subst coordinate
    simp [lp.single_apply]
  · simp [lp.single_apply, hCoordinate]

/-- The imaginary representative is the second real eigenvector belonging
to the same complex coordinate. -/
theorem smoothSquaredOperator_imaginaryModeSection
    (mode : PrimitiveSpinCGeometricFullMode) :
    realization.smoothSquaredOperator
        (realization.imaginaryModeSection mode) =
      primitiveSpinCGeometricSquaredEigenvalue period hPeriod mode •
        realization.imaginaryModeSection mode := by
  apply realization.analysis_injective
  ext coordinate
  rw [realization.analysis_smoothSquaredOperator_apply, map_smul,
    realization.analysis_imaginaryModeSection]
  by_cases hCoordinate : coordinate = mode
  · subst coordinate
    simp [lp.single_apply]
  · simp [lp.single_apply, hCoordinate]

/-- The geometric operator is injective, as a consequence of the proven
spectral gap rather than an additional assumption. -/
theorem smoothSquaredOperator_injective :
    Function.Injective realization.smoothSquaredOperator := by
  intro first second hEqual
  apply realization.analysis_injective
  have hImages := congrArg realization.analysis hEqual
  rw [realization.analysis_intertwines,
    realization.analysis_intertwines] at hImages
  have hDiagonal :=
    (primitiveSpinCGeometricUnboundedSquared_bijective
      period hPeriod).1 hImages
  exact congrArg Subtype.val hDiagonal

end ProgramPD9PrimitiveSpinCGeometricFourierRealization4D

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierBridge4D
end JanusFormal
