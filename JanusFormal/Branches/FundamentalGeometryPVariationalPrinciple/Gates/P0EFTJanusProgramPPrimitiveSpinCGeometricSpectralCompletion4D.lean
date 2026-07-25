import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCModeDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D

/-!
# Geometrically scaled primitive SpinC spectral completion

The previous full primitive completion restores the monopole sphere zero
mode for one external fold.  Here both normal-root sectors are included in
the mode label and the circle eigenvalue uses the actual mapping-torus
period.  Positive sphere levels are identified exactly with the existing
multiplicity-aware D10 labels, while the missing zero-sphere tower remains
an explicit additional summand.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPD7CircleHeatRegulatorBridge
open P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D
open P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCModeDecomposition4D
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

/-- Both normal-root sectors of the complete primitive spectrum. -/
abbrev PrimitiveSpinCGeometricFullMode :=
  NormalRootChoice × PrimitiveSpinCFullMode

/-- D10 labels extended by precisely the missing zero-sphere tower. -/
abbrev PrimitiveSpinCExtendedD10Mode :=
  (NormalRootChoice × Int) ⊕
    ProgramPD10Mode4D (PrimitiveSpinCSpectralData period hPeriod)

/-- Product-throat positive modes with their normal-root label are exactly
the multiplicity-aware D10 labels. -/
def primitiveSpinCPositiveD10ModeEquiv :
    (NormalRootChoice ×
      ProductThroatHeatMode
        (PrimitiveSpinCSpectralData period hPeriod)) ≃
      ProgramPD10Mode4D
        (PrimitiveSpinCSpectralData period hPeriod) where
  toFun mode :=
    { separatedMode :=
        { sphereLevel := mode.2.1.1
          circleMode := mode.2.2
          rootChoice := mode.1 }
      sphereMultiplicityIndex := mode.2.1.2 }
  invFun mode :=
    (mode.separatedMode.rootChoice,
      (⟨mode.separatedMode.sphereLevel,
        mode.sphereMultiplicityIndex⟩,
        mode.separatedMode.circleMode))
  left_inv mode := by
    rcases mode with ⟨choice, ⟨⟨level, multiplicity⟩, circleMode⟩⟩
    rfl
  right_inv mode := by
    rcases mode with ⟨⟨level, circleMode, choice⟩, multiplicity⟩
    rfl

/-- Exact mode-label decomposition of the doubled primitive spectrum. -/
def primitiveSpinCGeometricFullModeEquiv :
    PrimitiveSpinCGeometricFullMode ≃
      PrimitiveSpinCExtendedD10Mode period hPeriod :=
  (((Equiv.refl NormalRootChoice).prodCongr
      (primitiveSpinCFullModeEquiv period hPeriod)).trans
    (Equiv.prodSumDistrib NormalRootChoice Int
      (ProductThroatHeatMode
        (PrimitiveSpinCSpectralData period hPeriod)))).trans
      (Equiv.sumCongr (Equiv.refl (NormalRootChoice × Int))
        (primitiveSpinCPositiveD10ModeEquiv period hPeriod))

/-- Canonical full mode in the zero-sphere tower. -/
def primitiveSpinCGeometricZeroMode
    (choice : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCGeometricFullMode :=
  (choice, primitiveSpinCZeroSphereMode circleMode)

/-- Canonical embedding of an existing D10 mode into the positive-level
part of the full primitive spectrum. -/
def programPD10ModeToPrimitiveSpinCGeometricMode
    (mode : ProgramPD10Mode4D
      (PrimitiveSpinCSpectralData period hPeriod)) :
    PrimitiveSpinCGeometricFullMode :=
  (mode.separatedMode.rootChoice,
    primitiveSpinCPositiveModeEmbedding period hPeriod
      (⟨⟨mode.separatedMode.sphereLevel,
          mode.sphereMultiplicityIndex⟩,
        mode.separatedMode.circleMode⟩))

@[simp]
theorem primitiveSpinCGeometricFullModeEquiv_zero
    (choice : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCGeometricFullModeEquiv period hPeriod
        (primitiveSpinCGeometricZeroMode choice circleMode) =
      Sum.inl (choice, circleMode) := by
  rfl

@[simp]
theorem primitiveSpinCGeometricFullModeEquiv_positive
    (mode : ProgramPD10Mode4D
      (PrimitiveSpinCSpectralData period hPeriod)) :
    primitiveSpinCGeometricFullModeEquiv period hPeriod
        (programPD10ModeToPrimitiveSpinCGeometricMode
          period hPeriod mode) =
      Sum.inr mode := by
  rcases mode with ⟨⟨level, circleMode, choice⟩, multiplicity⟩
  rfl

theorem programPD10ModeToPrimitiveSpinCGeometricMode_injective :
    Function.Injective
      (programPD10ModeToPrimitiveSpinCGeometricMode
        period hPeriod) := by
  intro first second hEqual
  have hMapped := congrArg
    (primitiveSpinCGeometricFullModeEquiv period hPeriod) hEqual
  simpa using hMapped

/-- Squared primitive SpinC eigenvalue with the actual circle period and
both normal-root sectors. -/
def primitiveSpinCGeometricSquaredEigenvalue
    (mode : PrimitiveSpinCGeometricFullMode) : Real :=
  primitiveSpinCFullSphereEigenvalueSquared mode.2.1.1 +
    circleEigenvalue
      (PrimitiveSpinCSpectralData period hPeriod)
      mode.1 mode.2.2 ^ 2

theorem primitiveSpinCGeometricSquaredEigenvalue_nonnegative
    (mode : PrimitiveSpinCGeometricFullMode) :
    0 ≤ primitiveSpinCGeometricSquaredEigenvalue
      period hPeriod mode := by
  exact add_nonneg
    (primitiveSpinCFullSphereEigenvalueSquared_nonnegative
      mode.2.1.1)
    (sq_nonneg _)

/-- On the added zero-sphere tower only the geometric circle energy
remains. -/
@[simp]
theorem primitiveSpinCGeometricZeroMode_squaredEigenvalue
    (choice : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCGeometricSquaredEigenvalue period hPeriod
        (primitiveSpinCGeometricZeroMode choice circleMode) =
      circleEigenvalue
        (PrimitiveSpinCSpectralData period hPeriod)
        choice circleMode ^ 2 := by
  simp [primitiveSpinCGeometricSquaredEigenvalue,
    primitiveSpinCGeometricZeroMode,
    primitiveSpinCZeroSphereMode]

/-- Every positive full mode has exactly the existing geometric D10
squared eigenvalue, including its root and circle label. -/
theorem programPD10ModeToPrimitiveSpinCGeometricMode_squaredEigenvalue
    (mode : ProgramPD10Mode4D
      (PrimitiveSpinCSpectralData period hPeriod)) :
    primitiveSpinCGeometricSquaredEigenvalue period hPeriod
        (programPD10ModeToPrimitiveSpinCGeometricMode
          period hPeriod mode) =
      productDiracEigenvalueSquared
        (PrimitiveSpinCSpectralData period hPeriod)
        mode.separatedMode := by
  rcases mode with ⟨⟨level, circleMode, choice⟩, multiplicity⟩
  change
    primitiveSpinCFullSphereEigenvalueSquared (level + 1) +
        circleEigenvalue
          (PrimitiveSpinCSpectralData period hPeriod)
          choice circleMode ^ 2 =
      sphereEigenvalueSquared
          (PrimitiveSpinCSpectralData period hPeriod) level +
        circleEigenvalue
          (PrimitiveSpinCSpectralData period hPeriod)
          choice circleMode ^ 2
  rw [primitiveSpinCFull_positiveSphereEigenvalue_agrees
    period hPeriod level]

/-- Uniform geometric gap contributed by either the positive sphere level
or the quarter-twisted zero-sphere circle mode. -/
def primitiveSpinCGeometricSpectralGap : Real :=
  min 1
    ((Real.pi / (2 * |period|)) ^ 2)

theorem primitiveSpinCGeometricSpectralGap_pos
    (hPeriod : period ≠ 0) :
    0 < primitiveSpinCGeometricSpectralGap period := by
  unfold primitiveSpinCGeometricSpectralGap
  have hCircle :
      0 < (Real.pi / (2 * |period|)) ^ 2 :=
    sq_pos_of_pos
    (div_pos Real.pi_pos
      (mul_pos (by norm_num) (abs_pos.mpr hPeriod)))
  exact lt_min one_pos hCircle

private theorem normalRootModeNumerator_real_abs_ge_one
    (choice : NormalRootChoice) (circleMode : Int) :
    (1 : Real) ≤
      |(normalRootModeNumerator choice circleMode : Real)| := by
  exact_mod_cast
    Int.one_le_abs
      (normal_root_mode_numerator_nonzero choice circleMode)

theorem primitiveSpinCGeometric_circle_gap
    (choice : NormalRootChoice) (circleMode : Int) :
    (Real.pi / (2 * |period|)) ^ 2 ≤
      circleEigenvalue
        (PrimitiveSpinCSpectralData period hPeriod)
        choice circleMode ^ 2 := by
  have hNumerator :=
    normalRootModeNumerator_real_abs_ge_one choice circleMode
  have hNumeratorSq :
      (1 : Real) ≤
        (normalRootModeNumerator choice circleMode : Real) ^ 2 := by
    nlinarith [sq_abs
      (normalRootModeNumerator choice circleMode : Real)]
  have hScaleNonnegative :
      0 ≤ (Real.pi / (2 * |period|)) ^ 2 :=
    sq_nonneg _
  calc
    (Real.pi / (2 * |period|)) ^ 2 =
        (Real.pi / (2 * |period|)) ^ 2 * 1 := by ring
    _ ≤
        (Real.pi / (2 * |period|)) ^ 2 *
          (normalRootModeNumerator choice circleMode : Real) ^ 2 :=
      mul_le_mul_of_nonneg_left hNumeratorSq hScaleNonnegative
    _ =
        circleEigenvalue
          (PrimitiveSpinCSpectralData period hPeriod)
          choice circleMode ^ 2 := by
      unfold circleEigenvalue
      change
        (Real.pi / (2 * |period|)) ^ 2 *
            (normalRootModeNumerator choice circleMode : Real) ^ 2 =
          (Real.pi *
              (normalRootModeNumerator choice circleMode : Real) /
            (2 * |period|)) ^ 2
      ring

theorem primitiveSpinCGeometricSpectralGap_le
    (mode : PrimitiveSpinCGeometricFullMode) :
    primitiveSpinCGeometricSpectralGap period ≤
      primitiveSpinCGeometricSquaredEigenvalue
        period hPeriod mode := by
  unfold primitiveSpinCGeometricSpectralGap
    primitiveSpinCGeometricSquaredEigenvalue
  rcases mode with ⟨choice, ⟨⟨level, multiplicity⟩, circleMode⟩⟩
  cases level with
  | zero =>
      simp only [primitiveSpinCFullSphereEigenvalueSquared,
        Nat.cast_zero, zero_mul, zero_add]
      have hMin :
          min 1 ((Real.pi / (2 * |period|)) ^ 2) ≤
            (Real.pi / (2 * |period|)) ^ 2 :=
        min_le_right _ _
      exact hMin.trans
        (primitiveSpinCGeometric_circle_gap
          period hPeriod choice circleMode)
  | succ level =>
      change
        min 1 ((Real.pi / (2 * |period|)) ^ 2) ≤
          primitiveSpinCFullSphereEigenvalueSquared level.succ +
            circleEigenvalue
              (PrimitiveSpinCSpectralData period hPeriod)
              choice circleMode ^ 2
      have hLevel :
          (1 : Real) ≤ (level.succ : Real) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le level)
      have hShift :
          (1 : Real) ≤ ((level.succ + 1 : Nat) : Real) := by
        exact_mod_cast
          (show 1 ≤ level.succ + 1 by omega)
      have hSphere :
          (1 : Real) ≤
            primitiveSpinCFullSphereEigenvalueSquared level.succ := by
        unfold primitiveSpinCFullSphereEigenvalueSquared
        nlinarith
      have hMin :
          min 1 ((Real.pi / (2 * |period|)) ^ 2) ≤ 1 :=
        min_le_left _ _
      exact hMin.trans
        (hSphere.trans
          (le_add_of_nonneg_right (sq_nonneg _)))

/-- Complete geometrically scaled coefficient Hilbert space. -/
abbrev PrimitiveSpinCGeometricL2 :=
  ComplexDiagonalHilbert PrimitiveSpinCGeometricFullMode

/-- Complete coefficient space after separating the monopole zero tower
from the already existing positive D10 modes. -/
abbrev PrimitiveSpinCExtendedD10L2 :=
  ComplexDiagonalHilbert
    (PrimitiveSpinCExtendedD10Mode period hPeriod)

/-- Hilbert-level form of the exact full-mode decomposition. -/
def primitiveSpinCGeometricExtendedD10L2Equiv :
    PrimitiveSpinCGeometricL2 ≃ₗᵢ[Complex]
      PrimitiveSpinCExtendedD10L2 period hPeriod :=
  complexDiagonalHilbertCongr PrimitiveSpinCGeometricFullMode
    (primitiveSpinCGeometricFullModeEquiv period hPeriod)

@[simp]
theorem primitiveSpinCGeometricExtendedD10L2Equiv_zero_single
    (choice : NormalRootChoice) (circleMode : Int)
    (value : Complex) :
    primitiveSpinCGeometricExtendedD10L2Equiv period hPeriod
        (lp.single 2
          (primitiveSpinCGeometricZeroMode choice circleMode) value) =
      lp.single 2 (Sum.inl (choice, circleMode)) value := by
  rw [primitiveSpinCGeometricExtendedD10L2Equiv,
    complexDiagonalHilbertCongr_single,
    primitiveSpinCGeometricFullModeEquiv_zero]

@[simp]
theorem primitiveSpinCGeometricExtendedD10L2Equiv_positive_single
    (mode : ProgramPD10Mode4D
      (PrimitiveSpinCSpectralData period hPeriod))
    (value : Complex) :
    primitiveSpinCGeometricExtendedD10L2Equiv period hPeriod
        (lp.single 2
          (programPD10ModeToPrimitiveSpinCGeometricMode
            period hPeriod mode) value) =
      lp.single 2 (Sum.inr mode) value := by
  rw [primitiveSpinCGeometricExtendedD10L2Equiv,
    complexDiagonalHilbertCongr_single,
    primitiveSpinCGeometricFullModeEquiv_positive]

theorem primitiveSpinCGeometricExtendedD10L2Equiv_norm
    (state : PrimitiveSpinCGeometricL2) :
    ‖primitiveSpinCGeometricExtendedD10L2Equiv
        period hPeriod state‖ = ‖state‖ :=
  (primitiveSpinCGeometricExtendedD10L2Equiv
    period hPeriod).norm_map state

/-- Maximal graph domain of the geometric squared SpinC operator. -/
abbrev PrimitiveSpinCGeometricH2 :=
  complexDiagonalDomain PrimitiveSpinCGeometricFullMode
    (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)

/-- Maximal geometrically scaled squared SpinC realization. -/
abbrev primitiveSpinCGeometricUnboundedSquared :=
  complexDiagonalOperator PrimitiveSpinCGeometricFullMode
    (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)

theorem primitiveSpinCGeometricH2_dense :
    Dense
      (PrimitiveSpinCGeometricH2 period hPeriod :
        Set PrimitiveSpinCGeometricL2) :=
  complexDiagonalDomain_dense PrimitiveSpinCGeometricFullMode
    (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)

theorem primitiveSpinCGeometricUnboundedSquared_isSelfAdjoint :
    IsSelfAdjoint
      (primitiveSpinCGeometricUnboundedSquared period hPeriod) :=
  complexDiagonalOperator_isSelfAdjoint PrimitiveSpinCGeometricFullMode
    (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)

theorem primitiveSpinCGeometricUnboundedSquared_isClosed :
    (primitiveSpinCGeometricUnboundedSquared
      period hPeriod).IsClosed :=
  complexDiagonalOperator_isClosed PrimitiveSpinCGeometricFullMode
    (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)

private theorem primitiveSpinCGeometricSpectralGap_le_abs
    (mode : PrimitiveSpinCGeometricFullMode) :
    primitiveSpinCGeometricSpectralGap period ≤
      |primitiveSpinCGeometricSquaredEigenvalue
        period hPeriod mode| := by
  rw [abs_of_nonneg
    (primitiveSpinCGeometricSquaredEigenvalue_nonnegative
      period hPeriod mode)]
  exact primitiveSpinCGeometricSpectralGap_le
    period hPeriod mode

/-- Uniform coercivity of the complete geometrically scaled squared
primitive SpinC operator. -/
theorem primitiveSpinCGeometricUnboundedSquared_coercive
    (state : PrimitiveSpinCGeometricH2 period hPeriod) :
    ‖state.1‖ ≤
      (primitiveSpinCGeometricSpectralGap period)⁻¹ *
        ‖primitiveSpinCGeometricUnboundedSquared
          period hPeriod state‖ :=
  complexDiagonalOperator_coercive
    PrimitiveSpinCGeometricFullMode
    (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)
    (primitiveSpinCGeometricSpectralGap period)
    (primitiveSpinCGeometricSpectralGap_pos period hPeriod)
    (primitiveSpinCGeometricSpectralGap_le_abs period hPeriod)
    state

theorem primitiveSpinCGeometricUnboundedSquared_bijective :
    Function.Bijective
      (primitiveSpinCGeometricUnboundedSquared period hPeriod) :=
  ⟨complexDiagonalOperator_injective_of_gap
      PrimitiveSpinCGeometricFullMode
      (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)
      (primitiveSpinCGeometricSpectralGap period)
      (primitiveSpinCGeometricSpectralGap_pos period hPeriod)
      (primitiveSpinCGeometricSpectralGap_le_abs period hPeriod),
    complexDiagonalOperator_surjective_of_gap
      PrimitiveSpinCGeometricFullMode
      (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)
      (primitiveSpinCGeometricSpectralGap period)
      (primitiveSpinCGeometricSpectralGap_pos period hPeriod)
      (primitiveSpinCGeometricSpectralGap_le_abs period hPeriod)⟩

theorem primitiveSpinCGeometricUnboundedSquared_fredholm :
    IsClosed
        (LinearMap.range
            (primitiveSpinCGeometricUnboundedSquared
              period hPeriod).toFun :
          Set PrimitiveSpinCGeometricL2) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (primitiveSpinCGeometricUnboundedSquared
            period hPeriod).toFun) ∧
      FiniteDimensional Complex
        (ComplexDiagonalCokernel PrimitiveSpinCGeometricFullMode
          (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)) :=
  complexDiagonalOperator_fredholm_of_gap
    PrimitiveSpinCGeometricFullMode
    (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)
    (primitiveSpinCGeometricSpectralGap period)
    (primitiveSpinCGeometricSpectralGap_pos period hPeriod)
    (primitiveSpinCGeometricSpectralGap_le_abs period hPeriod)

theorem primitiveSpinCGeometricUnboundedSquared_index_zero :
    complexDiagonalOperatorIndex PrimitiveSpinCGeometricFullMode
      (primitiveSpinCGeometricSquaredEigenvalue period hPeriod) = 0 :=
  complexDiagonalOperatorIndex_zero_of_gap
    PrimitiveSpinCGeometricFullMode
    (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)
    (primitiveSpinCGeometricSpectralGap period)
    (primitiveSpinCGeometricSpectralGap_pos period hPeriod)
    (primitiveSpinCGeometricSpectralGap_le_abs period hPeriod)

/-- Concrete certificate combining the exact D10 positive-level agreement,
the missing zero tower, and the closed Fredholm realization. -/
structure ProgramPPrimitiveSpinCGeometricSpectralCertificate4D where
  modeDecomposition :
    PrimitiveSpinCGeometricFullMode ≃
      PrimitiveSpinCExtendedD10Mode period hPeriod
  positiveD10Agreement :
    ∀ mode : ProgramPD10Mode4D
        (PrimitiveSpinCSpectralData period hPeriod),
      primitiveSpinCGeometricSquaredEigenvalue period hPeriod
          (programPD10ModeToPrimitiveSpinCGeometricMode
            period hPeriod mode) =
        productDiracEigenvalueSquared
          (PrimitiveSpinCSpectralData period hPeriod)
          mode.separatedMode
  h2Dense :
    Dense
      (PrimitiveSpinCGeometricH2 period hPeriod :
        Set PrimitiveSpinCGeometricL2)
  selfAdjoint :
    IsSelfAdjoint
      (primitiveSpinCGeometricUnboundedSquared period hPeriod)
  fredholmIndexZero :
    complexDiagonalOperatorIndex PrimitiveSpinCGeometricFullMode
      (primitiveSpinCGeometricSquaredEigenvalue period hPeriod) = 0

def programPPrimitiveSpinCGeometricSpectralCertificate4D :
    ProgramPPrimitiveSpinCGeometricSpectralCertificate4D
      period hPeriod where
  modeDecomposition :=
    primitiveSpinCGeometricFullModeEquiv period hPeriod
  positiveD10Agreement :=
    programPD10ModeToPrimitiveSpinCGeometricMode_squaredEigenvalue
      period hPeriod
  h2Dense :=
    primitiveSpinCGeometricH2_dense period hPeriod
  selfAdjoint :=
    primitiveSpinCGeometricUnboundedSquared_isSelfAdjoint
      period hPeriod
  fredholmIndexZero :=
    primitiveSpinCGeometricUnboundedSquared_index_zero
      period hPeriod

end
end P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
end JanusFormal
