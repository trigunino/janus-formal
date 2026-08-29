import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFullSpectralSynthesis4D

/-!
# Finite geometric SpinC core and its Hilbert completion

The complete zero-plus-positive family of smooth eigensections is linearly
independent.  Hence its finite synthesis identifies the finite coefficient
space with an actual subspace of smooth geometric sections.  This file puts
the coefficient `ℓ²` norm on that geometric spectral core and proves that
its completion is unitarily the full coefficient Hilbert space.

This is not yet an identification with an independently defined integral
`L²` norm on every smooth section.  It is the canonical Hilbert completion
of the proved geometric eigensection span.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFiniteHilbertCompletion4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFullSpectralSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

local instance finiteHilbertPrimitiveSpinCComplexSMul :
    SMul Complex (SmoothSection period hPeriod) :=
  primitiveSpinCComplexSMul period hPeriod

local instance finiteHilbertPrimitiveSpinCComplexModule :
    Module Complex (SmoothSection period hPeriod) :=
  primitiveSpinCComplexModule period hPeriod

/-- Finite coefficients indexed by the complete geometric spectrum. -/
abbrev PrimitiveSpinCAllModeFiniteCoefficients :=
  PrimitiveSpinCGeometricFullMode →₀ Complex

/-- Insert one coefficient into the complete coefficient Hilbert space. -/
def primitiveSpinCAllModeFiniteL2Block
    (mode : PrimitiveSpinCGeometricFullMode) :
    Complex →ₗ[Complex] PrimitiveSpinCGeometricL2 :=
  (lp.singleContinuousLinearMap Complex
    (fun _ : PrimitiveSpinCGeometricFullMode => Complex) 2 mode).toLinearMap

/-- Canonical inclusion of finite coefficients into the complete
coefficient Hilbert space. -/
def primitiveSpinCAllModeFiniteL2Synthesis :
    PrimitiveSpinCAllModeFiniteCoefficients →ₗ[Complex]
      PrimitiveSpinCGeometricL2 :=
  Finsupp.lsum Complex primitiveSpinCAllModeFiniteL2Block

@[simp]
theorem primitiveSpinCAllModeFiniteL2Synthesis_single
    (mode : PrimitiveSpinCGeometricFullMode)
    (coefficient : Complex) :
    primitiveSpinCAllModeFiniteL2Synthesis
        (Finsupp.single mode coefficient) =
      lp.single 2 mode coefficient := by
  rw [primitiveSpinCAllModeFiniteL2Synthesis, Finsupp.lsum_single]
  rfl

/-- Coordinate evaluation recovers every finite coefficient. -/
@[simp]
theorem primitiveSpinCAllModeFiniteL2Synthesis_apply
    (coefficients : PrimitiveSpinCAllModeFiniteCoefficients)
    (mode : PrimitiveSpinCGeometricFullMode) :
    primitiveSpinCAllModeFiniteL2Synthesis coefficients mode =
      coefficients mode := by
  classical
  induction coefficients using Finsupp.induction with
  | zero =>
      simp
  | single_add source coefficient rest _ _ ih =>
      rw [map_add]
      rw [primitiveSpinCAllModeFiniteL2Synthesis_single]
      change
        (lp.single 2 source coefficient :
          PrimitiveSpinCGeometricL2) mode +
            primitiveSpinCAllModeFiniteL2Synthesis rest mode =
          Finsupp.single source coefficient mode + rest mode
      by_cases hMode : source = mode
      · subst mode
        simp [lp.single_apply, ih]
      · simp [lp.single_apply, hMode, ih]

theorem primitiveSpinCAllModeFiniteL2Synthesis_injective :
    Function.Injective primitiveSpinCAllModeFiniteL2Synthesis := by
  intro first second hEqual
  apply Finsupp.ext
  intro mode
  simpa only [primitiveSpinCAllModeFiniteL2Synthesis_apply] using
    congrArg (fun state : PrimitiveSpinCGeometricL2 => state mode) hEqual

/-- Finite packets are dense in the complete coefficient Hilbert space. -/
theorem primitiveSpinCAllModeFiniteL2Synthesis_denseRange :
    DenseRange primitiveSpinCAllModeFiniteL2Synthesis := by
  change Dense (Set.range primitiveSpinCAllModeFiniteL2Synthesis)
  rw [← LinearMap.coe_range,
    Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  calc
    (⊤ : Submodule Complex PrimitiveSpinCGeometricL2) =
        (Submodule.span Complex
          (Set.range
            (complexDiagonalBasis
              PrimitiveSpinCGeometricFullMode))).topologicalClosure :=
      (HilbertBasis.dense_span
        (complexDiagonalBasis
          PrimitiveSpinCGeometricFullMode)).symm
    _ ≤
        (LinearMap.range
          primitiveSpinCAllModeFiniteL2Synthesis).topologicalClosure :=
      Submodule.topologicalClosure_mono
        (Submodule.span_le.mpr (by
          rintro state ⟨mode, rfl⟩
          refine ⟨Finsupp.single mode 1, ?_⟩
          rw [primitiveSpinCAllModeFiniteL2Synthesis_single]
          exact
            (complexDiagonalBasis_eq_single
              PrimitiveSpinCGeometricFullMode mode).symm))

/-! ## The actual finite geometric eigensection span -/

/-- Actual smooth geometric subspace spanned by all proved eigensections. -/
abbrev PrimitiveSpinCAllModeFiniteGeometricSpan :=
  LinearMap.range
    (primitiveSpinCAllModeNullHarmonicSynthesis period hPeriod)

/-- Finite coefficients are exactly the actual geometric spectral span. -/
def primitiveSpinCAllModeFiniteGeometricSynthesisEquiv :
    PrimitiveSpinCAllModeFiniteCoefficients ≃ₗ[Complex]
      PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod :=
  LinearEquiv.ofInjective
    (primitiveSpinCAllModeNullHarmonicSynthesis period hPeriod)
    (primitiveSpinCAllModeNullHarmonicSynthesis_injective
      period hPeriod)

@[simp]
theorem primitiveSpinCAllModeFiniteGeometricSynthesisEquiv_coe
    (coefficients : PrimitiveSpinCAllModeFiniteCoefficients) :
    ((primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
          period hPeriod coefficients :
        PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod) :
      SmoothSection period hPeriod) =
      primitiveSpinCAllModeNullHarmonicSynthesis
        period hPeriod coefficients :=
  rfl

/-- Fourier analysis on the actual finite geometric spectral span. -/
def primitiveSpinCAllModeFiniteGeometricAnalysis :
    PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod →ₗ[Complex]
      PrimitiveSpinCGeometricL2 :=
  primitiveSpinCAllModeFiniteL2Synthesis.comp
    (primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
      period hPeriod).symm.toLinearMap

@[simp]
theorem primitiveSpinCAllModeFiniteGeometricAnalysis_synthesis
    (coefficients : PrimitiveSpinCAllModeFiniteCoefficients) :
    primitiveSpinCAllModeFiniteGeometricAnalysis period hPeriod
        (primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
          period hPeriod coefficients) =
      primitiveSpinCAllModeFiniteL2Synthesis coefficients := by
  simp [primitiveSpinCAllModeFiniteGeometricAnalysis]

theorem primitiveSpinCAllModeFiniteGeometricAnalysis_injective :
    Function.Injective
      (primitiveSpinCAllModeFiniteGeometricAnalysis period hPeriod) :=
  primitiveSpinCAllModeFiniteL2Synthesis_injective.comp
    (primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
      period hPeriod).symm.injective

theorem primitiveSpinCAllModeFiniteGeometricAnalysis_denseRange :
    DenseRange
      (primitiveSpinCAllModeFiniteGeometricAnalysis period hPeriod) := by
  rw [DenseRange]
  have hRange :
      Set.range
          (primitiveSpinCAllModeFiniteGeometricAnalysis period hPeriod) =
        Set.range primitiveSpinCAllModeFiniteL2Synthesis := by
    ext state
    constructor
    · rintro ⟨geometricState, rfl⟩
      exact
        ⟨(primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
            period hPeriod).symm geometricState, rfl⟩
    · rintro ⟨coefficients, rfl⟩
      exact
        ⟨primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
            period hPeriod coefficients,
          primitiveSpinCAllModeFiniteGeometricAnalysis_synthesis
            period hPeriod coefficients⟩
  rw [hRange]
  exact primitiveSpinCAllModeFiniteL2Synthesis_denseRange

/-- Actual smooth eigensection as an element of the finite geometric
spectral span. -/
def primitiveSpinCAllModeFiniteGeometricVector
    (mode : PrimitiveSpinCGeometricFullMode) :
    PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod :=
  primitiveSpinCAllModeFiniteGeometricSynthesisEquiv period hPeriod
    (Finsupp.single mode 1)

@[simp]
theorem primitiveSpinCAllModeFiniteGeometricVector_coe
    (mode : PrimitiveSpinCGeometricFullMode) :
    ((primitiveSpinCAllModeFiniteGeometricVector
          period hPeriod mode :
        PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod) :
      SmoothSection period hPeriod) =
      primitiveSpinCAllModeNullHarmonicRealSection
        period hPeriod mode := by
  rw [primitiveSpinCAllModeFiniteGeometricVector,
    primitiveSpinCAllModeFiniteGeometricSynthesisEquiv_coe,
    primitiveSpinCAllModeNullHarmonicSynthesis_single]
  simp

@[simp]
theorem primitiveSpinCAllModeFiniteGeometricAnalysis_vector
    (mode : PrimitiveSpinCGeometricFullMode) :
    primitiveSpinCAllModeFiniteGeometricAnalysis period hPeriod
        (primitiveSpinCAllModeFiniteGeometricVector
          period hPeriod mode) =
      lp.single 2 mode 1 := by
  rw [primitiveSpinCAllModeFiniteGeometricVector,
    primitiveSpinCAllModeFiniteGeometricAnalysis_synthesis,
    primitiveSpinCAllModeFiniteL2Synthesis_single]

/-! ## Exact squared-Dirac conjugacy on the finite geometric core -/

/-- Squared Dirac transported to the actual finite geometric span. -/
def primitiveSpinCAllModeFiniteGeometricSquaredOperator :
    PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod →ₗ[Complex]
      PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod :=
  (primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
      period hPeriod).toLinearMap.comp
    ((primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator
        period hPeriod).comp
      (primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
        period hPeriod).symm.toLinearMap)

@[simp]
theorem primitiveSpinCAllModeFiniteGeometricSquaredOperator_synthesis
    (coefficients : PrimitiveSpinCAllModeFiniteCoefficients) :
    primitiveSpinCAllModeFiniteGeometricSquaredOperator period hPeriod
        (primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
          period hPeriod coefficients) =
      primitiveSpinCAllModeFiniteGeometricSynthesisEquiv period hPeriod
        (primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator
          period hPeriod coefficients) := by
  simp [primitiveSpinCAllModeFiniteGeometricSquaredOperator]

/-- The transported operator is literally the genuine differential
squared Dirac operator on every state of the finite geometric span. -/
theorem primitiveSpinCAllModeFiniteGeometricSquaredOperator_coe
    (state :
      PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod) :
    ((primitiveSpinCAllModeFiniteGeometricSquaredOperator
          period hPeriod state :
        PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod) :
      SmoothSection period hPeriod) =
      primitiveSpinCGeometricDiracSquaredComplexLinearMap
        period hPeriod (state : SmoothSection period hPeriod) := by
  let coefficients :=
    (primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
      period hPeriod).symm state
  have hState :
      state =
        primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
          period hPeriod coefficients :=
    (primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
      period hPeriod).apply_symm_apply state |>.symm
  rw [hState,
    primitiveSpinCAllModeFiniteGeometricSquaredOperator_synthesis,
    primitiveSpinCAllModeFiniteGeometricSynthesisEquiv_coe,
    primitiveSpinCAllModeFiniteGeometricSynthesisEquiv_coe,
    primitiveSpinCAllModeNullHarmonicSynthesis_intertwines_dirac_sq]

@[simp]
theorem primitiveSpinCAllModeFiniteGeometricAnalysis_squaredOperator
    (state :
      PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod) :
    primitiveSpinCAllModeFiniteGeometricAnalysis period hPeriod
        (primitiveSpinCAllModeFiniteGeometricSquaredOperator
          period hPeriod state) =
      primitiveSpinCAllModeFiniteL2Synthesis
        (primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator
          period hPeriod
          ((primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
            period hPeriod).symm state)) := by
  rw [show state =
      primitiveSpinCAllModeFiniteGeometricSynthesisEquiv period hPeriod
        ((primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
          period hPeriod).symm state) by
      exact
        (primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
          period hPeriod).apply_symm_apply state |>.symm,
    primitiveSpinCAllModeFiniteGeometricSquaredOperator_synthesis,
    primitiveSpinCAllModeFiniteGeometricAnalysis_synthesis]
  simp

/-! ## Entry into the maximal coefficient domain -/

/-- A complete coefficient basis vector with its canonical maximal-domain
membership. -/
def primitiveSpinCAllModeFiniteH2Basis
    (mode : PrimitiveSpinCGeometricFullMode) :
    (primitiveSpinCGeometricUnboundedSquared period hPeriod).domain :=
  ⟨complexDiagonalBasis PrimitiveSpinCGeometricFullMode mode,
    complexDiagonalBasis_mem_domain
      PrimitiveSpinCGeometricFullMode
      (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)
      mode⟩

@[simp]
theorem primitiveSpinCAllModeFiniteH2Basis_coe
    (mode : PrimitiveSpinCGeometricFullMode) :
    ((primitiveSpinCAllModeFiniteH2Basis period hPeriod mode :
        (primitiveSpinCGeometricUnboundedSquared
          period hPeriod).domain) :
      PrimitiveSpinCGeometricL2) =
      lp.single 2 mode 1 :=
  complexDiagonalBasis_eq_single
    PrimitiveSpinCGeometricFullMode mode

def primitiveSpinCAllModeFiniteH2Block
    (mode : PrimitiveSpinCGeometricFullMode) :
    Complex →ₗ[Complex]
      (primitiveSpinCGeometricUnboundedSquared period hPeriod).domain :=
  LinearMap.toSpanSingleton Complex
    (primitiveSpinCGeometricUnboundedSquared period hPeriod).domain
    (primitiveSpinCAllModeFiniteH2Basis period hPeriod mode)

/-- Every finite full-spectrum packet lies canonically in the maximal
coefficient `H²` domain. -/
def primitiveSpinCAllModeFiniteH2Synthesis :
    PrimitiveSpinCAllModeFiniteCoefficients →ₗ[Complex]
      (primitiveSpinCGeometricUnboundedSquared period hPeriod).domain :=
  Finsupp.lsum Complex fun mode =>
    primitiveSpinCAllModeFiniteH2Block period hPeriod mode

@[simp]
theorem primitiveSpinCAllModeFiniteH2Synthesis_single
    (mode : PrimitiveSpinCGeometricFullMode)
    (coefficient : Complex) :
    primitiveSpinCAllModeFiniteH2Synthesis period hPeriod
        (Finsupp.single mode coefficient) =
      coefficient •
        primitiveSpinCAllModeFiniteH2Basis period hPeriod mode := by
  rw [primitiveSpinCAllModeFiniteH2Synthesis, Finsupp.lsum_single]
  simp [primitiveSpinCAllModeFiniteH2Block]

theorem primitiveSpinCAllModeFiniteH2Synthesis_coe
    (coefficients : PrimitiveSpinCAllModeFiniteCoefficients) :
    ((primitiveSpinCAllModeFiniteH2Synthesis
          period hPeriod coefficients :
        (primitiveSpinCGeometricUnboundedSquared
          period hPeriod).domain) :
      PrimitiveSpinCGeometricL2) =
      primitiveSpinCAllModeFiniteL2Synthesis coefficients := by
  let inclusion :
      (primitiveSpinCGeometricUnboundedSquared
          period hPeriod).domain →ₗ[Complex]
        PrimitiveSpinCGeometricL2 :=
    (primitiveSpinCGeometricUnboundedSquared
      period hPeriod).domain.subtype
  have hMaps :
      inclusion.comp
          (primitiveSpinCAllModeFiniteH2Synthesis period hPeriod) =
        primitiveSpinCAllModeFiniteL2Synthesis := by
    apply Finsupp.lhom_ext
    intro mode coefficient
    rw [LinearMap.comp_apply,
      primitiveSpinCAllModeFiniteH2Synthesis_single,
      primitiveSpinCAllModeFiniteL2Synthesis_single]
    change coefficient •
        (complexDiagonalBasis PrimitiveSpinCGeometricFullMode mode) =
      lp.single 2 mode coefficient
    rw [complexDiagonalBasis_eq_single]
    simp only [← lp.single_smul, smul_eq_mul, mul_one]
  exact LinearMap.congr_fun hMaps coefficients

/-- The maximal diagonal operator restricted to finite full-spectrum
coefficients. -/
def primitiveSpinCAllModeFiniteMaximalSquared :
    PrimitiveSpinCAllModeFiniteCoefficients →ₗ[Complex]
      PrimitiveSpinCGeometricL2 :=
  (primitiveSpinCGeometricUnboundedSquared period hPeriod).toFun.comp
    (primitiveSpinCAllModeFiniteH2Synthesis period hPeriod)

@[simp]
theorem primitiveSpinCAllModeFiniteMaximalSquared_single
    (mode : PrimitiveSpinCGeometricFullMode)
    (coefficient : Complex) :
    primitiveSpinCAllModeFiniteMaximalSquared period hPeriod
        (Finsupp.single mode coefficient) =
      ((primitiveSpinCGeometricSquaredEigenvalue
          period hPeriod mode : Real) : Complex) •
        lp.single 2 mode coefficient := by
  rw [primitiveSpinCAllModeFiniteMaximalSquared,
    LinearMap.comp_apply,
    primitiveSpinCAllModeFiniteH2Synthesis_single,
    map_smul]
  change coefficient •
      complexDiagonalOperator PrimitiveSpinCGeometricFullMode
        (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)
        ⟨complexDiagonalBasis PrimitiveSpinCGeometricFullMode mode,
          complexDiagonalBasis_mem_domain
            PrimitiveSpinCGeometricFullMode
            (primitiveSpinCGeometricSquaredEigenvalue period hPeriod)
            mode⟩ =
    ((primitiveSpinCGeometricSquaredEigenvalue
        period hPeriod mode : Real) : Complex) •
      lp.single 2 mode coefficient
  rw [complexDiagonalOperator_on_basis]
  change coefficient •
      (((primitiveSpinCGeometricSquaredEigenvalue
          period hPeriod mode : Real) : Complex) •
        complexDiagonalBasis PrimitiveSpinCGeometricFullMode mode) =
    ((primitiveSpinCGeometricSquaredEigenvalue
        period hPeriod mode : Real) : Complex) •
      lp.single 2 mode coefficient
  rw [complexDiagonalBasis_eq_single]
  simp only [← lp.single_smul, smul_eq_mul, mul_one]
  congr 1
  ring

/-- Exact agreement between the maximal coefficient operator and the
finite diagonal multiplier. -/
theorem primitiveSpinCAllModeFiniteMaximalSquared_intertwines
    (coefficients : PrimitiveSpinCAllModeFiniteCoefficients) :
    primitiveSpinCAllModeFiniteMaximalSquared
        period hPeriod coefficients =
      primitiveSpinCAllModeFiniteL2Synthesis
        (primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator
          period hPeriod coefficients) := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp
  | single_add mode coefficient rest _ _ ih =>
      rw [map_add, map_add, map_add, ih,
        primitiveSpinCAllModeFiniteMaximalSquared_single,
        primitiveSpinCAllModeNullHarmonicSquaredCoefficientOperator_single,
        map_smul,
        primitiveSpinCAllModeFiniteL2Synthesis_single]

/-- Every actual finite geometric state has a canonical representative in
the maximal coefficient domain. -/
def primitiveSpinCAllModeFiniteGeometricH2Analysis
    (state :
      PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod) :
    (primitiveSpinCGeometricUnboundedSquared period hPeriod).domain :=
  primitiveSpinCAllModeFiniteH2Synthesis period hPeriod
    ((primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
      period hPeriod).symm state)

theorem primitiveSpinCAllModeFiniteGeometricH2Analysis_coe
    (state :
      PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod) :
    ((primitiveSpinCAllModeFiniteGeometricH2Analysis
          period hPeriod state :
        (primitiveSpinCGeometricUnboundedSquared
          period hPeriod).domain) :
      PrimitiveSpinCGeometricL2) =
      primitiveSpinCAllModeFiniteGeometricAnalysis
        period hPeriod state := by
  rw [primitiveSpinCAllModeFiniteGeometricH2Analysis,
    primitiveSpinCAllModeFiniteH2Synthesis_coe]
  rfl

/-- The genuine geometric differential operator and the maximal
coefficient realization are exactly conjugate on the whole proved finite
spectral core. -/
theorem primitiveSpinCAllModeFiniteGeometric_maximal_conjugacy
    (state :
      PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod) :
    primitiveSpinCGeometricUnboundedSquared period hPeriod
        (primitiveSpinCAllModeFiniteGeometricH2Analysis
          period hPeriod state) =
      primitiveSpinCAllModeFiniteGeometricAnalysis period hPeriod
        (primitiveSpinCAllModeFiniteGeometricSquaredOperator
          period hPeriod state) := by
  change
    primitiveSpinCAllModeFiniteMaximalSquared period hPeriod
        ((primitiveSpinCAllModeFiniteGeometricSynthesisEquiv
          period hPeriod).symm state) =
      primitiveSpinCAllModeFiniteGeometricAnalysis period hPeriod
        (primitiveSpinCAllModeFiniteGeometricSquaredOperator
          period hPeriod state)
  rw [
    primitiveSpinCAllModeFiniteMaximalSquared_intertwines,
    primitiveSpinCAllModeFiniteGeometricAnalysis_squaredOperator]

/-! ## Intrinsic spectral norm and completion -/

/-- A type synonym carrying the coefficient-induced Hilbert norm on the
actual geometric finite span. -/
def PrimitiveSpinCAllModeFiniteHilbertCore :=
  PrimitiveSpinCAllModeFiniteGeometricSpan period hPeriod

/-- Coefficient analysis on the normed geometric finite core. -/
def primitiveSpinCAllModeFiniteHilbertCoreAnalysis :
    PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod →ₗ[Complex]
      PrimitiveSpinCGeometricL2 :=
  primitiveSpinCAllModeFiniteGeometricAnalysis period hPeriod

/-- Squared Dirac on the normed finite geometric core. -/
def primitiveSpinCAllModeFiniteHilbertCoreSquaredOperator :
    PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod →ₗ[Complex]
      PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod :=
  primitiveSpinCAllModeFiniteGeometricSquaredOperator period hPeriod

theorem primitiveSpinCAllModeFiniteHilbertCoreAnalysis_injective :
    Function.Injective
      (primitiveSpinCAllModeFiniteHilbertCoreAnalysis period hPeriod) :=
  primitiveSpinCAllModeFiniteGeometricAnalysis_injective period hPeriod

noncomputable instance primitiveSpinCAllModeFiniteHilbertCoreNormed :
    NormedAddCommGroup
      (PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod) :=
  NormedAddCommGroup.induced
    (PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod)
    PrimitiveSpinCGeometricL2
    (primitiveSpinCAllModeFiniteHilbertCoreAnalysis period hPeriod)
    (primitiveSpinCAllModeFiniteHilbertCoreAnalysis_injective
      period hPeriod)

noncomputable instance primitiveSpinCAllModeFiniteHilbertCoreNormedSpace :
    NormedSpace Complex
      (PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod) :=
  NormedSpace.induced Complex
    (PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod)
    PrimitiveSpinCGeometricL2
    (primitiveSpinCAllModeFiniteHilbertCoreAnalysis period hPeriod)

noncomputable instance primitiveSpinCAllModeFiniteHilbertCoreInner :
    InnerProductSpace Complex
      (PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod) :=
  InnerProductSpace.induced
    (primitiveSpinCAllModeFiniteHilbertCoreAnalysis period hPeriod)

@[simp]
theorem primitiveSpinCAllModeFiniteHilbertCoreAnalysis_norm
    (state : PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod) :
    ‖primitiveSpinCAllModeFiniteHilbertCoreAnalysis
        period hPeriod state‖ = ‖state‖ :=
  rfl

/-- The coefficient analysis is an isometric dense embedding. -/
def primitiveSpinCAllModeFiniteHilbertCoreIsometry :
    PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod →ₗᵢ[Complex]
      PrimitiveSpinCGeometricL2 where
  toLinearMap :=
    primitiveSpinCAllModeFiniteHilbertCoreAnalysis period hPeriod
  norm_map' :=
    primitiveSpinCAllModeFiniteHilbertCoreAnalysis_norm period hPeriod

theorem primitiveSpinCAllModeFiniteHilbertCoreIsometry_denseRange :
    DenseRange
      (primitiveSpinCAllModeFiniteHilbertCoreIsometry
        period hPeriod) :=
  primitiveSpinCAllModeFiniteGeometricAnalysis_denseRange period hPeriod

/-- Completion of the actual finite geometric spectral span in its
coefficient-induced norm. -/
abbrev PrimitiveSpinCAllModeGeometricHilbertCompletion :=
  UniformSpace.Completion
    (PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod)

/-- Canonical inclusion of the finite geometric core into its
completion. -/
def primitiveSpinCAllModeFiniteHilbertCoreInclusion :
    PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod →ₗ[Complex]
      PrimitiveSpinCAllModeGeometricHilbertCompletion period hPeriod :=
  (UniformSpace.Completion.toComplₗᵢ
    (𝕜 := Complex)
    (E := PrimitiveSpinCAllModeFiniteHilbertCore
      period hPeriod)).toLinearMap

/-- The completion of the proved geometric eigensection span is
canonically unitary to the complete coefficient `ℓ²` space. -/
def primitiveSpinCAllModeGeometricHilbertCompletionEquiv :
    PrimitiveSpinCAllModeGeometricHilbertCompletion
        period hPeriod ≃ₗᵢ[Complex]
      PrimitiveSpinCGeometricL2 :=
  LinearEquiv.extendOfIsometry
    (E := PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod)
    (F := PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod)
    (LinearEquiv.refl Complex
      (PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod))
    (primitiveSpinCAllModeFiniteHilbertCoreInclusion
      period hPeriod)
    (primitiveSpinCAllModeFiniteHilbertCoreIsometry
      period hPeriod).toLinearMap
    UniformSpace.Completion.denseRange_coe
    (primitiveSpinCAllModeFiniteHilbertCoreIsometry_denseRange
      period hPeriod)
    (by
      intro state
      change
        ‖primitiveSpinCAllModeFiniteHilbertCoreAnalysis
            period hPeriod state‖ =
          ‖(state :
            PrimitiveSpinCAllModeGeometricHilbertCompletion
              period hPeriod)‖
      simp)

@[simp]
theorem primitiveSpinCAllModeGeometricHilbertCompletionEquiv_core
    (state : PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod) :
    primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod
        (state :
          PrimitiveSpinCAllModeGeometricHilbertCompletion
            period hPeriod) =
      primitiveSpinCAllModeFiniteHilbertCoreAnalysis
        period hPeriod state := by
  change
    primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod
        (primitiveSpinCAllModeFiniteHilbertCoreInclusion
          period hPeriod state) =
      (primitiveSpinCAllModeFiniteHilbertCoreIsometry
        period hPeriod).toLinearMap state
  unfold primitiveSpinCAllModeGeometricHilbertCompletionEquiv
  rw [LinearEquiv.extendOfIsometry_eq]
  rfl

/-! ## Maximal operator on the completed geometric spectral core -/

/-- Pullback of the maximal coefficient `H²` domain to the completed
geometric spectral core. -/
def primitiveSpinCAllModeGeometricCompletedH2 :
    Submodule Complex
      (PrimitiveSpinCAllModeGeometricHilbertCompletion
        period hPeriod) :=
  (PrimitiveSpinCGeometricH2 period hPeriod).comap
    (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
      period hPeriod).toLinearMap

/-- The completed geometric domain is unitarily the maximal coefficient
domain. -/
def primitiveSpinCAllModeGeometricCompletedH2Equiv :
    primitiveSpinCAllModeGeometricCompletedH2
        period hPeriod ≃ₗᵢ[Complex]
      PrimitiveSpinCGeometricH2 period hPeriod where
  toFun state :=
    ⟨primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod state.1, state.2⟩
  invFun state :=
    ⟨(primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod).symm state.1, by
      simpa [primitiveSpinCAllModeGeometricCompletedH2] using state.2⟩
  left_inv state := by
    apply Subtype.ext
    exact
      (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod).symm_apply_apply state.1
  right_inv state := by
    apply Subtype.ext
    exact
      (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod).apply_symm_apply state.1
  map_add' first second := by
    apply Subtype.ext
    exact map_add
      (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod) first.1 second.1
  map_smul' scalar state := by
    apply Subtype.ext
    exact map_smul
      (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod) scalar state.1
  norm_map' state :=
    (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
      period hPeriod).norm_map state.1

/-- Squared Dirac on the completed geometric spectral core. -/
def primitiveSpinCAllModeGeometricCompletedSquaredOperator :
    primitiveSpinCAllModeGeometricCompletedH2
        period hPeriod →ₗ[Complex]
      PrimitiveSpinCAllModeGeometricHilbertCompletion
        period hPeriod :=
  (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
      period hPeriod).symm.toLinearMap.comp
    ((primitiveSpinCGeometricUnboundedSquared
        period hPeriod).toFun.comp
      (primitiveSpinCAllModeGeometricCompletedH2Equiv
        period hPeriod).toLinearMap)

/-- Exact unitary conjugacy with the maximal coefficient operator. -/
theorem
    primitiveSpinCAllModeGeometricCompletionEquiv_completedSquaredOperator
    (state :
      primitiveSpinCAllModeGeometricCompletedH2 period hPeriod) :
    primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod
        (primitiveSpinCAllModeGeometricCompletedSquaredOperator
          period hPeriod state) =
      primitiveSpinCGeometricUnboundedSquared period hPeriod
        (primitiveSpinCAllModeGeometricCompletedH2Equiv
          period hPeriod state) :=
  (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
    period hPeriod).apply_symm_apply _

/-- Every finite geometric spectral state belongs to the transported
maximal domain. -/
theorem primitiveSpinCAllModeFiniteHilbertCore_mem_completedH2
    (state : PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod) :
    (state :
      PrimitiveSpinCAllModeGeometricHilbertCompletion period hPeriod) ∈
        primitiveSpinCAllModeGeometricCompletedH2
          period hPeriod := by
  change
    primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod
        (state :
          PrimitiveSpinCAllModeGeometricHilbertCompletion
            period hPeriod) ∈
      PrimitiveSpinCGeometricH2 period hPeriod
  rw [primitiveSpinCAllModeGeometricHilbertCompletionEquiv_core,
    primitiveSpinCAllModeFiniteHilbertCoreAnalysis]
  change
    primitiveSpinCAllModeFiniteGeometricAnalysis period hPeriod
        (show PrimitiveSpinCAllModeFiniteGeometricSpan
          period hPeriod from state) ∈
      PrimitiveSpinCGeometricH2 period hPeriod
  rw [← primitiveSpinCAllModeFiniteGeometricH2Analysis_coe
      period hPeriod
      (show PrimitiveSpinCAllModeFiniteGeometricSpan
        period hPeriod from state)]
  exact
    (primitiveSpinCAllModeFiniteGeometricH2Analysis
      period hPeriod
      (show PrimitiveSpinCAllModeFiniteGeometricSpan
        period hPeriod from state)).property

theorem primitiveSpinCAllModeGeometricCompletedH2Equiv_core
    (state : PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod) :
    primitiveSpinCAllModeGeometricCompletedH2Equiv period hPeriod
        ⟨(state :
            PrimitiveSpinCAllModeGeometricHilbertCompletion
              period hPeriod),
          primitiveSpinCAllModeFiniteHilbertCore_mem_completedH2
            period hPeriod state⟩ =
      primitiveSpinCAllModeFiniteGeometricH2Analysis
        period hPeriod
        (show PrimitiveSpinCAllModeFiniteGeometricSpan
          period hPeriod from state) := by
  apply Subtype.ext
  change
    primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod
        (state :
          PrimitiveSpinCAllModeGeometricHilbertCompletion
            period hPeriod) =
      ((primitiveSpinCAllModeFiniteGeometricH2Analysis
          period hPeriod
          (show PrimitiveSpinCAllModeFiniteGeometricSpan
            period hPeriod from state) :
        PrimitiveSpinCGeometricH2 period hPeriod) :
          PrimitiveSpinCGeometricL2)
  rw [primitiveSpinCAllModeGeometricHilbertCompletionEquiv_core,
    primitiveSpinCAllModeFiniteHilbertCoreAnalysis,
    primitiveSpinCAllModeFiniteGeometricH2Analysis_coe]
  rfl

/-- The completed operator restricts exactly to the genuine differential
squared Dirac on every proved finite geometric spectral state. -/
theorem primitiveSpinCAllModeGeometricCompletedSquaredOperator_core
    (state : PrimitiveSpinCAllModeFiniteHilbertCore period hPeriod) :
    primitiveSpinCAllModeGeometricCompletedSquaredOperator
        period hPeriod
        ⟨(state :
            PrimitiveSpinCAllModeGeometricHilbertCompletion
              period hPeriod),
          primitiveSpinCAllModeFiniteHilbertCore_mem_completedH2
            period hPeriod state⟩ =
      (primitiveSpinCAllModeFiniteHilbertCoreSquaredOperator
          period hPeriod state :
        PrimitiveSpinCAllModeGeometricHilbertCompletion
          period hPeriod) := by
  apply
    (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
      period hPeriod).injective
  rw [
    primitiveSpinCAllModeGeometricCompletionEquiv_completedSquaredOperator,
    primitiveSpinCAllModeGeometricCompletedH2Equiv_core,
    primitiveSpinCAllModeGeometricHilbertCompletionEquiv_core]
  exact
    primitiveSpinCAllModeFiniteGeometric_maximal_conjugacy
      period hPeriod
      (show PrimitiveSpinCAllModeFiniteGeometricSpan
        period hPeriod from state)

/-- The completed geometric operator inherits the exact spectral-gap
coercivity estimate. -/
theorem primitiveSpinCAllModeGeometricCompletedSquaredOperator_coercive
    (state :
      primitiveSpinCAllModeGeometricCompletedH2 period hPeriod) :
    ‖(state :
        PrimitiveSpinCAllModeGeometricHilbertCompletion
          period hPeriod)‖ ≤
      (primitiveSpinCGeometricSpectralGap period)⁻¹ *
        ‖primitiveSpinCAllModeGeometricCompletedSquaredOperator
          period hPeriod state‖ := by
  have hOperatorNorm :
      ‖primitiveSpinCAllModeGeometricCompletedSquaredOperator
          period hPeriod state‖ =
        ‖primitiveSpinCGeometricUnboundedSquared period hPeriod
          (primitiveSpinCAllModeGeometricCompletedH2Equiv
            period hPeriod state)‖ := by
    rw [
      ←
        primitiveSpinCAllModeGeometricCompletionEquiv_completedSquaredOperator,
      (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod).norm_map]
  calc
    ‖(state :
        PrimitiveSpinCAllModeGeometricHilbertCompletion
          period hPeriod)‖ =
        ‖((primitiveSpinCAllModeGeometricCompletedH2Equiv
              period hPeriod state :
            PrimitiveSpinCGeometricH2 period hPeriod) :
          PrimitiveSpinCGeometricL2)‖ := by
      exact
        (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
          period hPeriod).norm_map state.1 |>.symm
    _ ≤
        (primitiveSpinCGeometricSpectralGap period)⁻¹ *
          ‖primitiveSpinCGeometricUnboundedSquared period hPeriod
            (primitiveSpinCAllModeGeometricCompletedH2Equiv
              period hPeriod state)‖ :=
      primitiveSpinCGeometricUnboundedSquared_coercive
        period hPeriod
        (primitiveSpinCAllModeGeometricCompletedH2Equiv
          period hPeriod state)
    _ =
        (primitiveSpinCGeometricSpectralGap period)⁻¹ *
          ‖primitiveSpinCAllModeGeometricCompletedSquaredOperator
            period hPeriod state‖ := by
      rw [hOperatorNorm]

/-- The completed geometric squared operator is bijective. -/
theorem primitiveSpinCAllModeGeometricCompletedSquaredOperator_bijective :
    Function.Bijective
      (primitiveSpinCAllModeGeometricCompletedSquaredOperator
        period hPeriod) := by
  constructor
  · intro first second hEqual
    apply
      (primitiveSpinCAllModeGeometricCompletedH2Equiv
        period hPeriod).injective
    apply
      (primitiveSpinCGeometricUnboundedSquared_bijective
        period hPeriod).1
    have hImages :=
      congrArg
        (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
          period hPeriod) hEqual
    simpa only
      [primitiveSpinCAllModeGeometricCompletionEquiv_completedSquaredOperator]
      using hImages
  · intro output
    obtain ⟨coefficientState, hCoefficientState⟩ :=
      (primitiveSpinCGeometricUnboundedSquared_bijective
        period hPeriod).2
        (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
          period hPeriod output)
    refine
      ⟨(primitiveSpinCAllModeGeometricCompletedH2Equiv
          period hPeriod).symm coefficientState, ?_⟩
    apply
      (primitiveSpinCAllModeGeometricHilbertCompletionEquiv
        period hPeriod).injective
    rw [
      primitiveSpinCAllModeGeometricCompletionEquiv_completedSquaredOperator,
      (primitiveSpinCAllModeGeometricCompletedH2Equiv
        period hPeriod).apply_symm_apply,
      hCoefficientState]

/-- Proof-carrying closure of the finite geometric spectral completion. -/
structure PrimitiveSpinCAllModeFiniteHilbertCompletionCertificate4D :
    Prop where
  finiteAnalysisInjective :
    Function.Injective
      (primitiveSpinCAllModeFiniteGeometricAnalysis period hPeriod)
  finiteAnalysisDense :
    DenseRange
      (primitiveSpinCAllModeFiniteGeometricAnalysis period hPeriod)
  completionUnitary :
    Nonempty
      (PrimitiveSpinCAllModeGeometricHilbertCompletion
          period hPeriod ≃ₗᵢ[Complex]
        PrimitiveSpinCGeometricL2)
  completedMaximalConjugacy :
    ∀ state :
        primitiveSpinCAllModeGeometricCompletedH2 period hPeriod,
      primitiveSpinCAllModeGeometricHilbertCompletionEquiv
          period hPeriod
          (primitiveSpinCAllModeGeometricCompletedSquaredOperator
            period hPeriod state) =
        primitiveSpinCGeometricUnboundedSquared period hPeriod
          (primitiveSpinCAllModeGeometricCompletedH2Equiv
            period hPeriod state)
  completedCoercive :
    ∀ state :
        primitiveSpinCAllModeGeometricCompletedH2 period hPeriod,
      ‖(state :
          PrimitiveSpinCAllModeGeometricHilbertCompletion
            period hPeriod)‖ ≤
        (primitiveSpinCGeometricSpectralGap period)⁻¹ *
          ‖primitiveSpinCAllModeGeometricCompletedSquaredOperator
            period hPeriod state‖
  completedBijective :
    Function.Bijective
      (primitiveSpinCAllModeGeometricCompletedSquaredOperator
        period hPeriod)

def primitiveSpinCAllModeFiniteHilbertCompletionCertificate4D :
    PrimitiveSpinCAllModeFiniteHilbertCompletionCertificate4D
      period hPeriod where
  finiteAnalysisInjective :=
    primitiveSpinCAllModeFiniteGeometricAnalysis_injective
      period hPeriod
  finiteAnalysisDense :=
    primitiveSpinCAllModeFiniteGeometricAnalysis_denseRange
      period hPeriod
  completionUnitary :=
    ⟨primitiveSpinCAllModeGeometricHilbertCompletionEquiv
      period hPeriod⟩
  completedMaximalConjugacy :=
    primitiveSpinCAllModeGeometricCompletionEquiv_completedSquaredOperator
      period hPeriod
  completedCoercive :=
    primitiveSpinCAllModeGeometricCompletedSquaredOperator_coercive
      period hPeriod
  completedBijective :=
    primitiveSpinCAllModeGeometricCompletedSquaredOperator_bijective
      period hPeriod

theorem primitiveSpinCAllModeFiniteHilbertCompletion_gate :
    Nonempty
      (PrimitiveSpinCAllModeFiniteHilbertCompletionCertificate4D
        period hPeriod) :=
  ⟨primitiveSpinCAllModeFiniteHilbertCompletionCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFiniteHilbertCompletion4D
end JanusFormal
