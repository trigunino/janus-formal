import Mathlib

/-!
# A concrete finite-mode Fredholm and determinant-line family

This gate constructs the symmetric finite Fourier cutoff of a complex Dirac
family.  For every cutoff it proves finite-dimensional Fredholmness, index
zero, holomorphic dependence on the holonomy, PT covariance, and constructs
the induced map on the top exterior power (the finite determinant-line
section).  It deliberately does not promote the cutoff family to the global
unbounded Janus operator or to a Quillen/Bismut--Freed package.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteModeFredholmDeterminantLine

set_option autoImplicit false

open scoped ContDiff

noncomputable section

/-- A symmetric cutoff has one positive and one negative mode of each size. -/
abbrev CutoffMode (cutoff : ℕ) := Fin cutoff × Bool

/-- Complex coefficient space of the finite Fourier cutoff. -/
abbrev CutoffSpace (cutoff : ℕ) := CutoffMode cutoff → ℂ

/-- The nonzero signed integer frequency attached to a cutoff mode. -/
def signedFrequency {cutoff : ℕ} : CutoffMode cutoff → ℂ
  | (mode, false) => (mode.val + 1 : ℕ)
  | (mode, true) => -((mode.val + 1 : ℕ) : ℂ)

/-- PT exchanges the positive and negative member of every mode pair. -/
def ptMode {cutoff : ℕ} : CutoffMode cutoff → CutoffMode cutoff
  | (mode, false) => (mode, true)
  | (mode, true) => (mode, false)

@[simp] theorem ptMode_involutive {cutoff : ℕ} (mode : CutoffMode cutoff) :
    ptMode (ptMode mode) = mode := by
  rcases mode with ⟨mode, sign⟩
  cases sign <;> rfl

@[simp] theorem signedFrequency_pt {cutoff : ℕ} (mode : CutoffMode cutoff) :
    signedFrequency (ptMode mode) = -signedFrequency mode := by
  rcases mode with ⟨mode, sign⟩
  cases sign <;> simp [ptMode, signedFrequency]

/-- Eigenvalue of the cutoff Dirac family at complexified holonomy `z`. -/
def cutoffEigenvalue {cutoff : ℕ} (z : ℂ) (mode : CutoffMode cutoff) : ℂ :=
  signedFrequency mode + z

@[simp] theorem cutoffEigenvalue_pt {cutoff : ℕ} (z : ℂ)
    (mode : CutoffMode cutoff) :
    cutoffEigenvalue (-z) mode = -cutoffEigenvalue z (ptMode mode) := by
  simp only [cutoffEigenvalue, signedFrequency_pt]
  ring

/-- The diagonal matrix of the finite Fourier Dirac family. -/
def cutoffDiracMatrix (cutoff : ℕ) (z : ℂ) :
    Matrix (CutoffMode cutoff) (CutoffMode cutoff) ℂ :=
  Matrix.diagonal (cutoffEigenvalue z)

/-- The actual finite-dimensional operator represented by `cutoffDiracMatrix`. -/
def cutoffDirac (cutoff : ℕ) (z : ℂ) :
    Module.End ℂ (CutoffSpace cutoff) :=
  Matrix.toLin' (cutoffDiracMatrix cutoff z)

@[simp] theorem cutoffDirac_apply (cutoff : ℕ) (z : ℂ)
    (vector : CutoffSpace cutoff) (mode : CutoffMode cutoff) :
    cutoffDirac cutoff z vector mode =
      cutoffEigenvalue z mode * vector mode := by
  simp [cutoffDirac, cutoffDiracMatrix, Matrix.toLin'_apply,
    Matrix.mulVec_diagonal]

/-- Linear PT on the cutoff coefficient space. -/
def cutoffPT (cutoff : ℕ) : Module.End ℂ (CutoffSpace cutoff) where
  toFun vector mode := vector (ptMode mode)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cutoffPT_apply (cutoff : ℕ) (vector : CutoffSpace cutoff)
    (mode : CutoffMode cutoff) :
    cutoffPT cutoff vector mode = vector (ptMode mode) := rfl

theorem cutoffPT_involutive (cutoff : ℕ) :
    (cutoffPT cutoff).comp (cutoffPT cutoff) = LinearMap.id := by
  ext vector mode
  simp [LinearMap.comp_apply]

/-- PT conjugates the `z` family to the negative of the `-z` family. -/
theorem cutoffDirac_pt_covariant (cutoff : ℕ) (z : ℂ) :
    (cutoffDirac cutoff (-z)).comp (cutoffPT cutoff) =
      -((cutoffPT cutoff).comp (cutoffDirac cutoff z)) := by
  ext vector mode
  simp [LinearMap.comp_apply]

/-- Every matrix entry depends holomorphically on the complexified holonomy. -/
theorem cutoffDiracMatrix_entry_contDiff (cutoff : ℕ)
    (row column : CutoffMode cutoff) :
    ContDiff ℂ ∞ (fun z : ℂ => cutoffDiracMatrix cutoff z row column) := by
  classical
  by_cases h : row = column
  · subst column
    simp [cutoffDiracMatrix, cutoffEigenvalue]
    fun_prop
  · simp only [cutoffDiracMatrix, Matrix.diagonal_apply_ne _ h]
    exact contDiff_const

/-- Entrywise holomorphy, which is the finite-dimensional smooth-family condition. -/
def MatrixFamilyHolomorphic {index : Type*}
    (family : ℂ → Matrix index index ℂ) : Prop :=
  ∀ row column, ContDiff ℂ ∞ (fun z => family z row column)

theorem cutoffDiracMatrix_holomorphic (cutoff : ℕ) :
    MatrixFamilyHolomorphic (cutoffDiracMatrix cutoff) := by
  exact cutoffDiracMatrix_entry_contDiff cutoff

/-- Algebraic cokernel of a finite cutoff operator. -/
abbrev CutoffCokernel (cutoff : ℕ) (z : ℂ) :=
  CutoffSpace cutoff ⧸ LinearMap.range (cutoffDirac cutoff z)

/-- Each cutoff is genuinely Fredholm in the finite-dimensional algebraic sense. -/
theorem cutoffDirac_kernel_and_cokernel_finite (cutoff : ℕ) (z : ℂ) :
    Module.Finite ℂ (LinearMap.ker (cutoffDirac cutoff z)) ∧
      Module.Finite ℂ (CutoffCokernel cutoff z) := by
  exact ⟨inferInstance, inferInstance⟩

/-- The algebraic Fredholm index of the square cutoff family. -/
def cutoffFredholmIndex (cutoff : ℕ) (z : ℂ) : ℤ :=
  (Module.finrank ℂ (LinearMap.ker (cutoffDirac cutoff z)) : ℤ) -
    (Module.finrank ℂ (CutoffCokernel cutoff z) : ℤ)

/-- Every member of the square finite family has index zero, including zero crossings. -/
theorem cutoffFredholmIndex_zero (cutoff : ℕ) (z : ℂ) :
    cutoffFredholmIndex cutoff z = 0 := by
  have hKernel :=
    LinearMap.finrank_range_add_finrank_ker (cutoffDirac cutoff z)
  have hCokernel :=
    (LinearMap.range (cutoffDirac cutoff z)).finrank_quotient_add_finrank
  have hCokernel' :
      Module.finrank ℂ (CutoffCokernel cutoff z) +
          Module.finrank ℂ (LinearMap.range (cutoffDirac cutoff z)) =
        Module.finrank ℂ (CutoffSpace cutoff) := by
    simpa only [CutoffCokernel] using hCokernel
  have hRanks :
      Module.finrank ℂ (LinearMap.ker (cutoffDirac cutoff z)) =
        Module.finrank ℂ (CutoffCokernel cutoff z) := by
    omega
  simp [cutoffFredholmIndex, hRanks]

/-- Determinant coordinate in the standard Fourier basis. -/
def cutoffDeterminant (cutoff : ℕ) (z : ℂ) : ℂ :=
  LinearMap.det (cutoffDirac cutoff z)

theorem cutoffDeterminant_product (cutoff : ℕ) (z : ℂ) :
    cutoffDeterminant cutoff z =
      ∏ mode : CutoffMode cutoff, cutoffEigenvalue z mode := by
  simp [cutoffDeterminant, cutoffDirac, cutoffDiracMatrix,
    LinearMap.det_toLin', Matrix.det_diagonal]

/-- Pairing positive and negative frequencies gives the even determinant polynomial. -/
theorem cutoffDeterminant_factorization (cutoff : ℕ) (z : ℂ) :
    cutoffDeterminant cutoff z =
      ∏ mode : Fin cutoff,
        (z ^ 2 - (((mode.val + 1 : ℕ) : ℂ) ^ 2)) := by
  rw [cutoffDeterminant_product]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro mode _
  simp [cutoffEigenvalue, signedFrequency]
  ring

/-- The determinant coordinate is holomorphic in holonomy. -/
theorem cutoffDeterminant_contDiff (cutoff : ℕ) :
    ContDiff ℂ ∞ (cutoffDeterminant cutoff) := by
  rw [funext fun z => cutoffDeterminant_product cutoff z]
  apply contDiff_prod
  intro mode _
  exact contDiff_const.add contDiff_id

/-- PT invariance of the paired finite determinant. -/
theorem cutoffDeterminant_pt_invariant (cutoff : ℕ) (z : ℂ) :
    cutoffDeterminant cutoff (-z) = cutoffDeterminant cutoff z := by
  simp only [cutoffDeterminant_factorization]
  congr 1
  funext mode
  ring

/-- No cutoff eigenvalue crosses zero in the unit holonomy disk. -/
theorem cutoffEigenvalue_ne_zero_of_norm_lt_one {cutoff : ℕ} {z : ℂ}
    (hz : ‖z‖ < 1) (mode : CutoffMode cutoff) :
    cutoffEigenvalue z mode ≠ 0 := by
  intro hZero
  have hzEq : z = -signedFrequency mode := by
    exact eq_neg_of_add_eq_zero_right hZero
  have hFrequency : 1 ≤ ‖signedFrequency mode‖ := by
    rcases mode with ⟨mode, sign⟩
    have hPositive : 1 ≤ ‖(((mode.val + 1 : ℕ) : ℂ))‖ := by
      calc
        1 ≤ |(((mode.val + 1 : ℕ) : ℂ)).re| := by
          rw [abs_of_nonneg]
          · exact_mod_cast Nat.succ_le_succ (Nat.zero_le mode.val)
          · exact_mod_cast Nat.zero_le (mode.val + 1)
        _ ≤ ‖(((mode.val + 1 : ℕ) : ℂ))‖ := Complex.abs_re_le_norm _
    cases sign
    · change 1 ≤ ‖(((mode.val + 1 : ℕ) : ℂ))‖
      exact hPositive
    · change 1 ≤ ‖-(((mode.val + 1 : ℕ) : ℂ))‖
      simpa only [norm_neg] using hPositive
  rw [hzEq, norm_neg] at hz
  exact (not_lt_of_ge hFrequency) hz

/-- Consequently the finite determinant does not vanish on that disk. -/
theorem cutoffDeterminant_ne_zero_of_norm_lt_one (cutoff : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    cutoffDeterminant cutoff z ≠ 0 := by
  rw [cutoffDeterminant_product]
  exact Finset.prod_ne_zero_iff.mpr fun mode _ =>
    cutoffEigenvalue_ne_zero_of_norm_lt_one hz mode

/-- The finite Dirac operator is invertible throughout the unit holonomy disk. -/
theorem cutoffDirac_injective_of_norm_lt_one (cutoff : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    Function.Injective (cutoffDirac cutoff z) := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hKernel
  exact cutoffDeterminant_ne_zero_of_norm_lt_one cutoff hz
    (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hKernel)

/-- An actual inverse linear equivalence for every small-holonomy cutoff. -/
noncomputable def cutoffDiracEquiv (cutoff : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    CutoffSpace cutoff ≃ₗ[ℂ] CutoffSpace cutoff :=
  LinearEquiv.ofInjectiveEndo (cutoffDirac cutoff z)
    (cutoffDirac_injective_of_norm_lt_one cutoff hz)

/-- The top exterior power of the cutoff coefficient space. -/
abbrev CutoffTopExterior (cutoff : ℕ) :=
  ⋀[ℂ]^(Fintype.card (CutoffMode cutoff)) (CutoffSpace cutoff)

/-- The finite determinant line is `Hom(det domain, det codomain)`. -/
abbrev CutoffDeterminantLine (cutoff : ℕ) :=
  CutoffTopExterior cutoff →ₗ[ℂ] CutoffTopExterior cutoff

/-- The determinant-line section induced functorially by the finite Dirac family. -/
def cutoffDeterminantLineSection (cutoff : ℕ) (z : ℂ) :
    CutoffDeterminantLine cutoff :=
  exteriorPower.map (Fintype.card (CutoffMode cutoff))
    (cutoffDirac cutoff z)

theorem cutoffSpace_finrank (cutoff : ℕ) :
    Module.finrank ℂ (CutoffSpace cutoff) =
      Fintype.card (CutoffMode cutoff) := by
  simp [CutoffSpace]

/-- The top exterior power is genuinely one-dimensional. -/
theorem cutoffTopExterior_finrank_one (cutoff : ℕ) :
    Module.finrank ℂ (CutoffTopExterior cutoff) = 1 := by
  rw [exteriorPower.finrank_eq, cutoffSpace_finrank, Nat.choose_self]

/-- Hence the finite determinant-line fiber is genuinely one-dimensional. -/
theorem cutoffDeterminantLine_finrank_one (cutoff : ℕ) :
    Module.finrank ℂ (CutoffDeterminantLine cutoff) = 1 := by
  rw [Module.finrank_linearMap, cutoffTopExterior_finrank_one]

/-- On the unit disk the induced top-exterior map is injective. -/
theorem cutoffDeterminantLineSection_injective (cutoff : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    Function.Injective (cutoffDeterminantLineSection cutoff z) := by
  exact exteriorPower.map_injective_field
    (cutoffDirac_injective_of_norm_lt_one cutoff hz)

/-- Positive spectral magnitude, kept separate from the line-valued section. -/
def cutoffPositiveSpectralMagnitude (cutoff : ℕ) (z : ℂ) : ℝ :=
  Complex.normSq (cutoffDeterminant cutoff z)

theorem cutoffPositiveSpectralMagnitude_nonnegative (cutoff : ℕ) (z : ℂ) :
    0 ≤ cutoffPositiveSpectralMagnitude cutoff z := by
  exact Complex.normSq_nonneg _

/-- The two quarter-holonomy roots give the same paired determinant coordinate. -/
theorem quarter_holonomy_determinants_agree (cutoff : ℕ) :
    cutoffDeterminant cutoff (-(1 / 4 : ℂ)) =
      cutoffDeterminant cutoff (1 / 4 : ℂ) := by
  exact cutoffDeterminant_pt_invariant cutoff (1 / 4 : ℂ)

/-- Both physical quarter-holonomy cutoffs are invertible. -/
theorem quarter_holonomy_cutoffs_invertible (cutoff : ℕ) :
    Function.Bijective (cutoffDirac cutoff (1 / 4 : ℂ)) ∧
      Function.Bijective (cutoffDirac cutoff (-(1 / 4 : ℂ))) := by
  have hPositive : ‖(1 / 4 : ℂ)‖ < 1 := by norm_num [Complex.norm_real]
  have hNegative : ‖(-(1 / 4 : ℂ))‖ < 1 := by simpa using hPositive
  constructor
  · have hInjective := cutoffDirac_injective_of_norm_lt_one cutoff hPositive
    exact ⟨hInjective, LinearMap.injective_iff_surjective.mp hInjective⟩
  · have hInjective := cutoffDirac_injective_of_norm_lt_one cutoff hNegative
    exact ⟨hInjective, LinearMap.injective_iff_surjective.mp hInjective⟩

end

end P0EFTJanusFiniteModeFredholmDeterminantLine
end JanusFormal
