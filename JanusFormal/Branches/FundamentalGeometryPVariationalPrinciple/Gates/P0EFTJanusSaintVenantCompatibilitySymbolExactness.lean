import Mathlib

/-!
# Canonical-frequency Saint-Venant symbol exactness

For the nonzero coordinate covector `xi = dx^0` on `R^4`, this gate constructs
the linearized metric/strain symbol

`sigma_J(xi)(v)_{ij} = xi_i v_j + xi_j v_i`

and the Saint-Venant (linearized curvature) symbol

`sigma_R(xi)(h)_{ijkl}`.

The composition `sigma_R o sigma_J` vanishes.  Conversely, for a symmetric
two-tensor, vanishing Saint-Venant symbol implies that the tensor is a unique
strain symbol.  Thus the symbol sequence is exact at this explicit nonzero
frequency, and the strain symbol is injective.

This is finite coordinate algebra at the canonical covector.  It does not
prove arbitrary-covector naturality, a global Lorentzian differential
complex, boundary exactness, ellipticity, or PDE solvability.
-/

namespace JanusFormal
namespace P0EFTJanusSaintVenantCompatibilitySymbolExactness

set_option autoImplicit false

noncomputable section

abbrev Index4 := Fin 4
abbrev TangentIndex := Fin 3
abbrev Vector4 := Index4 → ℝ
abbrev CovariantTwoTensor := Matrix Index4 Index4 ℝ
abbrev CovariantFourTensor := Index4 → Index4 → Index4 → Index4 → ℝ

def normalIndex : Index4 := 0

def tangentIndex (index : TangentIndex) : Index4 :=
  Fin.succ index

/-- Canonical nonzero frequency `dx^0`. -/
def canonicalCovector (index : Index4) : ℝ :=
  if index = normalIndex then 1 else 0

@[simp]
theorem canonicalCovector_normal :
    canonicalCovector normalIndex = 1 := by
  simp [canonicalCovector]

@[simp]
theorem canonicalCovector_tangent (index : TangentIndex) :
    canonicalCovector (tangentIndex index) = 0 := by
  simp [canonicalCovector, normalIndex, tangentIndex]

/-- Principal symbol of the linearized metric/Gram map at the identity. -/
def strainSymbol (variation : Vector4) : CovariantTwoTensor :=
  fun row column =>
    canonicalCovector row * variation column +
      canonicalCovector column * variation row

theorem strainSymbol_symmetric (variation : Vector4) :
    (strainSymbol variation).transpose = strainSymbol variation := by
  ext row column
  simp [strainSymbol, Matrix.transpose_apply]
  ring

/-- Diagonal coefficients of the explicit Minkowski metric. -/
def lorentzSign (index : Index4) : ℝ :=
  if index = normalIndex then -1 else 1

/-- Lower an ambient variation with `eta = diag(-1,1,1,1)`. -/
def lorentzLower (variation : Vector4) : Vector4 :=
  fun index => lorentzSign index * variation index

@[simp]
theorem lorentzLower_involutive (variation : Vector4) :
    lorentzLower (lorentzLower variation) = variation := by
  funext index
  fin_cases index <;> norm_num [lorentzLower, lorentzSign, normalIndex]

/-- The canonical-frequency Lorentzian Gram symbol at the identity frame. -/
def lorentzGramCanonicalSymbol (variation : Vector4) : CovariantTwoTensor :=
  strainSymbol (lorentzLower variation)

/-- Canonical-frequency Saint-Venant/linearized-curvature symbol. -/
def saintVenantSymbol
    (tensor : CovariantTwoTensor) : CovariantFourTensor :=
  fun first second third fourth =>
    canonicalCovector first * canonicalCovector third * tensor second fourth +
      canonicalCovector second * canonicalCovector fourth * tensor first third -
      canonicalCovector first * canonicalCovector fourth * tensor second third -
      canonicalCovector second * canonicalCovector third * tensor first fourth

/-- Gauge/strain directions are killed by the curvature symbol. -/
theorem saintVenantSymbol_strainSymbol_eq_zero (variation : Vector4) :
    saintVenantSymbol (strainSymbol variation) = 0 := by
  funext first second third fourth
  simp [saintVenantSymbol, strainSymbol]
  ring

/-- The Saint-Venant symbol kills the explicit Lorentzian Gram `J` symbol. -/
theorem saintVenantSymbol_lorentzGramCanonicalSymbol_eq_zero
    (variation : Vector4) :
    saintVenantSymbol (lorentzGramCanonicalSymbol variation) = 0 := by
  exact saintVenantSymbol_strainSymbol_eq_zero (lorentzLower variation)

/-- The canonical strain symbol is injective at the nonzero frequency. -/
theorem strainSymbol_injective : Function.Injective strainSymbol := by
  intro first second hEqual
  funext index
  refine Fin.cases ?_ (fun tangent => ?_) index
  · have hNormal := congrArg
      (fun tensor => tensor normalIndex normalIndex) hEqual
    simp [strainSymbol] at hNormal
    have hNormal' : first 0 + first 0 = second 0 + second 0 := by
      simpa [normalIndex] using hNormal
    linarith
  · have hMixed := congrArg
      (fun tensor => tensor normalIndex (tangentIndex tangent)) hEqual
    simpa [strainSymbol, canonicalCovector, normalIndex, tangentIndex] using hMixed

/-- Nondegeneracy of `eta` transfers injectivity to the Lorentzian Gram
symbol. -/
theorem lorentzGramCanonicalSymbol_injective :
    Function.Injective lorentzGramCanonicalSymbol := by
  intro first second hEqual
  have hLower : lorentzLower first = lorentzLower second :=
    strainSymbol_injective hEqual
  have hRaised := congrArg lorentzLower hLower
  simpa using hRaised

/-- Explicit gauge vector reconstructed from a symmetric tensor in the
Saint-Venant kernel. -/
def reconstructedGaugeVector
    (tensor : CovariantTwoTensor) : Vector4 :=
  fun index => Fin.cases (tensor normalIndex normalIndex / 2)
    (fun tangent => tensor normalIndex (tangentIndex tangent)) index

@[simp]
theorem reconstructedGaugeVector_normal (tensor : CovariantTwoTensor) :
    reconstructedGaugeVector tensor normalIndex =
      tensor normalIndex normalIndex / 2 := by
  rfl

@[simp]
theorem reconstructedGaugeVector_tangent
    (tensor : CovariantTwoTensor) (index : TangentIndex) :
    reconstructedGaugeVector tensor (tangentIndex index) =
      tensor normalIndex (tangentIndex index) := by
  rfl

/-- A symmetric tensor in the canonical Saint-Venant kernel is the strain of
its explicitly reconstructed gauge vector. -/
theorem tensor_eq_strainSymbol_reconstructed_of_symmetric_of_kernel
    (tensor : CovariantTwoTensor)
    (hSymmetric : tensor.transpose = tensor)
    (hKernel : saintVenantSymbol tensor = 0) :
    tensor = strainSymbol (reconstructedGaugeVector tensor) := by
  ext row column
  refine Fin.cases ?_ (fun tangentRow => ?_) row
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · simp [strainSymbol, canonicalCovector, normalIndex,
        reconstructedGaugeVector]
    · simp [strainSymbol, canonicalCovector, normalIndex, tangentIndex,
        reconstructedGaugeVector]
  · refine Fin.cases ?_ (fun tangentColumn => ?_) column
    · have hEntry := congrArg
        (fun matrix => matrix normalIndex (tangentIndex tangentRow)) hSymmetric
      have hEntry' :
          tensor (tangentIndex tangentRow) normalIndex =
            tensor normalIndex (tangentIndex tangentRow) := by
        simpa [Matrix.transpose_apply] using hEntry
      simpa [strainSymbol, canonicalCovector, normalIndex, tangentIndex,
        reconstructedGaugeVector] using hEntry'
    · have hEntry := congrArg
        (fun curvature => curvature normalIndex (tangentIndex tangentRow)
          normalIndex (tangentIndex tangentColumn)) hKernel
      have hTangential :
          tensor (tangentIndex tangentRow) (tangentIndex tangentColumn) = 0 := by
        simpa [saintVenantSymbol] using hEntry
      simpa [strainSymbol, canonicalCovector, normalIndex, tangentIndex,
        reconstructedGaugeVector] using hTangential

/-- Exactness of the canonical-frequency symbol sequence at symmetric
two-tensors. -/
theorem saintVenantSymbol_eq_zero_iff_exists_strain
    (tensor : CovariantTwoTensor)
    (hSymmetric : tensor.transpose = tensor) :
    saintVenantSymbol tensor = 0 ↔
      ∃ variation : Vector4, tensor = strainSymbol variation := by
  constructor
  · intro hKernel
    exact ⟨reconstructedGaugeVector tensor,
      tensor_eq_strainSymbol_reconstructed_of_symmetric_of_kernel
        tensor hSymmetric hKernel⟩
  · rintro ⟨variation, rfl⟩
    exact saintVenantSymbol_strainSymbol_eq_zero variation

/-- The same exact kernel statement written as the image of the explicit
Minkowski Gram linearization symbol. -/
theorem saintVenantSymbol_eq_zero_iff_exists_lorentzGramSymbol
    (tensor : CovariantTwoTensor)
    (hSymmetric : tensor.transpose = tensor) :
    saintVenantSymbol tensor = 0 ↔
      ∃ variation : Vector4,
        tensor = lorentzGramCanonicalSymbol variation := by
  rw [saintVenantSymbol_eq_zero_iff_exists_strain tensor hSymmetric]
  constructor
  · rintro ⟨covectorVariation, hTensor⟩
    refine ⟨lorentzLower covectorVariation, ?_⟩
    simpa [lorentzGramCanonicalSymbol] using hTensor
  · rintro ⟨ambientVariation, hTensor⟩
    exact ⟨lorentzLower ambientVariation, hTensor⟩

/-- Combined short exactness statement for the explicit symbol sequence. -/
theorem canonical_strain_saintVenant_symbol_sequence_exact :
    Function.Injective strainSymbol ∧
      (∀ tensor : CovariantTwoTensor,
        tensor.transpose = tensor →
          (saintVenantSymbol tensor = 0 ↔
            ∃ variation : Vector4, tensor = strainSymbol variation)) := by
  exact ⟨strainSymbol_injective,
    fun tensor hSymmetric =>
      saintVenantSymbol_eq_zero_iff_exists_strain tensor hSymmetric⟩

/-- Short exactness with the explicit Lorentzian Gram symbol as the first
arrow. -/
theorem canonical_lorentzGram_saintVenant_symbol_sequence_exact :
    Function.Injective lorentzGramCanonicalSymbol ∧
      (∀ tensor : CovariantTwoTensor,
        tensor.transpose = tensor →
          (saintVenantSymbol tensor = 0 ↔
            ∃ variation : Vector4,
              tensor = lorentzGramCanonicalSymbol variation)) := by
  exact ⟨lorentzGramCanonicalSymbol_injective,
    fun tensor hSymmetric =>
      saintVenantSymbol_eq_zero_iff_exists_lorentzGramSymbol
        tensor hSymmetric⟩

end

end P0EFTJanusSaintVenantCompatibilitySymbolExactness
end JanusFormal
