import Mathlib

/-!
# Arbitrary-frequency Saint-Venant symbol exactness

For every nonzero covector `xi : Fin 4 -> R`, this gate defines the strain
symbol `sigma_J(xi)` and the Saint-Venant symbol `sigma_R(xi)`.  Their
composition vanishes, the strain symbol is injective, and every symmetric
tensor in the Saint-Venant kernel is reconstructed explicitly from any pivot
`p` with `xi p != 0`.

This is pointwise symbol algebra at one arbitrary nonzero frequency.  It does
not prove a global differential complex, PDE solvability, or boundary
exactness.
-/

namespace JanusFormal
namespace P0EFTJanusArbitraryFrequencySaintVenantExactness

set_option autoImplicit false

noncomputable section

abbrev Index4 := Fin 4
abbrev Vector4 := Index4 -> Real
abbrev Covector4 := Index4 -> Real
abbrev CovariantTwoTensor := Matrix Index4 Index4 Real
abbrev CovariantFourTensor :=
  Index4 -> Index4 -> Index4 -> Index4 -> Real

/-- Principal symbol of the linearized metric map at covector `xi`. -/
def strainSymbol (xi : Covector4) (variation : Vector4) :
    CovariantTwoTensor :=
  fun row column =>
    xi row * variation column + xi column * variation row

theorem strainSymbol_symmetric (xi : Covector4) (variation : Vector4) :
    (strainSymbol xi variation).transpose = strainSymbol xi variation := by
  ext row column
  simp [strainSymbol, Matrix.transpose_apply]
  ring

/-- Principal Saint-Venant (linearized-curvature) symbol at `xi`. -/
def saintVenantSymbol (xi : Covector4) (tensor : CovariantTwoTensor) :
    CovariantFourTensor :=
  fun first second third fourth =>
    xi first * xi third * tensor second fourth +
      xi second * xi fourth * tensor first third -
      xi first * xi fourth * tensor second third -
      xi second * xi third * tensor first fourth

/-- The curvature symbol kills every strain direction, at every frequency. -/
theorem saintVenantSymbol_strainSymbol_eq_zero
    (xi : Covector4) (variation : Vector4) :
    saintVenantSymbol xi (strainSymbol xi variation) = 0 := by
  funext first second third fourth
  simp [saintVenantSymbol, strainSymbol]
  ring

theorem exists_nonzero_pivot
    (xi : Covector4) (hXi : xi ≠ 0) :
    Exists fun pivot => xi pivot ≠ 0 := by
  by_contra hPivot
  push Not at hPivot
  apply hXi
  funext pivot
  exact hPivot pivot

/-- At a nonzero frequency the strain symbol has no gauge kernel. -/
theorem strainSymbol_injective_of_pivot
    (xi : Covector4) (pivot : Index4) (hPivot : xi pivot ≠ 0) :
    Function.Injective (strainSymbol xi) := by
  intro first second hEqual
  funext index
  have hDiagonal := congrArg
    (fun tensor => tensor pivot pivot) hEqual
  have hPivotComponent : first pivot = second pivot := by
    simp only [strainSymbol] at hDiagonal
    have hProduct : xi pivot * (first pivot - second pivot) = 0 := by
      linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_left hPivot)
  have hMixed := congrArg
    (fun tensor => tensor pivot index) hEqual
  simp only [strainSymbol] at hMixed
  rw [hPivotComponent] at hMixed
  have hProduct : xi pivot * (first index - second index) = 0 := by
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_left hPivot)

theorem strainSymbol_injective
    (xi : Covector4) (hXi : xi ≠ 0) :
    Function.Injective (strainSymbol xi) := by
  obtain ⟨pivot, hPivot⟩ := exists_nonzero_pivot xi hXi
  exact strainSymbol_injective_of_pivot xi pivot hPivot

/-- Explicit gauge covector reconstructed through a nonzero pivot. -/
def reconstructedVariation
    (xi : Covector4) (pivot : Index4)
    (tensor : CovariantTwoTensor) : Vector4 :=
  fun index =>
    tensor pivot index / xi pivot -
      xi index * tensor pivot pivot / (2 * (xi pivot) ^ 2)

/-- The pivot formula reconstructs every symmetric tensor in the symbol
kernel, without assuming an externally supplied kernel law. -/
theorem tensor_eq_strainSymbol_reconstructed_of_pivot
    (xi : Covector4) (pivot : Index4) (hPivot : xi pivot ≠ 0)
    (tensor : CovariantTwoTensor)
    (hSymmetric : tensor.transpose = tensor)
    (hKernel : saintVenantSymbol xi tensor = 0) :
    tensor = strainSymbol xi (reconstructedVariation xi pivot tensor) := by
  ext row column
  have hSymmetryEntry : tensor row pivot = tensor pivot row := by
    have hEntry := congrArg
      (fun matrix => matrix pivot row) hSymmetric
    simpa [Matrix.transpose_apply] using hEntry
  have hCurvature := congrArg
    (fun curvature => curvature pivot row pivot column) hKernel
  have hCurvatureEntry :
      xi pivot * xi pivot * tensor row column +
          xi row * xi column * tensor pivot pivot -
          xi pivot * xi column * tensor row pivot -
          xi row * xi pivot * tensor pivot column = 0 := by
    simpa [saintVenantSymbol] using hCurvature
  rw [hSymmetryEntry] at hCurvatureEntry
  simp only [strainSymbol, reconstructedVariation]
  field_simp [hPivot]
  nlinarith [hCurvatureEntry]

theorem saintVenantSymbol_eq_zero_iff_exists_strain_of_pivot
    (xi : Covector4) (pivot : Index4) (hPivot : xi pivot ≠ 0)
    (tensor : CovariantTwoTensor)
    (hSymmetric : tensor.transpose = tensor) :
    saintVenantSymbol xi tensor = 0 <->
      Exists fun variation : Vector4 =>
        tensor = strainSymbol xi variation := by
  constructor
  · intro hKernel
    exact ⟨reconstructedVariation xi pivot tensor,
      tensor_eq_strainSymbol_reconstructed_of_pivot
        xi pivot hPivot tensor hSymmetric hKernel⟩
  · rintro ⟨variation, rfl⟩
    exact saintVenantSymbol_strainSymbol_eq_zero xi variation

/-- Exactness at every nonzero frequency. -/
theorem saintVenantSymbol_eq_zero_iff_exists_strain
    (xi : Covector4) (hXi : xi ≠ 0)
    (tensor : CovariantTwoTensor)
    (hSymmetric : tensor.transpose = tensor) :
    saintVenantSymbol xi tensor = 0 <->
      Exists fun variation : Vector4 =>
        tensor = strainSymbol xi variation := by
  obtain ⟨pivot, hPivot⟩ := exists_nonzero_pivot xi hXi
  exact saintVenantSymbol_eq_zero_iff_exists_strain_of_pivot
    xi pivot hPivot tensor hSymmetric

/-- Equality of the strain image with the symmetric Saint-Venant kernel. -/
theorem range_strainSymbol_eq_symmetric_saintVenant_kernel
    (xi : Covector4) (hXi : xi ≠ 0) :
    Set.range (strainSymbol xi) =
      {tensor : CovariantTwoTensor |
        tensor.transpose = tensor /\ saintVenantSymbol xi tensor = 0} := by
  ext tensor
  constructor
  · rintro ⟨variation, rfl⟩
    exact ⟨strainSymbol_symmetric xi variation,
      saintVenantSymbol_strainSymbol_eq_zero xi variation⟩
  · rintro ⟨hSymmetric, hKernel⟩
    obtain ⟨variation, hTensor⟩ :=
      (saintVenantSymbol_eq_zero_iff_exists_strain
        xi hXi tensor hSymmetric).mp hKernel
    exact ⟨variation, hTensor.symm⟩

/-- Diagonal coefficients of `eta = diag(-1,1,1,1)`. -/
def lorentzSign (index : Index4) : Real :=
  if index = 0 then -1 else 1

/-- Lower an ambient variation with the nondegenerate Minkowski metric. -/
def lorentzLower (variation : Vector4) : Vector4 :=
  fun index => lorentzSign index * variation index

@[simp]
theorem lorentzLower_involutive (variation : Vector4) :
    lorentzLower (lorentzLower variation) = variation := by
  funext index
  fin_cases index <;> norm_num [lorentzLower, lorentzSign]

/-- Arbitrary-frequency Lorentzian Gram linearization symbol. -/
def lorentzGramSymbol (xi : Covector4) (variation : Vector4) :
    CovariantTwoTensor :=
  strainSymbol xi (lorentzLower variation)

theorem saintVenantSymbol_lorentzGramSymbol_eq_zero
    (xi : Covector4) (variation : Vector4) :
    saintVenantSymbol xi (lorentzGramSymbol xi variation) = 0 :=
  saintVenantSymbol_strainSymbol_eq_zero xi (lorentzLower variation)

theorem lorentzGramSymbol_injective
    (xi : Covector4) (hXi : xi ≠ 0) :
    Function.Injective (lorentzGramSymbol xi) := by
  intro first second hEqual
  have hLower : lorentzLower first = lorentzLower second :=
    strainSymbol_injective xi hXi hEqual
  have hRaised := congrArg lorentzLower hLower
  simpa using hRaised

theorem range_lorentzGramSymbol_eq_range_strainSymbol
    (xi : Covector4) :
    Set.range (lorentzGramSymbol xi) = Set.range (strainSymbol xi) := by
  ext tensor
  constructor
  · rintro ⟨variation, rfl⟩
    exact ⟨lorentzLower variation, rfl⟩
  · rintro ⟨variation, rfl⟩
    refine ⟨lorentzLower variation, ?_⟩
    simp [lorentzGramSymbol]

theorem range_lorentzGramSymbol_eq_symmetric_saintVenant_kernel
    (xi : Covector4) (hXi : xi ≠ 0) :
    Set.range (lorentzGramSymbol xi) =
      {tensor : CovariantTwoTensor |
        tensor.transpose = tensor /\ saintVenantSymbol xi tensor = 0} := by
  rw [range_lorentzGramSymbol_eq_range_strainSymbol,
    range_strainSymbol_eq_symmetric_saintVenant_kernel xi hXi]

/-- Combined arbitrary-frequency exact-symbol certificate. -/
theorem arbitrary_frequency_saintVenant_symbol_sequence_exact
    (xi : Covector4) (hXi : xi ≠ 0) :
    Function.Injective (strainSymbol xi) /\
      Set.range (strainSymbol xi) =
        {tensor : CovariantTwoTensor |
          tensor.transpose = tensor /\ saintVenantSymbol xi tensor = 0} := by
  exact ⟨strainSymbol_injective xi hXi,
    range_strainSymbol_eq_symmetric_saintVenant_kernel xi hXi⟩

end

end P0EFTJanusArbitraryFrequencySaintVenantExactness
end JanusFormal
