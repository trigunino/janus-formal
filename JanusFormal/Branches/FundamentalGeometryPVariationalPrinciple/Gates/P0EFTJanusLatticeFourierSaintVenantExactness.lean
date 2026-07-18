import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCountableFourierSaintVenantExactness

/-!
# Integer-lattice Fourier Saint-Venant exactness

This gate upgrades the coefficientwise Saint-Venant reconstruction to the
countable four-dimensional lattice `Z^4`.  At every nonzero lattice mode it
chooses a coordinate of maximal absolute value.  The chosen pivot has size at
least one and dominates every other coordinate, so the explicit inverse
multiplier has a uniform bound independent of the mode.

Compatible symmetric coefficients are reconstructed mode by mode.  The sole
algebraic obstruction is the coefficient at the zero mode, and coordinatewise
`ell^2` summability is preserved by reconstruction.  This remains a Fourier
coefficient theorem: it does not assert convergence of differentiated Fourier
series, a global PDE inverse, or boundary exactness.
-/

namespace JanusFormal
namespace P0EFTJanusLatticeFourierSaintVenantExactness

set_option autoImplicit false

noncomputable section

open P0EFTJanusArbitraryFrequencySaintVenantExactness
open P0EFTJanusFiniteFourierSaintVenantExactness

abbrev LatticeMode := Fin 4 -> Int
abbrev LatticePotential := LatticeMode -> Vector4
abbrev LatticeMetricCoefficient := LatticeMode -> CovariantTwoTensor
abbrev LatticeCurvatureCoefficient := LatticeMode -> CovariantFourTensor

theorem latticeMode_countable : Countable LatticeMode := inferInstance

/-- The real covector associated with an integer lattice mode. -/
def latticeFrequency (mode : LatticeMode) : Covector4 :=
  fun index => (mode index : Real)

@[simp]
theorem latticeFrequency_zero : latticeFrequency 0 = 0 := by
  funext index
  simp [latticeFrequency]

theorem latticeFrequency_ne_zero {mode : LatticeMode} (hMode : mode ≠ 0) :
    latticeFrequency mode ≠ 0 := by
  intro hFrequency
  apply hMode
  funext index
  have hEntry : ((mode index : Int) : Real) = 0 := by
    simpa [latticeFrequency] using congrFun hFrequency index
  exact Int.cast_eq_zero.mp hEntry

/-- A maximal-coordinate pivot exists because the coordinate atlas is finite. -/
theorem exists_dominant_lattice_pivot (mode : LatticeMode) :
    Exists fun pivot : Index4 => forall index : Index4,
      |(mode index : Real)| <= |(mode pivot : Real)| := by
  obtain ⟨pivot, _hPivotMem, hMax⟩ :=
    Finset.exists_max_image Finset.univ
      (fun index : Index4 => |(mode index : Real)|) Finset.univ_nonempty
  exact ⟨pivot, fun index => hMax index (Finset.mem_univ index)⟩

/-- Deterministic choice of a maximal-coordinate pivot. -/
def latticePivot (mode : LatticeMode) : Index4 :=
  Classical.choose (exists_dominant_lattice_pivot mode)

theorem latticePivot_dominates (mode : LatticeMode) (index : Index4) :
    |(mode index : Real)| <= |(mode (latticePivot mode) : Real)| :=
  Classical.choose_spec (exists_dominant_lattice_pivot mode) index

/-- The integer gap gives a mode-independent lower bound on the chosen pivot. -/
theorem one_le_abs_latticePivot
    (mode : LatticeMode) (hMode : mode ≠ 0) :
    (1 : Real) <= |(mode (latticePivot mode) : Real)| := by
  have hExists : Exists fun index : Index4 => mode index ≠ 0 := by
    by_contra hNoIndex
    push Not at hNoIndex
    apply hMode
    funext index
    exact hNoIndex index
  obtain ⟨index, hIndex⟩ := hExists
  have hIntegerGap : (1 : Real) <= |(mode index : Real)| := by
    exact_mod_cast Int.one_le_abs hIndex
  exact hIntegerGap.trans (latticePivot_dominates mode index)

theorem latticeFrequency_pivot_ne_zero
    (mode : LatticeMode) (hMode : mode ≠ 0) :
    latticeFrequency mode (latticePivot mode) ≠ 0 := by
  intro hZero
  have hLower := one_le_abs_latticePivot mode hMode
  have hZeroCast : (mode (latticePivot mode) : Real) = 0 := by
    simpa [latticeFrequency] using hZero
  rw [hZeroCast] at hLower
  norm_num at hLower

/-- Lorentz-Gram and Saint-Venant symbols on all four-dimensional modes. -/
def latticeLorentzGram (potential : LatticePotential) :
    LatticeMetricCoefficient :=
  finiteFourierLorentzGram latticeFrequency potential

def latticeSaintVenant (tensor : LatticeMetricCoefficient) :
    LatticeCurvatureCoefficient :=
  finiteFourierSaintVenant latticeFrequency tensor

def SymmetricLatticeCoefficients (tensor : LatticeMetricCoefficient) : Prop :=
  forall mode, (tensor mode).transpose = tensor mode

def LatticePotentialVanishesAtZero (potential : LatticePotential) : Prop :=
  potential 0 = 0

/-- The complete zero-frequency obstruction. -/
def latticeZeroModeResidual (tensor : LatticeMetricCoefficient) :
    LatticeMetricCoefficient :=
  fun mode => if mode = 0 then tensor mode else 0

@[simp]
theorem latticeZeroModeResidual_zero (tensor : LatticeMetricCoefficient) :
    latticeZeroModeResidual tensor 0 = tensor 0 := by
  simp [latticeZeroModeResidual]

theorem latticeZeroModeResidual_nonzero
    (tensor : LatticeMetricCoefficient) {mode : LatticeMode}
    (hMode : mode ≠ 0) :
    latticeZeroModeResidual tensor mode = 0 := by
  simp [latticeZeroModeResidual, hMode]

/-- Explicit reconstruction through the dominant pivot, normalized at zero. -/
def latticeReconstructedPotential
    (tensor : LatticeMetricCoefficient) : LatticePotential :=
  fun mode =>
    if mode = 0 then 0
    else lorentzLower
      (reconstructedVariation
        (latticeFrequency mode) (latticePivot mode) (tensor mode))

@[simp]
theorem latticeReconstructedPotential_zero
    (tensor : LatticeMetricCoefficient) :
    latticeReconstructedPotential tensor 0 = 0 := by
  simp [latticeReconstructedPotential]

theorem latticeReconstructedPotential_vanishesAtZero
    (tensor : LatticeMetricCoefficient) :
    LatticePotentialVanishesAtZero (latticeReconstructedPotential tensor) :=
  latticeReconstructedPotential_zero tensor

theorem latticeSaintVenant_latticeLorentzGram_eq_zero
    (potential : LatticePotential) :
    latticeSaintVenant (latticeLorentzGram potential) = 0 :=
  finiteFourierSaintVenant_finiteFourierLorentzGram_eq_zero
    latticeFrequency potential

/-- Exact coefficientwise reconstruction plus the isolated zero mode. -/
theorem lattice_zeroMode_decomposition
    (tensor : LatticeMetricCoefficient)
    (hSymmetric : SymmetricLatticeCoefficients tensor)
    (hCompatible : latticeSaintVenant tensor = 0) :
    tensor = latticeLorentzGram (latticeReconstructedPotential tensor) +
      latticeZeroModeResidual tensor := by
  funext mode
  by_cases hMode : mode = 0
  . subst mode
    simp [latticeLorentzGram, finiteFourierLorentzGram,
      latticeZeroModeResidual]
  . have hKernel :
        saintVenantSymbol (latticeFrequency mode) (tensor mode) = 0 :=
      congrFun hCompatible mode
    have hReconstruction :=
      tensor_eq_strainSymbol_reconstructed_of_pivot
        (latticeFrequency mode) (latticePivot mode)
        (latticeFrequency_pivot_ne_zero mode hMode)
        (tensor mode) (hSymmetric mode) hKernel
    simpa [latticeLorentzGram, finiteFourierLorentzGram,
      latticeReconstructedPotential, latticeZeroModeResidual, hMode,
      lorentzGramSymbol] using hReconstruction

/-- Exactness on compatible coefficient families with vanishing zero mode. -/
theorem compatible_zeroModeFree_iff_exists_normalizedLatticePotential
    (tensor : LatticeMetricCoefficient)
    (hSymmetric : SymmetricLatticeCoefficients tensor) :
    latticeSaintVenant tensor = 0 /\ latticeZeroModeResidual tensor = 0 <->
      Exists fun potential : LatticePotential =>
        LatticePotentialVanishesAtZero potential /\
          tensor = latticeLorentzGram potential := by
  constructor
  . rintro ⟨hCompatible, hResidual⟩
    refine ⟨latticeReconstructedPotential tensor,
      latticeReconstructedPotential_vanishesAtZero tensor, ?_⟩
    simpa [hResidual] using
      lattice_zeroMode_decomposition tensor hSymmetric hCompatible
  . rintro ⟨potential, _hPotentialZero, rfl⟩
    constructor
    . exact latticeSaintVenant_latticeLorentzGram_eq_zero potential
    . funext mode
      by_cases hMode : mode = 0
      . subst mode
        simp [latticeZeroModeResidual, latticeLorentzGram,
          finiteFourierLorentzGram]
      . simp [latticeZeroModeResidual, hMode]

/-- Coordinatewise square summability on the countable lattice. -/
def LatticePotentialSquareSummable (potential : LatticePotential) : Prop :=
  forall index, Summable fun mode : LatticeMode => (potential mode index) ^ 2

def LatticeMetricSquareSummable (tensor : LatticeMetricCoefficient) : Prop :=
  forall row column,
    Summable fun mode : LatticeMode => (tensor mode row column) ^ 2

theorem lorentzLower_apply_sq
    (variation : Vector4) (index : Index4) :
    (lorentzLower variation index) ^ 2 = (variation index) ^ 2 := by
  fin_cases index <;> norm_num [lorentzLower, lorentzSign]

/-- Elementary uniform estimate for the dominant-pivot inverse formula. -/
theorem dominantPivot_inverse_sq_le
    (x y first diagonal : Real)
    (hOne : 1 <= x ^ 2) (hDominates : y ^ 2 <= x ^ 2) :
    (first / x - y * diagonal / (2 * x ^ 2)) ^ 2 <=
      2 * first ^ 2 + (1 / 2 : Real) * diagonal ^ 2 := by
  have hX : x ≠ 0 := by
    intro hZero
    simp [hZero] at hOne
    norm_num at hOne
  have hXSqPos : 0 < x ^ 2 := sq_pos_of_ne_zero hX
  have hFirst : (first / x) ^ 2 <= first ^ 2 := by
    rw [div_pow]
    apply (div_le_iff₀ hXSqPos).2
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hOne (sq_nonneg first)
  have hXSqLeFourth : x ^ 2 <= x ^ 4 := by
    nlinarith [sq_nonneg x]
  have hYFourth : y ^ 2 <= x ^ 4 := hDominates.trans hXSqLeFourth
  have hDenominator : 2 * x ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hX)
  have hSecond :
      (y * diagonal / (2 * x ^ 2)) ^ 2 <=
        (1 / 4 : Real) * diagonal ^ 2 := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_ne_zero hDenominator)).2
    calc
      (y * diagonal) ^ 2 = y ^ 2 * diagonal ^ 2 := by ring
      _ <= x ^ 4 * diagonal ^ 2 :=
        mul_le_mul_of_nonneg_right hYFourth (sq_nonneg diagonal)
      _ = (1 / 4 : Real) * diagonal ^ 2 * (2 * x ^ 2) ^ 2 := by ring
  have hDifference :
      (first / x - y * diagonal / (2 * x ^ 2)) ^ 2 <=
        2 * (first / x) ^ 2 +
          2 * (y * diagonal / (2 * x ^ 2)) ^ 2 := by
    nlinarith [sq_nonneg
      (first / x + y * diagonal / (2 * x ^ 2))]
  nlinarith

/-- Per-mode estimate through the selected finite pivot atlas. -/
theorem latticeReconstructedPotential_sq_le_pivot
    (tensor : LatticeMetricCoefficient) (mode : LatticeMode)
    (index : Index4) (hMode : mode ≠ 0) :
    (latticeReconstructedPotential tensor mode index) ^ 2 <=
      2 * (tensor mode (latticePivot mode) index) ^ 2 +
        (1 / 2 : Real) *
          (tensor mode (latticePivot mode) (latticePivot mode)) ^ 2 := by
  have hAbsOne := one_le_abs_latticePivot mode hMode
  have hOne :
      1 <= (latticeFrequency mode (latticePivot mode)) ^ 2 := by
    have hAbs :
        (1 : Real) <= |latticeFrequency mode (latticePivot mode)| := by
      simpa [latticeFrequency] using hAbsOne
    have hSquared :=
      mul_self_le_mul_self (by norm_num : (0 : Real) <= 1) hAbs
    calc
      (1 : Real) = 1 * 1 := by ring
      _ <= |latticeFrequency mode (latticePivot mode)| *
          |latticeFrequency mode (latticePivot mode)| := hSquared
      _ = (latticeFrequency mode (latticePivot mode)) ^ 2 := by
        rw [abs_mul_abs_self]
        ring
  have hDominates :
      (latticeFrequency mode index) ^ 2 <=
        (latticeFrequency mode (latticePivot mode)) ^ 2 := by
    rw [sq_le_sq]
    simpa [latticeFrequency] using latticePivot_dominates mode index
  rw [latticeReconstructedPotential]
  simp only [if_neg hMode, lorentzLower_apply_sq, reconstructedVariation]
  exact dominantPivot_inverse_sq_le
    (latticeFrequency mode (latticePivot mode))
    (latticeFrequency mode index)
    (tensor mode (latticePivot mode) index)
    (tensor mode (latticePivot mode) (latticePivot mode))
    hOne hDominates

/-- A fixed finite-coordinate majorant, independent of the selected pivot. -/
theorem latticeReconstructedPotential_sq_le_finiteSum
    (tensor : LatticeMetricCoefficient) (mode : LatticeMode)
    (index : Index4) :
    (latticeReconstructedPotential tensor mode index) ^ 2 <=
      2 * (Finset.univ.sum fun row : Index4 =>
        (tensor mode row index) ^ 2) +
      (1 / 2 : Real) * (Finset.univ.sum fun row : Index4 =>
        (tensor mode row row) ^ 2) := by
  by_cases hMode : mode = 0
  . subst mode
    have hPotentialZero :
        latticeReconstructedPotential tensor 0 index = 0 := by
      exact congrFun (latticeReconstructedPotential_zero tensor) index
    rw [hPotentialZero]
    have hColumnNonnegative :
        0 <= Finset.univ.sum fun row : Index4 =>
          (tensor 0 row index) ^ 2 :=
      Finset.sum_nonneg fun row _hRow => sq_nonneg (tensor 0 row index)
    have hDiagonalNonnegative :
        0 <= Finset.univ.sum fun row : Index4 =>
          (tensor 0 row row) ^ 2 :=
      Finset.sum_nonneg fun row _hRow => sq_nonneg (tensor 0 row row)
    nlinarith
  . have hPivot := latticeReconstructedPotential_sq_le_pivot
      tensor mode index hMode
    have hColumn :
        (tensor mode (latticePivot mode) index) ^ 2 <=
          Finset.univ.sum fun row : Index4 =>
            (tensor mode row index) ^ 2 := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun row : Index4 => (tensor mode row index) ^ 2)
        (fun row _hRow => sq_nonneg (tensor mode row index))
        (Finset.mem_univ (latticePivot mode))
    have hDiagonal :
        (tensor mode (latticePivot mode) (latticePivot mode)) ^ 2 <=
          Finset.univ.sum fun row : Index4 =>
            (tensor mode row row) ^ 2 := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun row : Index4 => (tensor mode row row) ^ 2)
        (fun row _hRow => sq_nonneg (tensor mode row row))
        (Finset.mem_univ (latticePivot mode))
    nlinarith

/-- The uniform lattice inverse preserves coordinatewise `ell^2`. -/
theorem latticeReconstructedPotential_squareSummable
    (tensor : LatticeMetricCoefficient)
    (hSummable : LatticeMetricSquareSummable tensor) :
    LatticePotentialSquareSummable (latticeReconstructedPotential tensor) := by
  intro index
  have hColumn : Summable (fun mode : LatticeMode =>
      Finset.univ.sum fun row : Index4 =>
        (tensor mode row index) ^ 2) := by
    apply summable_sum
    intro row _hRow
    exact hSummable row index
  have hDiagonal : Summable (fun mode : LatticeMode =>
      Finset.univ.sum fun row : Index4 =>
        (tensor mode row row) ^ 2) := by
    apply summable_sum
    intro row _hRow
    exact hSummable row row
  have hMajorant : Summable (fun mode : LatticeMode =>
      2 * (Finset.univ.sum fun row : Index4 =>
        (tensor mode row index) ^ 2) +
      (1 / 2 : Real) * (Finset.univ.sum fun row : Index4 =>
        (tensor mode row row) ^ 2)) :=
    (hColumn.mul_left 2).add (hDiagonal.mul_left (1 / 2 : Real))
  exact Summable.of_nonneg_of_le
    (fun mode => sq_nonneg (latticeReconstructedPotential tensor mode index))
    (fun mode => latticeReconstructedPotential_sq_le_finiteSum
      tensor mode index)
    hMajorant

/-- Square summability with an arbitrary fixed Fourier weight.  Nonnegative
weights include the standard polynomial Sobolev weights on `Z^4`. -/
def WeightedLatticePotentialSquareSummable
    (weight : LatticeMode -> Real) (potential : LatticePotential) : Prop :=
  forall index, Summable fun mode : LatticeMode =>
    weight mode * (potential mode index) ^ 2

def WeightedLatticeMetricSquareSummable
    (weight : LatticeMode -> Real)
    (tensor : LatticeMetricCoefficient) : Prop :=
  forall row column, Summable fun mode : LatticeMode =>
    weight mode * (tensor mode row column) ^ 2

/-- The dominant-pivot inverse preserves every common nonnegative Fourier
weight, with the same mode-independent constants as the unweighted estimate. -/
theorem latticeReconstructedPotential_weightedSquareSummable
    (weight : LatticeMode -> Real)
    (hWeight : forall mode, 0 <= weight mode)
    (tensor : LatticeMetricCoefficient)
    (hSummable : WeightedLatticeMetricSquareSummable weight tensor) :
    WeightedLatticePotentialSquareSummable weight
      (latticeReconstructedPotential tensor) := by
  intro index
  have hColumn : Summable (fun mode : LatticeMode =>
      weight mode * (Finset.univ.sum fun row : Index4 =>
        (tensor mode row index) ^ 2)) := by
    have hColumnSum : Summable (fun mode : LatticeMode =>
        Finset.univ.sum fun row : Index4 =>
          weight mode * (tensor mode row index) ^ 2) := by
      apply summable_sum
      intro row _hRow
      exact hSummable row index
    simpa only [Finset.mul_sum] using hColumnSum
  have hDiagonal : Summable (fun mode : LatticeMode =>
      weight mode * (Finset.univ.sum fun row : Index4 =>
        (tensor mode row row) ^ 2)) := by
    have hDiagonalSum : Summable (fun mode : LatticeMode =>
        Finset.univ.sum fun row : Index4 =>
          weight mode * (tensor mode row row) ^ 2) := by
      apply summable_sum
      intro row _hRow
      exact hSummable row row
    simpa only [Finset.mul_sum] using hDiagonalSum
  have hSeparatedMajorant : Summable (fun mode : LatticeMode =>
      2 * (weight mode * (Finset.univ.sum fun row : Index4 =>
        (tensor mode row index) ^ 2)) +
      (1 / 2 : Real) *
        (weight mode * (Finset.univ.sum fun row : Index4 =>
          (tensor mode row row) ^ 2))) :=
    (hColumn.mul_left 2).add (hDiagonal.mul_left (1 / 2 : Real))
  have hMajorant : Summable (fun mode : LatticeMode =>
      weight mode *
        (2 * (Finset.univ.sum fun row : Index4 =>
          (tensor mode row index) ^ 2) +
        (1 / 2 : Real) * (Finset.univ.sum fun row : Index4 =>
          (tensor mode row row) ^ 2))) := by
    convert hSeparatedMajorant using 1
    funext mode
    ring
  exact Summable.of_nonneg_of_le
    (fun mode => mul_nonneg (hWeight mode)
      (sq_nonneg (latticeReconstructedPotential tensor mode index)))
    (fun mode => mul_le_mul_of_nonneg_left
      (latticeReconstructedPotential_sq_le_finiteSum tensor mode index)
      (hWeight mode))
    hMajorant

/-- The singleton zero-mode residual is automatically square summable. -/
theorem latticeZeroModeResidual_squareSummable
    (tensor : LatticeMetricCoefficient) :
    LatticeMetricSquareSummable (latticeZeroModeResidual tensor) := by
  intro row column
  apply summable_of_ne_finset_zero (s := {0})
  intro mode hMode
  simp only [Finset.mem_singleton] at hMode
  simp [latticeZeroModeResidual, hMode]

theorem latticeZeroModeResidual_weightedSquareSummable
    (weight : LatticeMode -> Real)
    (tensor : LatticeMetricCoefficient) :
    WeightedLatticeMetricSquareSummable weight
      (latticeZeroModeResidual tensor) := by
  intro row column
  apply summable_of_ne_finset_zero (s := {0})
  intro mode hMode
  simp only [Finset.mem_singleton] at hMode
  simp [latticeZeroModeResidual, hMode]

/-- Countable `Z^4` exactness with zero-mode and uniform `ell^2` control. -/
theorem lattice_fourier_saintVenant_exactness_gate :
    (forall tensor : LatticeMetricCoefficient,
      SymmetricLatticeCoefficients tensor -> latticeSaintVenant tensor = 0 ->
      tensor = latticeLorentzGram (latticeReconstructedPotential tensor) +
        latticeZeroModeResidual tensor) /\
    (forall tensor : LatticeMetricCoefficient,
      LatticeMetricSquareSummable tensor ->
      LatticePotentialSquareSummable (latticeReconstructedPotential tensor)) /\
    (forall (weight : LatticeMode -> Real),
      (forall mode, 0 <= weight mode) ->
      forall tensor : LatticeMetricCoefficient,
        WeightedLatticeMetricSquareSummable weight tensor ->
        WeightedLatticePotentialSquareSummable weight
          (latticeReconstructedPotential tensor)) /\
    (forall tensor : LatticeMetricCoefficient,
      SymmetricLatticeCoefficients tensor ->
      (latticeSaintVenant tensor = 0 /\ latticeZeroModeResidual tensor = 0 <->
        Exists fun potential : LatticePotential =>
          LatticePotentialVanishesAtZero potential /\
            tensor = latticeLorentzGram potential)) := by
  exact ⟨lattice_zeroMode_decomposition,
    latticeReconstructedPotential_squareSummable,
    latticeReconstructedPotential_weightedSquareSummable,
    compatible_zeroModeFree_iff_exists_normalizedLatticePotential⟩

end

end P0EFTJanusLatticeFourierSaintVenantExactness
end JanusFormal
