import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRootScalarSpectralReduction4D
import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuity of the selected positive-root trace coefficient

The positive spectrum is normalized into the compact cube `[0,1]^4`.
On that cube, the sum of scalar square roots is constant on the fibres of
the four elementary symmetric coefficients.  Compact-to-Hausdorff quotient
descent therefore makes that sum continuous as a function of the
coefficients.  Undoing the normalization closes continuity of the last root
coefficient, and hence of all four characteristic coefficients.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRootTraceContinuity4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology BigOperators
open Polynomial
open Topology
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableRootGluing4D
open P0EFTJanusPositiveDiagonalizableRootCoefficientRegularity4D
open P0EFTJanusPositiveRootScalarSpectralReduction4D

abbrev Spectrum4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Spectrum4

/-- The four nonleading coefficients of the monic polynomial with the given
four roots. -/
def spectrumCoefficients (spectrum : Spectrum4) : Fin 4 → Real :=
  ![
    spectrum 0 * spectrum 1 * spectrum 2 * spectrum 3,
    -(spectrum 0 * spectrum 1 * spectrum 2 +
      spectrum 0 * spectrum 1 * spectrum 3 +
      spectrum 0 * spectrum 2 * spectrum 3 +
      spectrum 1 * spectrum 2 * spectrum 3),
    spectrum 0 * spectrum 1 + spectrum 0 * spectrum 2 +
      spectrum 0 * spectrum 3 + spectrum 1 * spectrum 2 +
      spectrum 1 * spectrum 3 + spectrum 2 * spectrum 3,
    -(spectrum 0 + spectrum 1 + spectrum 2 + spectrum 3)
  ]

private def monicQuartic (coefficient : Fin 4 → Real) : Real[X] :=
  Polynomial.X ^ 4 + Polynomial.C (coefficient 3) * Polynomial.X ^ 3 +
    Polynomial.C (coefficient 2) * Polynomial.X ^ 2 +
    Polynomial.C (coefficient 1) * Polynomial.X +
    Polynomial.C (coefficient 0)

private theorem diagonal_charpoly_eq_monicQuartic (spectrum : Spectrum4) :
    (Matrix.diagonal spectrum).charpoly =
      monicQuartic (spectrumCoefficients spectrum) := by
  rw [Matrix.charpoly_diagonal, Fin.prod_univ_four]
  simp [monicQuartic, spectrumCoefficients]
  ring

private theorem diagonal_charpoly_roots_eq_spectrum (spectrum : Spectrum4) :
    (Matrix.diagonal spectrum).charpoly.roots =
      Multiset.map spectrum Finset.univ.val := by
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

private theorem diagonal_charpoly_coefficient_eq
    (spectrum : Spectrum4) (index : Fin 4) :
    (Matrix.diagonal spectrum).charpoly.coeff index =
      spectrumCoefficients spectrum index := by
  rw [diagonal_charpoly_eq_monicQuartic]
  fin_cases index <;>
    simp [monicQuartic, spectrumCoefficients, Polynomial.coeff_add,
      Polynomial.coeff_mul_X_pow', Polynomial.coeff_X_pow,
      Polynomial.coeff_C]

private theorem target_coefficients_eq_spectrumCoefficients
    (target : positiveDiagonalizableLocus)
    (data : PositiveDiagonalizableRelativeMatrix)
    (hData : data.target = target.1) :
    positiveTargetCharpolyCoefficients target =
      spectrumCoefficients data.eigenvalue := by
  funext index
  unfold positiveTargetCharpolyCoefficients
  rw [← hData, positiveDiagonalizable_charpoly_eq_diagonal data,
    diagonal_charpoly_coefficient_eq]

/-- Sum of the positive scalar square roots of a spectrum. -/
def spectrumSqrtSum (spectrum : Spectrum4) : Real :=
  ∑ index : Fin 4, Real.sqrt (spectrum index)

private theorem spectrumCoefficients_continuous :
    Continuous spectrumCoefficients := by
  apply continuous_pi
  intro index
  fin_cases index <;> simp [spectrumCoefficients] <;> fun_prop

private theorem spectrumSqrtSum_continuous :
    Continuous spectrumSqrtSum := by
  unfold spectrumSqrtSum
  fun_prop

/-- Compact cube containing every normalized nonnegative spectrum. -/
def unitSpectrumCube : Set Spectrum4 :=
  Set.univ.pi fun _ => Set.Icc (0 : Real) 1

abbrev UnitSpectrumCube := unitSpectrumCube

local instance unitSpectrumCubeCompactSpace : CompactSpace UnitSpectrumCube :=
  isCompact_iff_compactSpace.mp (by
    change IsCompact (Set.univ.pi fun _ : Fin 4 => Set.Icc (0 : Real) 1)
    exact isCompact_univ_pi fun _ => isCompact_Icc)

/-- Coefficient map on the compact normalized-spectrum cube. -/
def unitSpectrumCoefficientMap (spectrum : UnitSpectrumCube) : Fin 4 → Real :=
  spectrumCoefficients spectrum.1

private theorem unitSpectrumCoefficientMap_continuous :
    Continuous unitSpectrumCoefficientMap :=
  spectrumCoefficients_continuous.comp continuous_subtype_val

private theorem spectrumSqrtSum_eq_of_coefficients_eq
    (first second : UnitSpectrumCube)
    (hCoefficients : unitSpectrumCoefficientMap first =
      unitSpectrumCoefficientMap second) :
    spectrumSqrtSum first.1 = spectrumSqrtSum second.1 := by
  have hCharpoly :
      (Matrix.diagonal first.1).charpoly =
        (Matrix.diagonal second.1).charpoly := by
    rw [diagonal_charpoly_eq_monicQuartic,
      diagonal_charpoly_eq_monicQuartic]
    exact congrArg monicQuartic hCoefficients
  have hRoots := congrArg Polynomial.roots hCharpoly
  rw [diagonal_charpoly_roots_eq_spectrum,
    diagonal_charpoly_roots_eq_spectrum] at hRoots
  have hSqrtRoots := congrArg
    (fun values : Multiset Real => (values.map Real.sqrt).sum) hRoots
  simpa [spectrumSqrtSum, Fin.sum_univ_four, add_assoc] using hSqrtRoots

private def unitSpectrumCoefficientRangeMap
    (spectrum : UnitSpectrumCube) :
    Set.range unitSpectrumCoefficientMap :=
  ⟨unitSpectrumCoefficientMap spectrum, spectrum, rfl⟩

/-- The normalized square-root trace descended to symmetric coefficients. -/
def coefficientRangeSqrtSum
    (coefficient : Set.range unitSpectrumCoefficientMap) : Real :=
  spectrumSqrtSum (Classical.choose coefficient.property).1

private theorem coefficientRangeSqrtSum_apply
    (spectrum : UnitSpectrumCube) :
    coefficientRangeSqrtSum (unitSpectrumCoefficientRangeMap spectrum) =
      spectrumSqrtSum spectrum.1 := by
  unfold coefficientRangeSqrtSum unitSpectrumCoefficientRangeMap
  apply spectrumSqrtSum_eq_of_coefficients_eq
  exact (Classical.choose_spec
    (unitSpectrumCoefficientRangeMap spectrum).property)

/-- Compact quotient descent supplies the missing continuity theorem without
ordering the four roots. -/
theorem coefficientRangeSqrtSum_continuous :
    Continuous coefficientRangeSqrtSum := by
  have hSurjective : Function.Surjective unitSpectrumCoefficientRangeMap := by
    intro coefficient
    obtain ⟨spectrum, hSpectrum⟩ := coefficient.property
    refine ⟨spectrum, ?_⟩
    exact Subtype.ext hSpectrum
  have hContinuous : Continuous unitSpectrumCoefficientRangeMap :=
    unitSpectrumCoefficientMap_continuous.subtype_mk _
  have hQuotient : IsQuotientMap unitSpectrumCoefficientRangeMap :=
    IsQuotientMap.of_surjective_continuous hSurjective hContinuous
  rw [hQuotient.continuous_iff]
  have hSqrtContinuous : Continuous
      (fun spectrum : UnitSpectrumCube => spectrumSqrtSum spectrum.1) :=
    spectrumSqrtSum_continuous.comp continuous_subtype_val
  exact hSqrtContinuous.congr fun spectrum => by
    simpa only [Function.comp_apply] using
      (coefficientRangeSqrtSum_apply spectrum).symm

/-- Positive normalization scale, equal to one plus the sum of the supplied
positive eigenvalues. -/
def positiveSpectrumNormalizationScale
    (target : positiveDiagonalizableLocus) : Real :=
  1 - positiveTargetCharpolyCoefficients target 3

private theorem positiveSpectrumNormalizationScale_eq
    (target : positiveDiagonalizableLocus)
    (data : PositiveDiagonalizableRelativeMatrix)
    (hData : data.target = target.1) :
    positiveSpectrumNormalizationScale target =
      1 + ∑ index : Fin 4, data.eigenvalue index := by
  rw [positiveSpectrumNormalizationScale,
    target_coefficients_eq_spectrumCoefficients target data hData]
  simp [spectrumCoefficients, Fin.sum_univ_four]
  ring

theorem positiveSpectrumNormalizationScale_pos
    (target : positiveDiagonalizableLocus) :
    0 < positiveSpectrumNormalizationScale target := by
  let data := chosenPositiveDiagonalization target
  rw [positiveSpectrumNormalizationScale_eq target data
    (chosenPositiveDiagonalization_target target)]
  have hSum : 0 < ∑ index : Fin 4, data.eigenvalue index :=
    Finset.sum_pos (fun index _ => data.eigenvalue_pos index)
      Finset.univ_nonempty
  linarith

private theorem positiveSpectrumNormalizationScale_continuous :
    Continuous positiveSpectrumNormalizationScale := by
  unfold positiveSpectrumNormalizationScale
  exact continuous_const.sub
    ((continuous_apply 3).comp positiveTargetCharpolyCoefficients_continuous)

/-- Continuous normalized target coefficients. -/
def normalizedPositiveTargetCoefficients
    (target : positiveDiagonalizableLocus) : Fin 4 → Real :=
  fun index =>
    positiveTargetCharpolyCoefficients target index /
      positiveSpectrumNormalizationScale target ^ (4 - (index : Nat))

private theorem normalizedPositiveTargetCoefficients_continuous :
    Continuous normalizedPositiveTargetCoefficients := by
  apply continuous_pi
  intro index
  exact ((continuous_apply index).comp
    positiveTargetCharpolyCoefficients_continuous).div
      (positiveSpectrumNormalizationScale_continuous.pow _)
      (fun target => pow_ne_zero _
        (positiveSpectrumNormalizationScale_pos target).ne')

private theorem spectrumCoefficients_div
    (spectrum : Spectrum4) (scale : Real) (hScale : scale ≠ 0) :
    spectrumCoefficients (fun index => spectrum index / scale) =
      fun index => spectrumCoefficients spectrum index /
        scale ^ (4 - (index : Nat)) := by
  funext index
  fin_cases index <;> simp [spectrumCoefficients] <;>
    field_simp

private theorem normalizedSpectrum_mem_unitCube
    (target : positiveDiagonalizableLocus)
    (data : PositiveDiagonalizableRelativeMatrix)
    (hData : data.target = target.1) :
    (fun index =>
      data.eigenvalue index / positiveSpectrumNormalizationScale target) ∈
        unitSpectrumCube := by
  intro index _
  rw [positiveSpectrumNormalizationScale_eq target data hData]
  have hScale : 0 < 1 + ∑ coordinate : Fin 4, data.eigenvalue coordinate := by
    have hSum : 0 < ∑ coordinate : Fin 4, data.eigenvalue coordinate :=
      Finset.sum_pos (fun coordinate _ => data.eigenvalue_pos coordinate)
        Finset.univ_nonempty
    linarith
  constructor
  · exact div_nonneg (data.eigenvalue_pos index).le hScale.le
  · apply (div_le_one hScale).2
    have hIndex : data.eigenvalue index ≤
        ∑ coordinate : Fin 4, data.eigenvalue coordinate := by
      exact Finset.single_le_sum
        (fun coordinate _ => (data.eigenvalue_pos coordinate).le)
        (Finset.mem_univ index)
    linarith

private theorem normalizedSpectrum_coefficients_eq
    (target : positiveDiagonalizableLocus)
    (data : PositiveDiagonalizableRelativeMatrix)
    (hData : data.target = target.1) :
    spectrumCoefficients
        (fun index => data.eigenvalue index /
          positiveSpectrumNormalizationScale target) =
      normalizedPositiveTargetCoefficients target := by
  rw [spectrumCoefficients_div _ _
    (positiveSpectrumNormalizationScale_pos target).ne']
  unfold normalizedPositiveTargetCoefficients
  rw [target_coefficients_eq_spectrumCoefficients target data hData]

/-- The normalized coefficient vector lies in the compact coefficient image. -/
def normalizedPositiveTargetCoefficientRange
    (target : positiveDiagonalizableLocus) :
    Set.range unitSpectrumCoefficientMap := by
  let data := chosenPositiveDiagonalization target
  let spectrum : UnitSpectrumCube :=
    ⟨fun index =>
      data.eigenvalue index / positiveSpectrumNormalizationScale target,
      normalizedSpectrum_mem_unitCube target data
        (chosenPositiveDiagonalization_target target)⟩
  refine ⟨normalizedPositiveTargetCoefficients target, spectrum, ?_⟩
  exact normalizedSpectrum_coefficients_eq target data
    (chosenPositiveDiagonalization_target target)

private theorem normalizedPositiveTargetCoefficientRange_continuous :
    Continuous normalizedPositiveTargetCoefficientRange :=
  normalizedPositiveTargetCoefficients_continuous.subtype_mk _

private theorem positiveRoot_coefficient_three_eq_sqrt_sum
    (target : positiveDiagonalizableLocus)
    (data : PositiveDiagonalizableRelativeMatrix)
    (hData : data.target = target.1) :
    positiveRootCharpolyCoefficients target 3 =
      -spectrumSqrtSum data.eigenvalue := by
  have hRoot :
      positiveDiagonalizableGlobalRoot target = positiveSimilarityRoot data :=
    positiveDiagonalizableGlobalRoot_eq_of_presentation target data hData
  have hCharpoly :
      (positiveSimilarityRoot data).charpoly =
        (Matrix.diagonal (positiveSimilarityRootSpectrum data)).charpoly := by
    simpa [positiveSimilarityRootPresentation] using
      positiveDiagonalizable_charpoly_eq_diagonal
        (positiveSimilarityRootPresentation data)
  unfold positiveRootCharpolyCoefficients
  rw [hRoot, hCharpoly, diagonal_charpoly_coefficient_eq]
  simp [spectrumCoefficients, spectrumSqrtSum,
    positiveSimilarityRootSpectrum, Fin.sum_univ_four]

/-- Exact compact-quotient formula for the selected negative trace
coefficient. -/
theorem positiveRootCharpolyCoefficient_three_eq_normalized_sqrt_sum
    (target : positiveDiagonalizableLocus) :
    positiveRootCharpolyCoefficients target 3 =
      -Real.sqrt (positiveSpectrumNormalizationScale target) *
        coefficientRangeSqrtSum
          (normalizedPositiveTargetCoefficientRange target) := by
  let data := chosenPositiveDiagonalization target
  let normalizedSpectrum : UnitSpectrumCube :=
    ⟨fun index =>
      data.eigenvalue index / positiveSpectrumNormalizationScale target,
      normalizedSpectrum_mem_unitCube target data
        (chosenPositiveDiagonalization_target target)⟩
  have hRange :
      normalizedPositiveTargetCoefficientRange target =
        unitSpectrumCoefficientRangeMap normalizedSpectrum := by
    apply Subtype.ext
    exact (normalizedSpectrum_coefficients_eq target data
      (chosenPositiveDiagonalization_target target)).symm
  rw [positiveRoot_coefficient_three_eq_sqrt_sum target data
      (chosenPositiveDiagonalization_target target),
    hRange, coefficientRangeSqrtSum_apply]
  have hScalePos := positiveSpectrumNormalizationScale_pos target
  have hScaleSqrt :
      Real.sqrt (positiveSpectrumNormalizationScale target) ≠ 0 :=
    (Real.sqrt_pos.2 hScalePos).ne'
  simp only [spectrumSqrtSum, normalizedSpectrum, Real.sqrt_div
    (data.eigenvalue_pos _).le]
  simp only [Fin.sum_univ_four]
  field_simp [hScaleSqrt]

/-- Continuity of the last scalar coefficient. -/
theorem positiveRootCharpolyCoefficient_three_continuous :
    Continuous (fun target : positiveDiagonalizableLocus =>
      positiveRootCharpolyCoefficients target 3) := by
  rw [show
      (fun target : positiveDiagonalizableLocus =>
        positiveRootCharpolyCoefficients target 3) =
      fun target =>
        -Real.sqrt (positiveSpectrumNormalizationScale target) *
          coefficientRangeSqrtSum
            (normalizedPositiveTargetCoefficientRange target) from by
        funext target
        exact positiveRootCharpolyCoefficient_three_eq_normalized_sqrt_sum target]
  exact (Real.continuous_sqrt.comp
    positiveSpectrumNormalizationScale_continuous).neg.mul
      (coefficientRangeSqrtSum_continuous.comp
        normalizedPositiveTargetCoefficientRange_continuous)

/-- All four scalar coefficients of the selected positive root are
continuous. -/
theorem positiveRootCharpolyCoefficients_continuous :
    Continuous positiveRootCharpolyCoefficients :=
  positiveRootCharpolyCoefficients_continuous_iff_coefficient_three.2
    positiveRootCharpolyCoefficient_three_continuous

end

end P0EFTJanusPositiveRootTraceContinuity4D
end JanusFormal
