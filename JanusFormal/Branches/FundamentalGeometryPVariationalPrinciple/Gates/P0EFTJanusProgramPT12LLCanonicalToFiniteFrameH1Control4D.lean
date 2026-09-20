import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalFrameH1Control4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatFiniteFrameReconstruction4D

/-! # Control of the finite chart frame by the canonical LL frame -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalToFiniteFrameH1Control4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff BigOperators
open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

private abbrev FiniteFrame :=
  finiteSmoothThroatGeneratingFrame period hPeriod

private abbrev CanonicalFrame :=
  canonicalDivergenceFreeLLFrame period hPeriod

/-- Smooth coefficient expressing one finite chart generator in the
canonical LL frame. -/
def finiteToCanonicalFrameCoefficient
    (finiteIndex : Fin (FiniteFrame period hPeriod).count)
    (canonicalIndex : Fin (CanonicalFrame period hPeriod).count) :
    SmoothThroatField period hPeriod Real :=
  intrinsicThroatFiniteFrameCoefficient period hPeriod
    (CanonicalFrame period hPeriod)
    (smoothThroatFrameVectorSection period hPeriod
      (FiniteFrame period hPeriod) finiteIndex)
    canonicalIndex

universe u

/-- Every derivative in the finite chart frame is the exact smooth linear
combination of derivatives in the canonical LL frame. -/
theorem throatFrameDerivative_finite_eq_sum_canonical
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod)
    (finiteIndex : Fin (FiniteFrame period hPeriod).count) :
    throatFrameDerivative period hPeriod Fiber
        (FiniteFrame period hPeriod) field point finiteIndex =
      ∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
        finiteToCanonicalFrameCoefficient period hPeriod
            finiteIndex canonicalIndex point •
          throatFrameDerivative period hPeriod Fiber
            (CanonicalFrame period hPeriod) field point canonicalIndex := by
  rw [throatFrameDerivative_eq_mvfderiv]
  have hReconstruct :=
    intrinsicThroatFiniteFrame_reconstructs period hPeriod
      (CanonicalFrame period hPeriod)
      (smoothThroatFrameVectorSection period hPeriod
        (FiniteFrame period hPeriod) finiteIndex) point
  rw [smoothThroatFrameVectorSection_apply] at hReconstruct
  rw [hReconstruct, map_sum]
  apply Finset.sum_congr rfl
  intro canonicalIndex _
  rw [map_smul, throatFrameDerivative_eq_mvfderiv]
  rfl

/-- Compactness gives one nonnegative absolute bound for every coefficient
of the finite-to-canonical frame change. -/
theorem exists_finiteToCanonicalFrameCoefficient_uniform_bound :
    ∃ bound : Real, 0 ≤ bound ∧
      ∀ (point : EffectiveThroat period hPeriod)
        (finiteIndex : Fin (FiniteFrame period hPeriod).count)
        (canonicalIndex : Fin (CanonicalFrame period hPeriod).count),
        |finiteToCanonicalFrameCoefficient period hPeriod
          finiteIndex canonicalIndex point| ≤ bound := by
  let localBound :
      Fin (FiniteFrame period hPeriod).count ×
        Fin (CanonicalFrame period hPeriod).count → Real :=
    fun index => Classical.choose
      (isCompact_univ.bddAbove_image
        ((finiteToCanonicalFrameCoefficient period hPeriod
          index.1 index.2).contMDiff_toFun.continuous.norm.continuousOn))
  have hLocal : ∀ (point : EffectiveThroat period hPeriod)
      (finiteIndex : Fin (FiniteFrame period hPeriod).count)
      (canonicalIndex : Fin (CanonicalFrame period hPeriod).count),
      |finiteToCanonicalFrameCoefficient period hPeriod
        finiteIndex canonicalIndex point| ≤
        localBound (finiteIndex, canonicalIndex) := by
    intro point finiteIndex canonicalIndex
    exact Classical.choose_spec
      (isCompact_univ.bddAbove_image
        ((finiteToCanonicalFrameCoefficient period hPeriod
          finiteIndex canonicalIndex).contMDiff_toFun.continuous.norm.continuousOn))
      ⟨point, Set.mem_univ point, rfl⟩
  obtain ⟨upper, hUpper⟩ := Finite.exists_le localBound
  refine ⟨max 0 upper, le_max_left _ _, ?_⟩
  intro point finiteIndex canonicalIndex
  exact (hLocal point finiteIndex canonicalIndex).trans
    ((hUpper (finiteIndex, canonicalIndex)).trans (le_max_right _ _))

private theorem finite_linearCombination_sq_le
    {n : Nat} {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (coefficients : Fin n → Real) (values : Fin n → Fiber)
    (bound : Real) (hBound : 0 ≤ bound)
    (hCoefficient : ∀ index, |coefficients index| ≤ bound) :
    ‖∑ index, coefficients index • values index‖ ^ 2 ≤
      (n : Real) * bound ^ 2 *
        ∑ index, ‖values index‖ ^ 2 := by
  have hNorm :
      ‖∑ index, coefficients index • values index‖ ≤
        bound * ∑ index, ‖values index‖ := by
    calc
      ‖∑ index, coefficients index • values index‖ ≤
          ∑ index, ‖coefficients index • values index‖ :=
        norm_sum_le _ _
      _ ≤ ∑ index, bound * ‖values index‖ := by
        apply Finset.sum_le_sum
        intro index _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          (hCoefficient index) (norm_nonneg _)
      _ = bound * ∑ index, ‖values index‖ := by
        rw [Finset.mul_sum]
  have hSumNorm : 0 ≤ ∑ index, ‖values index‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hSquare :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hBound hSumNorm)).2 hNorm
  have hCauchy :
      (∑ index, ‖values index‖) ^ 2 ≤
        (n : Real) * ∑ index, ‖values index‖ ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun index => ‖values index‖))
  calc
    ‖∑ index, coefficients index • values index‖ ^ 2 ≤
        (bound * ∑ index, ‖values index‖) ^ 2 := hSquare
    _ = bound ^ 2 * (∑ index, ‖values index‖) ^ 2 := by ring
    _ ≤ bound ^ 2 *
        ((n : Real) * ∑ index, ‖values index‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hCauchy (sq_nonneg bound)
    _ = (n : Real) * bound ^ 2 *
        ∑ index, ‖values index‖ ^ 2 := by ring

/-- The actual canonical first-derivative energy uniformly controls the
finite chart-generator derivative energy. -/
theorem exists_finiteFrame_derivativeEnergy_le_canonical :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ (field : SmoothThroatField period hPeriod LLFieldFiber)
        (point : EffectiveThroat period hPeriod),
        throatDerivativeEnergy period hPeriod
            (FiniteFrame period hPeriod) field point ≤
          constant *
            throatDerivativeEnergy period hPeriod
              (CanonicalFrame period hPeriod) field point := by
  obtain ⟨bound, hBound, hCoefficient⟩ :=
    exists_finiteToCanonicalFrameCoefficient_uniform_bound
      period hPeriod
  let constant : Real :=
    ((FiniteFrame period hPeriod).count : Real) *
      ((CanonicalFrame period hPeriod).count : Real) * bound ^ 2
  refine ⟨constant, by positivity, ?_⟩
  intro field point
  have hOne (finiteIndex : Fin (FiniteFrame period hPeriod).count) :
      ‖throatFrameDerivative period hPeriod LLFieldFiber
          (FiniteFrame period hPeriod) field point finiteIndex‖ ^ 2 ≤
        ((CanonicalFrame period hPeriod).count : Real) * bound ^ 2 *
          ∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
            ‖throatFrameDerivative period hPeriod LLFieldFiber
              (CanonicalFrame period hPeriod) field point canonicalIndex‖ ^ 2 := by
    rw [throatFrameDerivative_finite_eq_sum_canonical
      period hPeriod LLFieldFiber field point finiteIndex]
    exact finite_linearCombination_sq_le
      (fun canonicalIndex =>
        finiteToCanonicalFrameCoefficient period hPeriod
          finiteIndex canonicalIndex point)
      (fun canonicalIndex =>
        throatFrameDerivative period hPeriod LLFieldFiber
          (CanonicalFrame period hPeriod) field point canonicalIndex)
      bound hBound (hCoefficient point finiteIndex)
  unfold throatDerivativeEnergy
  calc
    ∑ finiteIndex : Fin (FiniteFrame period hPeriod).count,
        ‖throatFrameDerivative period hPeriod LLFieldFiber
          (FiniteFrame period hPeriod) field point finiteIndex‖ ^ 2 ≤
      ∑ _finiteIndex : Fin (FiniteFrame period hPeriod).count,
        ((CanonicalFrame period hPeriod).count : Real) * bound ^ 2 *
          ∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
            ‖throatFrameDerivative period hPeriod LLFieldFiber
              (CanonicalFrame period hPeriod) field point canonicalIndex‖ ^ 2 :=
      Finset.sum_le_sum fun finiteIndex _ => hOne finiteIndex
    _ = constant *
        ∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
          ‖throatFrameDerivative period hPeriod LLFieldFiber
            (CanonicalFrame period hPeriod) field point canonicalIndex‖ ^ 2 := by
      simp [constant]
      ring

end
end P0EFTJanusProgramPT12LLCanonicalToFiniteFrameH1Control4D
end JanusFormal
