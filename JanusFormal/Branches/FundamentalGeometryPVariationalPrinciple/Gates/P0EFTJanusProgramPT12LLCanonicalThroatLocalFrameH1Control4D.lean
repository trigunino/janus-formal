import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalToFiniteFrameH1Control4D
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Local throat-chart derivatives controlled by the canonical LL frame

For every closed finite throat patch, a smooth plateau extends each
unweighted local chart vector to a global smooth tangent section.  Intrinsic
finite-frame reconstruction then expresses its directional derivative in the
canonical LL frame and gives a uniform chartwise first-derivative bound.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalThroatLocalFrameH1Control4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff BigOperators Topology
open Bundle Filter Set
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

private abbrev TangentFiber
    (point : EffectiveThroat period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

/-- Smooth tangent sections used to extend one local chart vector. -/
abbrev FiniteThroatGeneratorSmoothTangentSection :=
  ContMDiffSection throatCoverModelWithCorners ThroatCoverCoordinates ∞
    (TangentFiber period hPeriod)

private abbrev CanonicalFrame :=
  canonicalDivergenceFreeLLFrame period hPeriod

private def finiteThroatGeneratorPlateauOpen
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Set (EffectiveThroat period hPeriod) :=
  Classical.choose
    (normal_exists_closure_subset
      (finiteThroatGeneratorClosedPatch_isClosed period hPeriod patch)
      (finiteThroatGeneratorOpenPatch_isOpen period hPeriod patch)
      (finiteThroatGeneratorClosedPatch_subset_openPatch
        period hPeriod patch))

private theorem finiteThroatGeneratorPlateauOpen_isOpen
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    IsOpen (finiteThroatGeneratorPlateauOpen period hPeriod patch) :=
  (Classical.choose_spec
    (normal_exists_closure_subset
      (finiteThroatGeneratorClosedPatch_isClosed period hPeriod patch)
      (finiteThroatGeneratorOpenPatch_isOpen period hPeriod patch)
      (finiteThroatGeneratorClosedPatch_subset_openPatch
        period hPeriod patch))).1

private theorem finiteThroatGeneratorClosedPatch_subset_plateauOpen
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    finiteThroatGeneratorClosedPatch period hPeriod patch ⊆
      finiteThroatGeneratorPlateauOpen period hPeriod patch :=
  (Classical.choose_spec
    (normal_exists_closure_subset
      (finiteThroatGeneratorClosedPatch_isClosed period hPeriod patch)
      (finiteThroatGeneratorOpenPatch_isOpen period hPeriod patch)
      (finiteThroatGeneratorClosedPatch_subset_openPatch
        period hPeriod patch))).2.1

private theorem finiteThroatGeneratorPlateauOpen_closure_subset
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    closure (finiteThroatGeneratorPlateauOpen period hPeriod patch) ⊆
      finiteThroatGeneratorOpenPatch period hPeriod patch :=
  (Classical.choose_spec
    (normal_exists_closure_subset
      (finiteThroatGeneratorClosedPatch_isClosed period hPeriod patch)
      (finiteThroatGeneratorOpenPatch_isOpen period hPeriod patch)
      (finiteThroatGeneratorClosedPatch_subset_openPatch
        period hPeriod patch))).2.2

private theorem exists_finiteThroatGeneratorPlateau
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    ∃ cutoff : SmoothThroatField period hPeriod Real,
      (∀ᶠ point in 𝓝ˢ
          (finiteThroatGeneratorClosedPatch period hPeriod patch),
        cutoff point = 1) ∧
      tsupport cutoff.toFun ⊆
        finiteThroatGeneratorOpenPatch period hPeriod patch := by
  have hInterior :
      finiteThroatGeneratorClosedPatch period hPeriod patch ⊆
        interior
          (closure (finiteThroatGeneratorPlateauOpen period hPeriod patch)) :=
    (finiteThroatGeneratorClosedPatch_subset_plateauOpen
      period hPeriod patch).trans
      (finiteThroatGeneratorPlateauOpen_isOpen
        period hPeriod patch).subset_interior_closure
  obtain ⟨cutoff, hOne, hZero, _hRange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      throatCoverModelWithCorners
      (finiteThroatGeneratorClosedPatch_isClosed period hPeriod patch)
      hInterior (n := (⊤ : ℕ∞))
  let smoothCutoff : SmoothThroatField period hPeriod Real :=
    { toFun := cutoff
      contMDiff_toFun := cutoff.contMDiff }
  refine ⟨smoothCutoff, hOne, ?_⟩
  have hSupport : Function.support smoothCutoff.toFun ⊆
      closure (finiteThroatGeneratorPlateauOpen period hPeriod patch) := by
    intro point hPoint
    by_contra hOutside
    exact hPoint (hZero point hOutside)
  exact (closure_minimal hSupport isClosed_closure).trans
    (finiteThroatGeneratorPlateauOpen_closure_subset
      period hPeriod patch)

/-- A smooth plateau equal to one around the closed patch and supported
inside its open chart. -/
def finiteThroatGeneratorPlateau
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    SmoothThroatField period hPeriod Real :=
  Classical.choose
    (exists_finiteThroatGeneratorPlateau period hPeriod patch)

theorem finiteThroatGeneratorPlateau_eq_one
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hPoint : point ∈
      finiteThroatGeneratorClosedPatch period hPeriod patch) :
    finiteThroatGeneratorPlateau period hPeriod patch point = 1 :=
  (Classical.choose_spec
    (exists_finiteThroatGeneratorPlateau period hPeriod patch)).1.self_of_nhdsSet
      point hPoint

theorem finiteThroatGeneratorPlateau_tsupport_subset
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    tsupport
        (finiteThroatGeneratorPlateau period hPeriod patch).toFun ⊆
      finiteThroatGeneratorOpenPatch period hPeriod patch :=
  (Classical.choose_spec
    (exists_finiteThroatGeneratorPlateau period hPeriod patch)).2

/-- Global smooth extension of an unweighted local chart-frame vector. -/
def finiteThroatGeneratorExtendedLocalVector
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex) :
    FiniteThroatGeneratorSmoothTangentSection period hPeriod where
  toFun point :=
    finiteThroatGeneratorPlateau period hPeriod patch point •
      finiteThroatGeneratorLocalVector
        period hPeriod patch basisIndex point
  contMDiff_toFun := by
    exact ContMDiffOn.smul_section_of_tsupport
      ((finiteThroatGeneratorPlateau
        period hPeriod patch).contMDiff_toFun.contMDiffOn)
      (finiteThroatGeneratorOpenPatch_isOpen period hPeriod patch)
      (finiteThroatGeneratorPlateau_tsupport_subset
        period hPeriod patch)
      ((trivializationAt ThroatCoverCoordinates
          (TangentFiber period hPeriod) patch.1).contMDiffOn_localFrame_baseSet
        (n := ∞) (finiteThroatGeneratorModelBasis) basisIndex)

@[simp]
theorem finiteThroatGeneratorExtendedLocalVector_apply
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (point : EffectiveThroat period hPeriod) :
    finiteThroatGeneratorExtendedLocalVector
        period hPeriod patch basisIndex point =
      finiteThroatGeneratorPlateau period hPeriod patch point •
        finiteThroatGeneratorLocalVector
          period hPeriod patch basisIndex point :=
  rfl

theorem finiteThroatGeneratorExtendedLocalVector_eq_local
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (point : EffectiveThroat period hPeriod)
    (hPoint : point ∈
      finiteThroatGeneratorClosedPatch period hPeriod patch) :
    finiteThroatGeneratorExtendedLocalVector
        period hPeriod patch basisIndex point =
      finiteThroatGeneratorLocalVector
        period hPeriod patch basisIndex point := by
  rw [finiteThroatGeneratorExtendedLocalVector_apply,
    finiteThroatGeneratorPlateau_eq_one period hPeriod patch point hPoint,
    one_smul]

/-- Smooth canonical-frame coefficient of one plateau-extended local vector. -/
def finiteThroatGeneratorCanonicalCoefficient
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (canonicalIndex : Fin (CanonicalFrame period hPeriod).count) :
    SmoothThroatField period hPeriod Real :=
  intrinsicThroatFiniteFrameCoefficient period hPeriod
    (CanonicalFrame period hPeriod)
    (finiteThroatGeneratorExtendedLocalVector
      period hPeriod patch basisIndex)
    canonicalIndex

/-- Exact canonical-frame reconstruction of the extended local vector. -/
theorem finiteThroatGeneratorCanonicalCoefficient_reconstructs
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (point : EffectiveThroat period hPeriod) :
    finiteThroatGeneratorExtendedLocalVector
        period hPeriod patch basisIndex point =
      ∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
        finiteThroatGeneratorCanonicalCoefficient
            period hPeriod patch basisIndex canonicalIndex point •
          (CanonicalFrame period hPeriod).vectorAt point canonicalIndex :=
  intrinsicThroatFiniteFrame_reconstructs period hPeriod
    (CanonicalFrame period hPeriod)
    (finiteThroatGeneratorExtendedLocalVector
      period hPeriod patch basisIndex) point

theorem finiteThroatGeneratorCanonicalCoefficient_reconstructs_local
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (point : EffectiveThroat period hPeriod)
    (hPoint : point ∈
      finiteThroatGeneratorClosedPatch period hPeriod patch) :
    finiteThroatGeneratorLocalVector
        period hPeriod patch basisIndex point =
      ∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
        finiteThroatGeneratorCanonicalCoefficient
            period hPeriod patch basisIndex canonicalIndex point •
          (CanonicalFrame period hPeriod).vectorAt point canonicalIndex := by
  rw [← finiteThroatGeneratorExtendedLocalVector_eq_local
    period hPeriod patch basisIndex point hPoint]
  exact finiteThroatGeneratorCanonicalCoefficient_reconstructs
    period hPeriod patch basisIndex point

universe u

/-- Directional derivative along the plateau-extended local vector. -/
def finiteThroatGeneratorExtendedDerivative
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (point : EffectiveThroat period hPeriod) : Fiber :=
  mvfderiv throatCoverModelWithCorners field.toFun point
    (finiteThroatGeneratorExtendedLocalVector
      period hPeriod patch basisIndex point)

/-- The extended local derivative is the exact coefficient combination of
canonical LL-frame derivatives. -/
theorem finiteThroatGeneratorExtendedDerivative_eq_sum
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (point : EffectiveThroat period hPeriod) :
    finiteThroatGeneratorExtendedDerivative
        period hPeriod Fiber field patch basisIndex point =
      ∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
        finiteThroatGeneratorCanonicalCoefficient
            period hPeriod patch basisIndex canonicalIndex point •
          throatFrameDerivative period hPeriod Fiber
            (CanonicalFrame period hPeriod) field point canonicalIndex := by
  unfold finiteThroatGeneratorExtendedDerivative
  rw [finiteThroatGeneratorCanonicalCoefficient_reconstructs
    period hPeriod patch basisIndex point, map_sum]
  apply Finset.sum_congr rfl
  intro canonicalIndex _
  rw [map_smul, throatFrameDerivative_eq_mvfderiv]

/-- Directional derivative along the unweighted local chart vector. -/
def finiteThroatGeneratorLocalDerivative
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (point : EffectiveThroat period hPeriod) : Fiber :=
  mvfderiv throatCoverModelWithCorners field.toFun point
    (finiteThroatGeneratorLocalVector
      period hPeriod patch basisIndex point)

theorem finiteThroatGeneratorLocalDerivative_eq_extended
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (point : EffectiveThroat period hPeriod)
    (hPoint : point ∈
      finiteThroatGeneratorClosedPatch period hPeriod patch) :
    finiteThroatGeneratorLocalDerivative
        period hPeriod Fiber field patch basisIndex point =
      finiteThroatGeneratorExtendedDerivative
        period hPeriod Fiber field patch basisIndex point := by
  unfold finiteThroatGeneratorLocalDerivative
    finiteThroatGeneratorExtendedDerivative
  rw [finiteThroatGeneratorExtendedLocalVector_eq_local
    period hPeriod patch basisIndex point hPoint]

/-- On the closed patch, this is the derivative in the inverse-chart image
of the fixed model-basis vector. -/
theorem finiteThroatGeneratorLocalDerivative_eq_chartAt
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (point : EffectiveThroat period hPeriod)
    (hPoint : point ∈
      finiteThroatGeneratorClosedPatch period hPeriod patch) :
    finiteThroatGeneratorLocalDerivative
        period hPeriod Fiber field patch basisIndex point =
      mvfderiv throatCoverModelWithCorners field.toFun point
        (mfderivWithin
          (modelWithCornersSelf Real ThroatCoverCoordinates)
          throatCoverModelWithCorners
          (extChartAt throatCoverModelWithCorners patch.1).symm
          (Set.range throatCoverModelWithCorners)
          (extChartAt throatCoverModelWithCorners patch.1 point)
          (finiteThroatGeneratorModelBasisVector basisIndex)) := by
  unfold finiteThroatGeneratorLocalDerivative
  rw [finiteThroatGeneratorLocalVector_eq_chartAt_inverseDerivative
    period hPeriod patch basisIndex point
      (finiteThroatGeneratorClosedPatch_subset_openPatch
        period hPeriod patch hPoint)]

/-- Sum of squared canonical coefficients for all local model directions. -/
def finiteThroatGeneratorCanonicalCoefficientMass
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  ∑ basisIndex : FiniteThroatGeneratorBasisIndex,
    ∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
      ‖finiteThroatGeneratorCanonicalCoefficient
        period hPeriod patch basisIndex canonicalIndex point‖ ^ 2

theorem finiteThroatGeneratorCanonicalCoefficientMass_continuous
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Continuous
      (finiteThroatGeneratorCanonicalCoefficientMass
        period hPeriod patch) := by
  apply continuous_finsetSum
  intro basisIndex _
  apply continuous_finsetSum
  intro canonicalIndex _
  exact ((finiteThroatGeneratorCanonicalCoefficient
    period hPeriod patch basisIndex canonicalIndex).contMDiff_toFun.continuous.norm.pow 2)

theorem finiteThroatGeneratorCanonicalCoefficientMass_nonneg
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    0 ≤ finiteThroatGeneratorCanonicalCoefficientMass
      period hPeriod patch point :=
  Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Compactness bounds the complete coefficient mass for one patch. -/
theorem exists_finiteThroatGeneratorCanonicalCoefficientMass_bound
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    ∃ bound : Real, 0 ≤ bound ∧
      ∀ point : EffectiveThroat period hPeriod,
        finiteThroatGeneratorCanonicalCoefficientMass
          period hPeriod patch point ≤ bound := by
  obtain ⟨upper, hUpper⟩ :=
    isCompact_univ.exists_bound_of_continuousOn
      (finiteThroatGeneratorCanonicalCoefficientMass_continuous
        period hPeriod patch).continuousOn
  refine ⟨max upper 0, le_max_right _ _, ?_⟩
  intro point
  have hNorm := hUpper point (Set.mem_univ point)
  have hAbs :
      |finiteThroatGeneratorCanonicalCoefficientMass
        period hPeriod patch point| ≤ upper := by
    simpa only [Real.norm_eq_abs] using hNorm
  exact (le_abs_self _).trans (hAbs.trans (le_max_left _ _))

private theorem finite_weightedSum_sq_le
    {n : Nat} {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (coefficients : Fin n → Real) (values : Fin n → Fiber) :
    ‖∑ index, coefficients index • values index‖ ^ 2 ≤
      (∑ index, ‖coefficients index‖ ^ 2) *
        ∑ index, ‖values index‖ ^ 2 := by
  have hNorm :
      ‖∑ index, coefficients index • values index‖ ≤
        ∑ index, ‖coefficients index • values index‖ :=
    norm_sum_le _ _
  have hSquare :=
    (sq_le_sq₀ (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 hNorm
  calc
    ‖∑ index, coefficients index • values index‖ ^ 2 ≤
        (∑ index, ‖coefficients index • values index‖) ^ 2 := hSquare
    _ = (∑ index, ‖coefficients index‖ * ‖values index‖) ^ 2 := by
      simp only [norm_smul]
    _ ≤ (∑ index, ‖coefficients index‖ ^ 2) *
          ∑ index, ‖values index‖ ^ 2 := by
      simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun index => ‖coefficients index‖)
          (fun index => ‖values index‖))

/-- The coefficient mass controls all plateau-extended local derivatives. -/
theorem finiteThroatGeneratorExtendedDerivativeEnergy_le_mass
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (patch : FiniteThroatGeneratorPatch period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (∑ basisIndex : FiniteThroatGeneratorBasisIndex,
      ‖finiteThroatGeneratorExtendedDerivative
        period hPeriod LLFieldFiber field patch basisIndex point‖ ^ 2) ≤
      finiteThroatGeneratorCanonicalCoefficientMass
          period hPeriod patch point *
        throatDerivativeEnergy period hPeriod
          (CanonicalFrame period hPeriod) field point := by
  have hOne (basisIndex : FiniteThroatGeneratorBasisIndex) :
      ‖finiteThroatGeneratorExtendedDerivative
        period hPeriod LLFieldFiber field patch basisIndex point‖ ^ 2 ≤
      (∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
        ‖finiteThroatGeneratorCanonicalCoefficient
          period hPeriod patch basisIndex canonicalIndex point‖ ^ 2) *
      ∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
        ‖throatFrameDerivative period hPeriod LLFieldFiber
          (CanonicalFrame period hPeriod) field point canonicalIndex‖ ^ 2 := by
    rw [finiteThroatGeneratorExtendedDerivative_eq_sum
      period hPeriod LLFieldFiber field patch basisIndex point]
    exact finite_weightedSum_sq_le
      (fun canonicalIndex =>
        finiteThroatGeneratorCanonicalCoefficient
          period hPeriod patch basisIndex canonicalIndex point)
      (fun canonicalIndex =>
        throatFrameDerivative period hPeriod LLFieldFiber
          (CanonicalFrame period hPeriod) field point canonicalIndex)
  unfold finiteThroatGeneratorCanonicalCoefficientMass
    throatDerivativeEnergy
  calc
    ∑ basisIndex : FiniteThroatGeneratorBasisIndex,
        ‖finiteThroatGeneratorExtendedDerivative
          period hPeriod LLFieldFiber field patch basisIndex point‖ ^ 2 ≤
      ∑ basisIndex : FiniteThroatGeneratorBasisIndex,
        (∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
          ‖finiteThroatGeneratorCanonicalCoefficient
            period hPeriod patch basisIndex canonicalIndex point‖ ^ 2) *
        ∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
          ‖throatFrameDerivative period hPeriod LLFieldFiber
            (CanonicalFrame period hPeriod) field point canonicalIndex‖ ^ 2 :=
      Finset.sum_le_sum fun basisIndex _ => hOne basisIndex
    _ = (∑ basisIndex : FiniteThroatGeneratorBasisIndex,
          ∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
            ‖finiteThroatGeneratorCanonicalCoefficient
              period hPeriod patch basisIndex canonicalIndex point‖ ^ 2) *
        ∑ canonicalIndex : Fin (CanonicalFrame period hPeriod).count,
          ‖throatFrameDerivative period hPeriod LLFieldFiber
            (CanonicalFrame period hPeriod) field point canonicalIndex‖ ^ 2 := by
      rw [Finset.sum_mul]

/-- Uniform canonical-energy control of every unweighted local chart
derivative on the corresponding closed patch. -/
theorem exists_finiteThroatGeneratorLocalDerivativeEnergy_le_canonical
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ (field : SmoothThroatField period hPeriod LLFieldFiber)
        (point : EffectiveThroat period hPeriod),
        point ∈ finiteThroatGeneratorClosedPatch period hPeriod patch →
        (∑ basisIndex : FiniteThroatGeneratorBasisIndex,
          ‖finiteThroatGeneratorLocalDerivative
            period hPeriod LLFieldFiber field patch basisIndex point‖ ^ 2) ≤
          constant * throatDerivativeEnergy period hPeriod
            (CanonicalFrame period hPeriod) field point := by
  obtain ⟨constant, hConstant, hMass⟩ :=
    exists_finiteThroatGeneratorCanonicalCoefficientMass_bound
      period hPeriod patch
  refine ⟨constant, hConstant, ?_⟩
  intro field point hPoint
  have hEnergy : 0 ≤ throatDerivativeEnergy period hPeriod
      (CanonicalFrame period hPeriod) field point :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    (∑ basisIndex : FiniteThroatGeneratorBasisIndex,
        ‖finiteThroatGeneratorLocalDerivative
          period hPeriod LLFieldFiber field patch basisIndex point‖ ^ 2) =
      ∑ basisIndex : FiniteThroatGeneratorBasisIndex,
        ‖finiteThroatGeneratorExtendedDerivative
          period hPeriod LLFieldFiber field patch basisIndex point‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro basisIndex _
      rw [finiteThroatGeneratorLocalDerivative_eq_extended
        period hPeriod LLFieldFiber field patch basisIndex point hPoint]
    _ ≤ finiteThroatGeneratorCanonicalCoefficientMass
          period hPeriod patch point *
        throatDerivativeEnergy period hPeriod
          (CanonicalFrame period hPeriod) field point :=
      finiteThroatGeneratorExtendedDerivativeEnergy_le_mass
        period hPeriod field patch point
    _ ≤ constant * throatDerivativeEnergy period hPeriod
          (CanonicalFrame period hPeriod) field point :=
      mul_le_mul_of_nonneg_right (hMass point) hEnergy

/-- The same estimate in the inverse-chart directions used by the Euclidean
Rellich patch. -/
theorem exists_finiteThroatGeneratorChartAtDerivativeEnergy_le_canonical
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ (field : SmoothThroatField period hPeriod LLFieldFiber)
        (point : EffectiveThroat period hPeriod),
        point ∈ finiteThroatGeneratorClosedPatch period hPeriod patch →
        (∑ basisIndex : FiniteThroatGeneratorBasisIndex,
          ‖mvfderiv throatCoverModelWithCorners field.toFun point
            (mfderivWithin
              (modelWithCornersSelf Real ThroatCoverCoordinates)
              throatCoverModelWithCorners
              (extChartAt throatCoverModelWithCorners patch.1).symm
              (Set.range throatCoverModelWithCorners)
              (extChartAt throatCoverModelWithCorners patch.1 point)
              (finiteThroatGeneratorModelBasisVector basisIndex))‖ ^ 2) ≤
          constant * throatDerivativeEnergy period hPeriod
            (CanonicalFrame period hPeriod) field point := by
  obtain ⟨constant, hConstant, hLocal⟩ :=
    exists_finiteThroatGeneratorLocalDerivativeEnergy_le_canonical
      period hPeriod patch
  refine ⟨constant, hConstant, ?_⟩
  intro field point hPoint
  calc
    (∑ basisIndex : FiniteThroatGeneratorBasisIndex,
        ‖mvfderiv throatCoverModelWithCorners field.toFun point
          (mfderivWithin
            (modelWithCornersSelf Real ThroatCoverCoordinates)
            throatCoverModelWithCorners
            (extChartAt throatCoverModelWithCorners patch.1).symm
            (Set.range throatCoverModelWithCorners)
            (extChartAt throatCoverModelWithCorners patch.1 point)
            (finiteThroatGeneratorModelBasisVector basisIndex))‖ ^ 2) =
      ∑ basisIndex : FiniteThroatGeneratorBasisIndex,
        ‖finiteThroatGeneratorLocalDerivative
          period hPeriod LLFieldFiber field patch basisIndex point‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro basisIndex _
      rw [finiteThroatGeneratorLocalDerivative_eq_chartAt
        period hPeriod LLFieldFiber field patch basisIndex point hPoint]
    _ ≤ constant * throatDerivativeEnergy period hPeriod
          (CanonicalFrame period hPeriod) field point :=
      hLocal field point hPoint

end
end P0EFTJanusProgramPT12LLCanonicalThroatLocalFrameH1Control4D
end JanusFormal
