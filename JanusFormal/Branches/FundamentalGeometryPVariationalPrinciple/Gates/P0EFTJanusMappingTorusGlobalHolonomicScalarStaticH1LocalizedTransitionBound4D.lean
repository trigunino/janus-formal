import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FiniteFramePatchClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FixedLocalEnergyReduction4D

/-!
# Localized transition bound for the static scalar H1 bridge

The energy comparison only needs bounded scalar holonomic coefficients for
each partition-localized generator on its own closed support.  It does not
need raw vector continuity for every generator on every patch.

This gate proves that the localized scalar continuity condition supplies a
single uniform coefficient bound, the full quadratic frame control, and the
fixed-local energy domination contract.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1LocalizedTransitionBound4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1UniformEllipticity4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FrameControl4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FiniteFramePatchClosure4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FixedLocalEnergyReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

/-- Holonomic coefficient of one actual partition-localized generator. -/
def finiteLocalizedHolonomicCoefficient
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod)
    (holonomicIndex : Fin 4) : Real :=
  smoothFrameHolonomicCoefficient period hPeriod
    (finiteSmoothTangentFrame period hPeriod) point
      (finiteTangentGeneratorIndexEquivFin period hPeriod index) holonomicIndex

/-- Exact quantitative transition datum after partition localization. -/
structure FiniteLocalizedHolonomicCoefficientBound where
  bound : Real
  bound_nonneg : 0 ≤ bound
  coefficient_sq_le : ∀
      (point : EffectiveQuotient period hPeriod)
      (index : FiniteTangentGeneratorIndex period hPeriod)
      (holonomicIndex : Fin 4),
    finiteLocalizedHolonomicCoefficient period hPeriod point index
        holonomicIndex ^ 2 ≤ bound

/-- Sufficient localized regularity: continuity of each real coefficient only
on the closed support of its own localized generator. -/
structure FiniteLocalizedHolonomicCoefficientContinuity : Prop where
  continuousOn_coefficient : ∀
      (index : FiniteTangentGeneratorIndex period hPeriod)
      (holonomicIndex : Fin 4),
    ContinuousOn
      (fun point : EffectiveQuotient period hPeriod =>
        finiteLocalizedHolonomicCoefficient period hPeriod point index
          holonomicIndex)
      (finiteTangentGeneratorClosedPatch period hPeriod index.1)

/-- The previous all-generators/all-patches regularity contract implies the
localized scalar condition used here. -/
def FiniteSmoothTangentFrameRawPatchContinuity.toLocalizedCoefficientContinuity
    (regularity : FiniteSmoothTangentFrameRawPatchContinuity period hPeriod) :
    FiniteLocalizedHolonomicCoefficientContinuity period hPeriod where
  continuousOn_coefficient index holonomicIndex := by
    simpa [finiteLocalizedHolonomicCoefficient] using
      regularity.coefficient_continuousOn period hPeriod index.1
        (finiteTangentGeneratorIndexEquivFin period hPeriod index)
          holonomicIndex

private theorem finiteTangentGeneratorWeight_eq_zero_of_not_mem
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (hPoint : point ∉ finiteTangentGeneratorClosedPatch period hPeriod patch) :
    finiteTangentGeneratorWeight period hPeriod patch point = 0 := by
  by_contra hWeight
  exact hPoint (subset_closure hWeight)

theorem finiteLocalizedHolonomicCoefficient_eq_zero_of_not_mem
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod)
    (holonomicIndex : Fin 4)
    (hPoint : point ∉
      finiteTangentGeneratorClosedPatch period hPeriod index.1) :
    finiteLocalizedHolonomicCoefficient period hPeriod point index
        holonomicIndex = 0 := by
  have hVector :
      (finiteSmoothTangentFrame period hPeriod).vectorAt point
          (finiteTangentGeneratorIndexEquivFin period hPeriod index) = 0 := by
    rw [finiteSmoothTangentFrame_vectorAt_generator,
      finiteTangentGeneratorWeight_eq_zero_of_not_mem
        period hPeriod index.1 point hPoint, zero_smul]
  unfold finiteLocalizedHolonomicCoefficient smoothFrameHolonomicCoefficient
  rw [hVector]
  refine Fin.cases ?_ (fun spatial => ?_) holonomicIndex
  · rfl
  · rfl

/-- Compactness of the finitely many closed supports upgrades localized
scalar continuity to one global square bound. -/
def FiniteLocalizedHolonomicCoefficientContinuity.toBound
    (regularity : FiniteLocalizedHolonomicCoefficientContinuity
      period hPeriod) :
    FiniteLocalizedHolonomicCoefficientBound period hPeriod := by
  have hPatchBound
      (index : FiniteTangentGeneratorIndex period hPeriod)
      (holonomicIndex : Fin 4) :
      ∃ upper : Real, ∀ point,
        point ∈ finiteTangentGeneratorClosedPatch period hPeriod index.1 →
          ‖finiteLocalizedHolonomicCoefficient period hPeriod point index
            holonomicIndex‖ ≤ upper := by
    rcases (finiteTangentGeneratorClosedPatch_isClosed period hPeriod
        index.1).isCompact.bddAbove_image
          (regularity.continuousOn_coefficient index holonomicIndex).norm with
      ⟨upper, hUpper⟩
    exact ⟨upper, fun point hPoint => hUpper ⟨point, hPoint, rfl⟩⟩
  let upper : FiniteTangentGeneratorIndex period hPeriod → Fin 4 → Real :=
    fun index holonomicIndex => (hPatchBound index holonomicIndex).choose
  let normBound :=
    ∑ index : FiniteTangentGeneratorIndex period hPeriod,
      (∑ holonomicIndex : Fin 4, (|upper index holonomicIndex| + 1))
  have hTermNonneg
      (index : FiniteTangentGeneratorIndex period hPeriod)
      (holonomicIndex : Fin 4) :
      0 ≤ |upper index holonomicIndex| + 1 :=
    add_nonneg (abs_nonneg _) zero_le_one
  have hInnerNonneg (index : FiniteTangentGeneratorIndex period hPeriod) :
      0 ≤ ∑ holonomicIndex : Fin 4,
        (|upper index holonomicIndex| + 1) :=
    Finset.sum_nonneg (s := Finset.univ) fun holonomicIndex _ =>
      hTermNonneg index holonomicIndex
  have hNormBoundNonneg : 0 ≤ normBound := by
    dsimp only [normBound]
    exact Finset.sum_nonneg (s := Finset.univ) fun index _ =>
      hInnerNonneg index
  refine {
    bound := normBound ^ 2
    bound_nonneg := sq_nonneg normBound
    coefficient_sq_le := ?_ }
  intro point index holonomicIndex
  have hCoefficientNorm :
      ‖finiteLocalizedHolonomicCoefficient period hPeriod point index
        holonomicIndex‖ ≤ normBound := by
    by_cases hPoint : point ∈
        finiteTangentGeneratorClosedPatch period hPeriod index.1
    · calc
        _ ≤ upper index holonomicIndex :=
          (hPatchBound index holonomicIndex).choose_spec point hPoint
        _ ≤ |upper index holonomicIndex| + 1 := by
          linarith [le_abs_self (upper index holonomicIndex)]
        _ ≤ ∑ holonomicIndex : Fin 4,
            (|upper index holonomicIndex| + 1) := by
          exact Finset.single_le_sum (s := Finset.univ)
            (fun coordinate _ => hTermNonneg index coordinate)
            (Finset.mem_univ holonomicIndex)
        _ ≤ normBound := by
          dsimp only [normBound]
          exact Finset.single_le_sum (s := Finset.univ)
            (fun generator _ => hInnerNonneg generator)
            (Finset.mem_univ index)
    · rw [finiteLocalizedHolonomicCoefficient_eq_zero_of_not_mem
        period hPeriod point index holonomicIndex hPoint, norm_zero]
      exact hNormBoundNonneg
  simpa [pow_two] using
    (mul_self_le_mul_self (norm_nonneg _) hCoefficientNorm)

private theorem finite_coordinate_map_sq_le
    (count : Nat) (coefficients : Fin count → Fin 4 → Real)
    (bound : Real) (hBound : 0 ≤ bound)
    (hCoefficient : ∀ frameIndex holonomicIndex,
      coefficients frameIndex holonomicIndex ^ 2 ≤ bound) :
    ∀ (value : Real) (covector : Fin 4 → Real),
      ‖(value, fun frameIndex =>
        ∑ holonomicIndex : Fin 4,
          coefficients frameIndex holonomicIndex * covector holonomicIndex)‖ ^ 2 ≤
        (2 + 8 * (count : Real) ^ 2 * bound) *
          (value ^ 2 + ∑ holonomicIndex : Fin 4,
            covector holonomicIndex ^ 2) := by
  intro value covector
  let transformed : Fin count → Real := fun frameIndex =>
    ∑ holonomicIndex : Fin 4,
      coefficients frameIndex holonomicIndex * covector holonomicIndex
  let covectorSquare := ∑ holonomicIndex : Fin 4,
    covector holonomicIndex ^ 2
  let derivativeAbsSum := ∑ frameIndex : Fin count,
    |transformed frameIndex|
  have hCovectorSquare : 0 ≤ covectorSquare :=
    Finset.sum_nonneg fun index _ => sq_nonneg (covector index)
  have hComponent (frameIndex : Fin count) :
      transformed frameIndex ^ 2 ≤ 4 * bound * covectorSquare := by
    have hCauchy :
        transformed frameIndex ^ 2 ≤
          (∑ index : Fin 4, coefficients frameIndex index ^ 2) *
            covectorSquare := by
      simpa [transformed, covectorSquare] using
        (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4))
          (coefficients frameIndex) covector)
    have hCoefficientSum :
        (∑ index : Fin 4, coefficients frameIndex index ^ 2) ≤
          4 * bound := by
      calc
        _ ≤ ∑ _index : Fin 4, bound :=
          Finset.sum_le_sum fun holonomicIndex _ =>
            hCoefficient frameIndex holonomicIndex
        _ = 4 * bound := by simp
    exact hCauchy.trans
      (mul_le_mul_of_nonneg_right hCoefficientSum hCovectorSquare)
  have hComponentSum :
      (∑ frameIndex : Fin count, transformed frameIndex ^ 2) ≤
        (count : Real) * (4 * bound * covectorSquare) := by
    calc
      _ ≤ ∑ _frameIndex : Fin count, 4 * bound * covectorSquare :=
        Finset.sum_le_sum fun frameIndex _ => hComponent frameIndex
      _ = (count : Real) * (4 * bound * covectorSquare) := by simp
  have hAbsCauchy :
      derivativeAbsSum ^ 2 ≤
        (count : Real) *
          ∑ frameIndex : Fin count, transformed frameIndex ^ 2 := by
    dsimp only [derivativeAbsSum]
    simpa [sq_abs] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin count)))
        (f := fun frameIndex => |transformed frameIndex|))
  have hCount : 0 ≤ (count : Real) := Nat.cast_nonneg _
  have hAbsSumSquare :
      derivativeAbsSum ^ 2 ≤
        4 * (count : Real) ^ 2 * bound * covectorSquare := by
    calc
      derivativeAbsSum ^ 2 ≤
          (count : Real) *
            ∑ frameIndex : Fin count, transformed frameIndex ^ 2 := hAbsCauchy
      _ ≤ (count : Real) *
          ((count : Real) * (4 * bound * covectorSquare)) :=
        mul_le_mul_of_nonneg_left hComponentSum hCount
      _ = 4 * (count : Real) ^ 2 * bound * covectorSquare := by ring
  have hDerivativeAbsSum : 0 ≤ derivativeAbsSum :=
    Finset.sum_nonneg fun frameIndex _ => abs_nonneg (transformed frameIndex)
  have hDerivativeNorm : ‖transformed‖ ≤ derivativeAbsSum := by
    apply (pi_norm_le_iff_of_nonneg hDerivativeAbsSum).2
    intro frameIndex
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum
      (fun index _ => abs_nonneg (transformed index))
      (Finset.mem_univ frameIndex)
  have hJetNorm : ‖(value, transformed)‖ ≤ |value| + derivativeAbsSum := by
    rw [Prod.norm_mk]
    apply max_le
    · rw [Real.norm_eq_abs]
      exact le_add_of_nonneg_right hDerivativeAbsSum
    · exact hDerivativeNorm.trans
        (le_add_of_nonneg_left (abs_nonneg value))
  have hJetSquare :
      ‖(value, transformed)‖ ^ 2 ≤
        (|value| + derivativeAbsSum) ^ 2 := by
    simpa [pow_two] using
      (mul_self_le_mul_self (norm_nonneg (value, transformed)) hJetNorm)
  have hAddSquare :
      (|value| + derivativeAbsSum) ^ 2 ≤
        2 * value ^ 2 + 2 * derivativeAbsSum ^ 2 := by
    nlinarith [sq_nonneg (|value| - derivativeAbsSum), sq_abs value]
  let coefficient := 8 * (count : Real) ^ 2 * bound
  have hCoefficientNonneg : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  change ‖(value, transformed)‖ ^ 2 ≤
    (2 + coefficient) * (value ^ 2 + covectorSquare)
  calc
    ‖(value, transformed)‖ ^ 2 ≤
        (|value| + derivativeAbsSum) ^ 2 := hJetSquare
    _ ≤ 2 * value ^ 2 + 2 * derivativeAbsSum ^ 2 := hAddSquare
    _ ≤ 2 * value ^ 2 + coefficient * covectorSquare := by
      apply add_le_add_right
      dsimp only [coefficient]
      nlinarith
    _ ≤ 2 * (value ^ 2 + covectorSquare) +
        coefficient * (value ^ 2 + covectorSquare) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right hCovectorSquare) (by norm_num)
      · exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (sq_nonneg value)) hCoefficientNonneg
    _ = (2 + coefficient) * (value ^ 2 + covectorSquare) := by ring

/-- The localized coefficient bound supplies the full geometric control for
the implemented finite smooth frame. -/
def FiniteLocalizedHolonomicCoefficientBound.toHolonomicFrameControl
    (control : FiniteLocalizedHolonomicCoefficientBound period hPeriod) :
    StaticScalarHolonomicFrameControl period hPeriod
      (finiteSmoothTangentFrame period hPeriod) where
  coefficients point frameIndex holonomicIndex :=
    smoothFrameHolonomicCoefficient period hPeriod
      (finiteSmoothTangentFrame period hPeriod) point frameIndex holonomicIndex
  covector_decomposition point frameIndex covector :=
    smoothFrameHolonomicCoefficient_covector_decomposition period hPeriod
      (finiteSmoothTangentFrame period hPeriod) point frameIndex covector
  constant := 2 +
    8 * ((finiteSmoothTangentFrame period hPeriod).count : Real) ^ 2 *
      control.bound
  constant_nonneg := by
    exact add_nonneg (by norm_num)
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (sq_nonneg
            ((finiteSmoothTangentFrame period hPeriod).count : Real)))
        control.bound_nonneg)
  coordinate_bound point value covector := by
    apply finite_coordinate_map_sq_le
      (finiteSmoothTangentFrame period hPeriod).count
      (fun frameIndex holonomicIndex =>
        smoothFrameHolonomicCoefficient period hPeriod
          (finiteSmoothTangentFrame period hPeriod) point
            frameIndex holonomicIndex)
      control.bound control.bound_nonneg
    intro frameIndex holonomicIndex
    simpa [finiteLocalizedHolonomicCoefficient] using
      control.coefficient_sq_le point
        ((finiteTangentGeneratorIndexEquivFin period hPeriod).symm frameIndex)
          holonomicIndex

/-- The energy-side contract isolated by the fixed-local gate follows from
the localized scalar coefficient bound. -/
def FiniteLocalizedHolonomicCoefficientBound.toEnergyDomination
    (control : FiniteLocalizedHolonomicCoefficientBound period hPeriod)
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    StaticScalarFixedLocalEnergyDomination period hPeriod data := by
  let ellipticity :=
    StaticScalarHolonomicFrameControl.toUniformGraphEllipticity period hPeriod
      data (finiteSmoothTangentFrame period hPeriod)
        (control.toHolonomicFrameControl period hPeriod)
  refine {
    constant := ellipticity.constant
    constant_nonneg := ellipticity.constant_nonneg
    pointwise_bound := ?_ }
  intro field point
  rw [finiteFixedLocalJacobiDensity, Real.sqrt_sq (norm_nonneg _),
    ← smoothFirstJet_norm_eq_finiteFixedLocalFirstJet period hPeriod]
  exact ellipticity.pointwise_bound field point

/-- Thus this sufficient localized scalar continuity hypothesis supplies the
current conditional fixed-local energy comparison. -/
def FiniteLocalizedHolonomicCoefficientContinuity.toEnergyDomination
    (regularity : FiniteLocalizedHolonomicCoefficientContinuity
      period hPeriod)
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    StaticScalarFixedLocalEnergyDomination period hPeriod data :=
  (regularity.toBound period hPeriod).toEnergyDomination period hPeriod data

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1LocalizedTransitionBound4D
end JanusFormal
