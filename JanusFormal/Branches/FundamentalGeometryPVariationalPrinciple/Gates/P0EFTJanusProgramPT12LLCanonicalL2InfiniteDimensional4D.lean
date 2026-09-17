import Mathlib.Topology.NatEmbedding
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Module.Connected
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatVolumeOpenPos4D

/-! An open-positive finite measure on an infinite Hausdorff space has infinite-dimensional L². -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalL2InfiniteDimensional4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal
open scoped ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D

/-- Disjoint positive-measure opens give infinitely many orthogonal L² vectors. -/
theorem l2_not_finiteDimensional_of_openPos
    (X : Type*) [TopologicalSpace X] [T2Space X] [Infinite X]
    [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] [mu.IsOpenPosMeasure] :
    ¬ FiniteDimensional Real (Lp Real (2 : ENNReal) mu) := by
  obtain ⟨U, hInfinite, hOpen, hDisjoint⟩ :=
    exists_seq_infinite_isOpen_pairwise_disjoint X
  have hNonzero (n : Nat) : mu (U n) ≠ 0 :=
    (hOpen n).measure_ne_zero mu (hInfinite n).nonempty
  let v (n : Nat) : Lp Real (2 : ENNReal) mu :=
    indicatorConstLp (2 : ENNReal) (hOpen n).measurableSet
      (measure_ne_top mu (U n)) (1 : Real)
  have hvNorm (n : Nat) : ‖v n‖ ≠ 0 := by
    have hReal : 0 < mu.real (U n) := by
      simpa only [measureReal_def] using
        (ENNReal.toReal_pos (hNonzero n) (measure_ne_top mu (U n)))
    have hNorm := norm_indicatorConstLp
      (p := (2 : ENNReal))
      (hs := (hOpen n).measurableSet)
      (hμs := measure_ne_top mu (U n))
      (c := (1 : Real))
      (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ (∞ : ENNReal))
    change ‖v n‖ = _ at hNorm
    rw [hNorm]
    have hPower : 0 < mu.real (U n) ^ (1 / ((2 : ENNReal).toReal)) :=
      Real.rpow_pos_of_pos hReal _
    exact ne_of_gt (mul_pos (by norm_num : 0 < ‖(1 : Real)‖) hPower)
  have hvInner (i j : Nat) (hij : i ≠ j) :
      inner Real (v i) (v j) = 0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards
      [indicatorConstLp_coeFn
        (p := (2 : ENNReal))
        (hs := (hOpen i).measurableSet)
        (hμs := measure_ne_top mu (U i))
        (c := (1 : Real)),
       indicatorConstLp_coeFn
        (p := (2 : ENNReal))
        (hs := (hOpen j).measurableSet)
        (hμs := measure_ne_top mu (U j))
        (c := (1 : Real))]
      with point hi hj
    change inner Real (v i point) (v j point) = 0
    rw [hi, hj]
    by_cases hPoint : point ∈ U i
    · have hOther : point ∉ U j :=
        (Set.disjoint_left.mp (hDisjoint hij)) hPoint
      simp [Set.indicator_of_mem hPoint, Set.indicator_of_notMem hOther]
    · simp [Set.indicator_of_notMem hPoint]
  let w (n : Nat) : Lp Real (2 : ENNReal) mu :=
    (‖v n‖)⁻¹ • v n
  have hwNorm (n : Nat) : ‖w n‖ = 1 := by
    simp [w, norm_smul, hvNorm n]
  have hwInner (i j : Nat) (hij : i ≠ j) :
      inner Real (w i) (w j) = 0 := by
    simp [w, inner_smul_left, inner_smul_right, hvInner i j hij]
  have hOrthonormal : Orthonormal Real w :=
    ⟨hwNorm, fun i j hij => hwInner i j hij⟩
  intro hFinite
  letI : FiniteDimensional Real (Lp Real (2 : ENNReal) mu) := hFinite
  exact Module.Finite.not_linearIndependent_of_infinite w hOrthonormal.linearIndependent

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

private theorem effectiveThroat_infinite :
    Infinite (EffectiveThroat period hPeriod) := by
  have hRank : 1 < Module.rank Real EuclideanR3 := by
    rw [← Module.finrank_eq_rank]
    norm_num [finrank_euclideanSpace_fin]
  let first : EuclideanR3 := EuclideanSpace.single 0 (1 : Real)
  let second : EuclideanR3 := EuclideanSpace.single 1 (1 : Real)
  have hFirst : first ∈ Metric.sphere (0 : EuclideanR3) 1 := by
      simp [first]
  have hSecond : second ∈ Metric.sphere (0 : EuclideanR3) 1 := by
      simp [second]
  have hDistinct : first ≠ second := by
    intro h
    have hCoordinate := congrArg (fun point : EuclideanR3 => point (0 : Fin 3)) h
    norm_num [first, second, PiLp.single_apply] at hCoordinate
  have hSphere : (Metric.sphere (0 : EuclideanR3) 1).Infinite :=
    (isPreconnected_sphere hRank (0 : EuclideanR3) (1 : Real))
      |>.infinite_of_nontrivial ⟨first, hFirst, second, hSecond, hDistinct⟩
  letI : Infinite StandardEquatorialTwoSphere := hSphere.to_subtype
  letI : Infinite EquatorialTwoSphere :=
    Infinite.of_injective equatorialTwoSphereHomeomorph.symm
      equatorialTwoSphereHomeomorph.symm.injective
  let inclusion : EquatorialTwoSphere → EffectiveThroat period hPeriod :=
    fun point => mappingTorusMk (fixedEquatorData period hPeriod)
      ⟨point, 0⟩
  have hInclusion : Function.Injective inclusion := by
    intro first second hEqual
    obtain ⟨winding, hWinding⟩ :=
      (mappingTorusMk_eq_iff_exists_vadd
        (fixedEquatorData period hPeriod)
        (⟨first, 0⟩ : MappingTorusCover (fixedEquatorData period hPeriod))
        (⟨second, 0⟩ : MappingTorusCover (fixedEquatorData period hPeriod))).1 hEqual
    have hFiber := congrArg
      (fun point : MappingTorusCover (fixedEquatorData period hPeriod) =>
        point.fiber) hWinding
    change ((Homeomorph.refl EquatorialTwoSphere) ^ winding) second = first at hFiber
    have hIdentity :
        ((Homeomorph.refl EquatorialTwoSphere) ^ winding) second = second := by
      rw [show ((Homeomorph.refl EquatorialTwoSphere) ^ winding) second =
        (((Homeomorph.refl EquatorialTwoSphere) ^ winding).toEquiv) second from rfl,
        homeomorph_toEquiv_zpow]
      simp [show (Homeomorph.refl EquatorialTwoSphere).toEquiv = 1 from rfl]
    exact hFiber.symm.trans hIdentity
  exact Infinite.of_injective inclusion hInclusion

/-- The actual canonical throat scalar L² has infinite real dimension. -/
theorem canonicalThroatL2_not_finiteDimensional :
    ¬ FiniteDimensional Real
      (Lp Real (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by
  letI : Infinite (EffectiveThroat period hPeriod) :=
    effectiveThroat_infinite period hPeriod
  letI : Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact l2_not_finiteDimensional_of_openPos
    (EffectiveThroat period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

end
end P0EFTJanusProgramPT12LLCanonicalL2InfiniteDimensional4D
end JanusFormal
