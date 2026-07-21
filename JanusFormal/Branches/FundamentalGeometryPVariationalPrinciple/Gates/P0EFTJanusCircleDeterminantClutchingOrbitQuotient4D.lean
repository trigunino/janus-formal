import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleDeterminantTopologicalBundle
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Actual orbit quotient for the circle determinant clutching

The total space is the quotient of `ℝ × ℂ` by integer translation together
with the inverse power of the exact large-gauge determinant monodromy.  This
is the genuine clutching quotient; it is not defined as a trivial bundle.
-/

namespace JanusFormal
namespace P0EFTJanusCircleDeterminantClutchingOrbitQuotient4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleBoundedTransformSpectralFlow
open P0EFTJanusCircleDeterminantLineFamily
open P0EFTJanusCircleDeterminantTopologicalBundle
open Bundle

/-- Scalar carrying the complex-linear endpoint monodromy. -/
def circleLargeGaugeMonodromyScalar (fold : Fold) : Complex :=
  circleLargeGaugeFrameCoordinateTransition fold 1

theorem circleLargeGaugeMonodromyScalar_ne_zero (fold : Fold) :
    circleLargeGaugeMonodromyScalar fold ≠ 0 := by
  intro hZero
  change circleLargeGaugeFrameCoordinateTransition fold 1 = 0 at hZero
  have hEqual : circleLargeGaugeFrameCoordinateTransition fold 1 =
      circleLargeGaugeFrameCoordinateTransition fold 0 := by
    rw [map_zero]
    exact hZero
  exact one_ne_zero
    ((circleLargeGaugeFrameCoordinateTransition fold).injective hEqual)

/-- Every complex-linear automorphism of the one-dimensional coordinate fiber
is multiplication by its value at one. -/
theorem circleLargeGaugeFrameCoordinateTransition_apply_eq_mul
    (fold : Fold) (scalar : Complex) :
    circleLargeGaugeFrameCoordinateTransition fold scalar =
      scalar * circleLargeGaugeMonodromyScalar fold := by
  calc
    circleLargeGaugeFrameCoordinateTransition fold scalar =
        circleLargeGaugeFrameCoordinateTransition fold (scalar • (1 : Complex)) := by simp
    _ = scalar • circleLargeGaugeFrameCoordinateTransition fold 1 := by
      rw [map_smul]
    _ = scalar * circleLargeGaugeMonodromyScalar fold := by
      rfl

/-- Integer action on the universal-cover total space. -/
def circleDeterminantClutchingTranslate
    (fold : Fold) (winding : Int) (point : Real × Complex) : Real × Complex :=
  (point.1 + winding,
    ((circleLargeGaugeFrameCoordinateTransition fold) ^ (-winding)) point.2)

theorem circleDeterminantClutchingTranslate_continuous
    (fold : Fold) (winding : Int) :
    Continuous (circleDeterminantClutchingTranslate fold winding) := by
  exact (continuous_fst.add continuous_const).prodMk
    ((((circleLargeGaugeFrameCoordinateTransition fold) ^ (-winding))
      |>.toContinuousLinearEquiv).continuous.comp continuous_snd)

@[simp] theorem circleDeterminantClutchingTranslate_zero
    (fold : Fold) (point : Real × Complex) :
    circleDeterminantClutchingTranslate fold 0 point = point := by
  simp [circleDeterminantClutchingTranslate]

theorem circleDeterminantClutchingTranslate_add
    (fold : Fold) (first second : Int) (point : Real × Complex) :
    circleDeterminantClutchingTranslate fold (first + second) point =
      circleDeterminantClutchingTranslate fold first
        (circleDeterminantClutchingTranslate fold second point) := by
  ext
  · simp [circleDeterminantClutchingTranslate]
    ring
  · simp [circleDeterminantClutchingTranslate, neg_add_rev]
    rw [show -second + -first = -first + -second by abel, zpow_add]
    simp only [zpow_neg]
    rfl

/-- Orbit equivalence relation for the actual large-gauge monodromy. -/
def circleDeterminantClutchingSetoid (fold : Fold) : Setoid (Real × Complex) where
  r first second := ∃ winding : Int,
    second = circleDeterminantClutchingTranslate fold winding first
  iseqv := by
    constructor
    · intro point
      exact ⟨0, (circleDeterminantClutchingTranslate_zero fold point).symm⟩
    · intro first second h
      obtain ⟨winding, rfl⟩ := h
      refine ⟨-winding, ?_⟩
      rw [← circleDeterminantClutchingTranslate_add]
      simp
    · intro first second third hFirst hSecond
      obtain ⟨firstWinding, rfl⟩ := hFirst
      obtain ⟨secondWinding, rfl⟩ := hSecond
      refine ⟨secondWinding + firstWinding, ?_⟩
      rw [circleDeterminantClutchingTranslate_add]

/-- Genuine quotient total space of the determinant clutching. -/
abbrev CircleDeterminantClutchingTotal (fold : Fold) :=
  Quotient (circleDeterminantClutchingSetoid fold)

/-- Quotient insertion from universal-cover frame coordinates. -/
def circleDeterminantClutchingMk
    (fold : Fold) (point : Real × Complex) :
    CircleDeterminantClutchingTotal fold :=
  Quotient.mk (circleDeterminantClutchingSetoid fold) point

theorem circleDeterminantClutchingMk_continuous (fold : Fold) :
    Continuous (circleDeterminantClutchingMk fold) :=
  continuous_quotient_mk'

/-- Projection of the clutching quotient to the holonomy circle. -/
def circleDeterminantClutchingBase
    (fold : Fold) : CircleDeterminantClutchingTotal fold → CircleHolonomyQuotient :=
  Quotient.lift (fun point : Real × Complex => (point.1 : AddCircle (1 : Real))) (by
    intro first second h
    obtain ⟨winding, rfl⟩ := h
    simp [circleDeterminantClutchingTranslate])

theorem circleDeterminantClutchingBase_continuous (fold : Fold) :
    Continuous (circleDeterminantClutchingBase fold) := by
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp continuous_fst

@[simp] theorem circleDeterminantClutchingBase_mk
    (fold : Fold) (point : Real × Complex) :
    circleDeterminantClutchingBase fold (circleDeterminantClutchingMk fold point) =
      (point.1 : AddCircle (1 : Real)) := rfl

/-- The two fundamental-domain endpoints are identified by the exact
large-gauge monodromy. -/
theorem circleDeterminantClutchingMk_endpoints
    (fold : Fold) (scalar : Complex) :
    circleDeterminantClutchingMk fold (1, scalar) =
      circleDeterminantClutchingMk fold
        (0, circleLargeGaugeFrameCoordinateTransition fold scalar) := by
  apply Quotient.sound
  refine ⟨(-1 : Int), ?_⟩
  ext
  · norm_num [circleDeterminantClutchingTranslate]
  · simp [circleDeterminantClutchingTranslate]

theorem circleLargeGaugeFrameCoordinateTransition_inv_apply (fold : Fold) (z : Complex) :
    (circleLargeGaugeFrameCoordinateTransition fold)⁻¹ z =
      z * (circleLargeGaugeMonodromyScalar fold)⁻¹ := by
  apply (circleLargeGaugeFrameCoordinateTransition fold).injective
  simp [circleLargeGaugeFrameCoordinateTransition_apply_eq_mul,
    circleLargeGaugeMonodromyScalar_ne_zero]

theorem circleLargeGaugeFrameCoordinateTransition_zpow_apply (fold : Fold) (winding : Int) (z : Complex) :
    ((circleLargeGaugeFrameCoordinateTransition fold) ^ winding) z =
      z * (circleLargeGaugeMonodromyScalar fold) ^ winding := by
  induction winding using Int.induction_on generalizing z with
  | zero => simp
  | succ k ih =>
      rw [zpow_add_one,
        zpow_add_one₀ (circleLargeGaugeMonodromyScalar_ne_zero fold)]
      change (circleLargeGaugeFrameCoordinateTransition fold ^ (k : Int))
        (circleLargeGaugeFrameCoordinateTransition fold z) = _
      rw [circleLargeGaugeFrameCoordinateTransition_apply_eq_mul]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ih (z * circleLargeGaugeMonodromyScalar fold)
  | pred k ih =>
      rw [zpow_sub_one,
        zpow_sub_one₀ (circleLargeGaugeMonodromyScalar_ne_zero fold)]
      change (circleLargeGaugeFrameCoordinateTransition fold ^ (-(k : Int)))
        ((circleLargeGaugeFrameCoordinateTransition fold)⁻¹ z) = _
      rw [circleLargeGaugeFrameCoordinateTransition_inv_apply]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ih (z * (circleLargeGaugeMonodromyScalar fold)⁻¹)

noncomputable def circleDeterminantClutchingGauge (fold : Fold) (x : Real) : Complex :=
  Complex.exp ((x : Complex) * Complex.log
    (circleLargeGaugeMonodromyScalar fold))

theorem gauge_add_int (fold : Fold) (x : Real) (n : Int) :
    circleDeterminantClutchingGauge fold (x + n) = circleDeterminantClutchingGauge fold x *
      (circleLargeGaugeMonodromyScalar fold) ^ n := by
  unfold circleDeterminantClutchingGauge
  rw [show (((x + n : Real) : Complex) *
      Complex.log (circleLargeGaugeMonodromyScalar fold)) =
    (x : Complex) * Complex.log (circleLargeGaugeMonodromyScalar fold) +
      (n : Complex) * Complex.log (circleLargeGaugeMonodromyScalar fold) by
        push_cast
        ring]
  rw [Complex.exp_add, Complex.exp_int_mul,
    Complex.exp_log (circleLargeGaugeMonodromyScalar_ne_zero fold)]

theorem gauge_translate_invariant (fold : Fold) (n : Int)
    (point : Real × Complex) :
    circleDeterminantClutchingGauge fold (circleDeterminantClutchingTranslate fold n point).1 *
        (circleDeterminantClutchingTranslate fold n point).2 =
      circleDeterminantClutchingGauge fold point.1 * point.2 := by
  rw [show (circleDeterminantClutchingTranslate fold n point).1 =
      point.1 + n by rfl, gauge_add_int]
  rw [show (circleDeterminantClutchingTranslate fold n point).2 =
      point.2 * (circleLargeGaugeMonodromyScalar fold) ^ (-n) by
        exact circleLargeGaugeFrameCoordinateTransition_zpow_apply fold (-n) point.2]
  calc
    circleDeterminantClutchingGauge fold point.1 *
          (circleLargeGaugeMonodromyScalar fold) ^ n *
          (point.2 * (circleLargeGaugeMonodromyScalar fold) ^ (-n)) =
        circleDeterminantClutchingGauge fold point.1 * point.2 *
          ((circleLargeGaugeMonodromyScalar fold) ^ n *
            (circleLargeGaugeMonodromyScalar fold) ^ (-n)) := by ring
    _ = circleDeterminantClutchingGauge fold point.1 * point.2 := by
      rw [← zpow_add₀ (circleLargeGaugeMonodromyScalar_ne_zero fold)]
      simp

theorem circleDeterminantClutchingGauge_ne_zero (fold : Fold) (x : Real) :
    circleDeterminantClutchingGauge fold x ≠ 0 := Complex.exp_ne_zero _

noncomputable def circleDeterminantClutchingGaugeHomeomorph (fold : Fold) :
    (Real × Complex) ≃ₜ (Real × Complex) where
  toFun point := (point.1, circleDeterminantClutchingGauge fold point.1 * point.2)
  invFun point := (point.1, (circleDeterminantClutchingGauge fold point.1)⁻¹ * point.2)
  left_inv point := by
    ext
    · rfl
    · simp [circleDeterminantClutchingGauge_ne_zero]
  right_inv point := by
    ext
    · rfl
    · simp [circleDeterminantClutchingGauge_ne_zero]
  continuous_toFun := continuous_fst.prodMk
    ((Complex.continuous_exp.comp
      (Complex.continuous_ofReal.comp continuous_fst |>.mul continuous_const)).mul
        continuous_snd)
  continuous_invFun := continuous_fst.prodMk
    (((Complex.continuous_exp.comp
      (Complex.continuous_ofReal.comp continuous_fst |>.mul continuous_const)).inv₀
        (fun _ => Complex.exp_ne_zero _)).mul continuous_snd)

def circleDeterminantUntwistedProjection (point : Real × Complex) :
    AddCircle (1 : Real) × Complex :=
  Prod.map
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : Real))) id point

theorem clutching_relation_iff_untwisted_kernel (fold : Fold)
    (first second : Real × Complex) :
    circleDeterminantClutchingSetoid fold first second ↔
      Setoid.ker circleDeterminantUntwistedProjection
        (circleDeterminantClutchingGaugeHomeomorph fold first) (circleDeterminantClutchingGaugeHomeomorph fold second) := by
  constructor
  · rintro ⟨n, rfl⟩
    apply Prod.ext
    · simp [circleDeterminantUntwistedProjection, circleDeterminantClutchingGaugeHomeomorph,
        circleDeterminantClutchingTranslate]
    · exact (gauge_translate_invariant fold n first).symm
  · intro h
    have hBase : (first.1 : AddCircle (1 : Real)) =
        (second.1 : AddCircle (1 : Real)) :=
      congrArg Prod.fst h
    rw [QuotientAddGroup.eq_iff_sub_mem,
      AddSubgroup.mem_zmultiples_iff] at hBase
    obtain ⟨n, hn⟩ := hBase
    refine ⟨-n, ?_⟩
    have hFirst :
        (circleDeterminantClutchingTranslate fold (-n) first).1 = second.1 := by
      change first.1 + (-n : Int) = second.1
      have hn' : (n : Real) = first.1 - second.1 := by
        simpa using hn
      push_cast
      linarith
    apply Prod.ext
    · exact hFirst.symm
    · have hCoordinate : circleDeterminantClutchingGauge fold first.1 * first.2 =
          circleDeterminantClutchingGauge fold second.1 * second.2 :=
        congrArg Prod.snd h
      have hInvariant := gauge_translate_invariant fold (-n) first
      have hGauge : circleDeterminantClutchingGauge fold
          (circleDeterminantClutchingTranslate fold (-n) first).1 =
          circleDeterminantClutchingGauge fold second.1 := by rw [hFirst]
      apply (mul_left_cancel₀ (circleDeterminantClutchingGauge_ne_zero fold second.1))
      rw [← hCoordinate, ← hGauge, hInvariant]

def circleDeterminantUntwistedProjectionContinuousMap :
    C(Real × Complex, AddCircle (1 : Real) × Complex) :=
  ⟨circleDeterminantUntwistedProjection,
    (AddCircle.continuous_mk' 1).comp continuous_fst |>.prodMk continuous_snd⟩

theorem circleDeterminantUntwistedProjection_isOpenQuotientMap :
    IsOpenQuotientMap circleDeterminantUntwistedProjection := by
  have h := (QuotientAddGroup.isOpenQuotientMap_mk
    (N := AddSubgroup.zmultiples (1 : Real))).prodMap
      (IsOpenQuotientMap.id : IsOpenQuotientMap (id : Complex → Complex))
  unfold circleDeterminantUntwistedProjection
  exact h

noncomputable def circleDeterminantClutchingProductHomeomorph (fold : Fold) :
    CircleDeterminantClutchingTotal fold ≃ₜ
      (AddCircle (1 : Real) × Complex) :=
  (Homeomorph.Quotient.congr (circleDeterminantClutchingGaugeHomeomorph fold)
    (clutching_relation_iff_untwisted_kernel fold)).trans
      (Topology.IsQuotientMap.homeomorph
        (f := circleDeterminantUntwistedProjectionContinuousMap)
        circleDeterminantUntwistedProjection_isOpenQuotientMap.isQuotientMap)

noncomputable def circleDeterminantQuotientTotalSpaceHomeomorph :
    Bundle.TotalSpace Complex CircleDeterminantQuotientFiber ≃ₜ
      (AddCircle (1 : Real) × Complex) :=
  circleDeterminantQuotientTrivialization.toOpenPartialHomeomorph
    |>.toHomeomorphOfSourceEqUnivTargetEqUniv rfl rfl

noncomputable def circleDeterminantClutchingBundleHomeomorph (fold : Fold) :
    CircleDeterminantClutchingTotal fold ≃ₜ
      Bundle.TotalSpace Complex CircleDeterminantQuotientFiber :=
  (circleDeterminantClutchingProductHomeomorph fold).trans
    circleDeterminantQuotientTotalSpaceHomeomorph.symm

theorem circleDeterminantClutchingProductHomeomorph_mk
    (fold : Fold) (point : Real × Complex) :
    circleDeterminantClutchingProductHomeomorph fold
        (circleDeterminantClutchingMk fold point) =
      ((point.1 : AddCircle (1 : Real)),
        circleDeterminantClutchingGauge fold point.1 * point.2) := by
  change circleDeterminantUntwistedProjection
    (circleDeterminantClutchingGaugeHomeomorph fold point) = _
  rfl

/-- Explicit bundle isomorphism formula in the descended line coordinates. -/
theorem circleDeterminantClutchingBundleHomeomorph_mk
    (fold : Fold) (point : Real × Complex) :
    circleDeterminantClutchingBundleHomeomorph fold
        (circleDeterminantClutchingMk fold point) =
      (Bundle.TotalSpace.mk' (E := CircleDeterminantQuotientFiber) Complex
        (point.1 : AddCircle (1 : Real))
        (circleDeterminantClutchingGauge fold point.1 * point.2) :
          Bundle.TotalSpace Complex CircleDeterminantQuotientFiber) := by
  change Bundle.TotalSpace.mk' (E := CircleDeterminantQuotientFiber) Complex
    (point.1 : AddCircle (1 : Real))
    (circleDeterminantClutchingGauge fold point.1 * point.2) = _
  rfl

/-- The homeomorphism covers the clutching projection, hence is an
isomorphism over the same holonomy circle. -/
theorem circleDeterminantClutchingBundleHomeomorph_proj
    (fold : Fold) (point : CircleDeterminantClutchingTotal fold) :
    (circleDeterminantClutchingBundleHomeomorph fold point).proj =
      circleDeterminantClutchingBase fold point := by
  refine Quotient.inductionOn point ?_
  intro representative
  change (circleDeterminantClutchingBundleHomeomorph fold
      (circleDeterminantClutchingMk fold representative)).proj =
    (representative.1 : AddCircle (1 : Real))
  rw [circleDeterminantClutchingBundleHomeomorph_mk]

/-- Fiber coordinates preserve addition; each clutching fiber is the complex
line carried by the descended bundle. -/
theorem circleDeterminantClutchingBundleHomeomorph_mk_add
    (fold : Fold) (parameter : Real) (first second : Complex) :
    (circleDeterminantClutchingBundleHomeomorph fold
      (circleDeterminantClutchingMk fold (parameter, first + second))).2 =
      (circleDeterminantClutchingBundleHomeomorph fold
        (circleDeterminantClutchingMk fold (parameter, first))).2 +
      (circleDeterminantClutchingBundleHomeomorph fold
        (circleDeterminantClutchingMk fold (parameter, second))).2 := by
  rw [circleDeterminantClutchingBundleHomeomorph_mk,
    circleDeterminantClutchingBundleHomeomorph_mk,
    circleDeterminantClutchingBundleHomeomorph_mk]
  exact mul_add _ _ _

/-- Fiber coordinates preserve complex scalar multiplication. -/
theorem circleDeterminantClutchingBundleHomeomorph_mk_smul
    (fold : Fold) (parameter : Real) (scalar value : Complex) :
    (circleDeterminantClutchingBundleHomeomorph fold
      (circleDeterminantClutchingMk fold (parameter, scalar * value))).2 =
      scalar • (circleDeterminantClutchingBundleHomeomorph fold
        (circleDeterminantClutchingMk fold (parameter, value))).2 := by
  rw [circleDeterminantClutchingBundleHomeomorph_mk,
    circleDeterminantClutchingBundleHomeomorph_mk]
  change circleDeterminantClutchingGauge fold parameter * (scalar * value) =
    scalar * (circleDeterminantClutchingGauge fold parameter * value)
  ring

end


end P0EFTJanusCircleDeterminantClutchingOrbitQuotient4D
end JanusFormal
