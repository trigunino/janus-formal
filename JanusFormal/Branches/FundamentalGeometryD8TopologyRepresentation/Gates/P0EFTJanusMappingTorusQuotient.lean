import Mathlib.Geometry.Manifold.Instances.Quotient
import Mathlib.Topology.Homeomorph.TransferInstance
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusReflectionFixedThroat

namespace JanusFormal
namespace P0EFTJanusMappingTorusQuotient

set_option autoImplicit false

open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- A topological monodromy and a nonzero translation period. -/
structure MappingTorusData (X : Type*) [TopologicalSpace X] where
  monodromy : X ≃ₜ X
  period : ℝ
  period_ne_zero : period ≠ 0

/-- The product cover, packaged so that its action can depend on the data. -/
@[ext] structure MappingTorusCover (data : MappingTorusData X) where
  fiber : X
  time : ℝ

/-- The packaged cover is topologically the ordinary product. -/
def coverEquivProd (data : MappingTorusData X) : MappingTorusCover data ≃ X × ℝ where
  toFun p := (p.fiber, p.time)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (data : MappingTorusData X) : TopologicalSpace (MappingTorusCover data) :=
  (coverEquivProd data).topologicalSpace

/-- The explicit homeomorphism from the packaged cover to `X × ℝ`. -/
def coverHomeomorphProd (data : MappingTorusData X) :
    MappingTorusCover data ≃ₜ X × ℝ :=
  (coverEquivProd data).homeomorph

@[simp] theorem coverHomeomorphProd_apply (data : MappingTorusData X)
    (p : MappingTorusCover data) :
    coverHomeomorphProd data p = (p.fiber, p.time) := rfl

@[simp] theorem coverHomeomorphProd_symm_apply (data : MappingTorusData X)
    (p : X × ℝ) :
    (coverHomeomorphProd data).symm p = ⟨p.1, p.2⟩ := rfl

theorem continuous_fiber (data : MappingTorusData X) :
    Continuous (MappingTorusCover.fiber : MappingTorusCover data → X) :=
  by simpa [Function.comp_def] using
    continuous_fst.comp (coverHomeomorphProd data).continuous

theorem continuous_time (data : MappingTorusData X) :
    Continuous (MappingTorusCover.time : MappingTorusCover data → ℝ) :=
  by simpa [Function.comp_def] using
    continuous_snd.comp (coverHomeomorphProd data).continuous

theorem homeomorph_toEquiv_zpow {Y : Type*} [TopologicalSpace Y]
    (f : Y ≃ₜ Y) (n : ℤ) :
    (f ^ n).toEquiv = f.toEquiv ^ n := by
  induction n using Int.induction_on with
  | zero => rfl
  | succ n ih =>
      rw [zpow_add_one, zpow_add_one]
      change (f ^ (n : ℤ)).toEquiv * f.toEquiv =
        f.toEquiv ^ (n : ℤ) * f.toEquiv
      exact congrArg (fun g ↦ g * f.toEquiv) ih
  | pred n ih =>
      rw [zpow_sub_one, zpow_sub_one]
      change (f ^ (-(n : ℤ))).toEquiv * f.toEquiv⁻¹ =
        f.toEquiv ^ (-(n : ℤ)) * f.toEquiv⁻¹
      exact congrArg (fun g ↦ g * f.toEquiv⁻¹) ih

/-- The combined iterate: monodromy power on `X`, translation on `ℝ`. -/
def mappingTorusVAdd (data : MappingTorusData X) (n : ℤ)
    (p : MappingTorusCover data) : MappingTorusCover data :=
  ⟨(data.monodromy ^ n) p.fiber, p.time + (n : ℝ) * data.period⟩

instance (data : MappingTorusData X) : VAdd ℤ (MappingTorusCover data) :=
  ⟨mappingTorusVAdd data⟩

instance (data : MappingTorusData X) : AddAction ℤ (MappingTorusCover data) where
  zero_vadd p := by
    change mappingTorusVAdd data 0 p = p
    ext <;> simp [mappingTorusVAdd]
  add_vadd m n p := by
    change mappingTorusVAdd data (m + n) p =
      mappingTorusVAdd data m (mappingTorusVAdd data n p)
    ext
    · simp [mappingTorusVAdd, zpow_add]
    · simp [mappingTorusVAdd]
      ring

@[simp] theorem vadd_fiber (data : MappingTorusData X) (n : ℤ)
    (p : MappingTorusCover data) :
    (n +ᵥ p).fiber = (data.monodromy ^ n) p.fiber := rfl

@[simp] theorem vadd_time (data : MappingTorusData X) (n : ℤ)
    (p : MappingTorusCover data) :
    (n +ᵥ p).time = p.time + (n : ℝ) * data.period := rfl

theorem continuous_const_vadd (data : MappingTorusData X) (n : ℤ) :
    Continuous (n +ᵥ · : MappingTorusCover data → MappingTorusCover data) := by
  change Continuous (mappingTorusVAdd data n)
  have hFiber : Continuous (fun p : MappingTorusCover data ↦
      (data.monodromy ^ n) p.fiber) :=
    (data.monodromy ^ n).continuous.comp (continuous_fiber data)
  have hTime : Continuous (fun p : MappingTorusCover data ↦
      p.time + (n : ℝ) * data.period) :=
    (continuous_time data).add continuous_const
  have h := (coverHomeomorphProd data).symm.continuous.comp (hFiber.prodMk hTime)
  exact h.congr fun _ ↦ rfl

instance (data : MappingTorusData X) :
    ContinuousConstVAdd ℤ (MappingTorusCover data) where
  continuous_const_vadd := continuous_const_vadd data

/-- The real translation makes the additive action free. -/
theorem vadd_eq_self_iff (data : MappingTorusData X) (n : ℤ)
    (p : MappingTorusCover data) :
    n +ᵥ p = p ↔ n = 0 := by
  constructor
  · intro h
    have hTime := congrArg MappingTorusCover.time h
    change p.time + (n : ℝ) * data.period = p.time at hTime
    have hProduct : (n : ℝ) * data.period = 0 := by linarith
    have hCast : (n : ℝ) = 0 :=
      (mul_eq_zero.mp hProduct).resolve_right data.period_ne_zero
    exact_mod_cast hCast
  · rintro rfl
    simp

instance (data : MappingTorusData X) : IsCancelVAdd ℤ (MappingTorusCover data) :=
  isCancelVAdd_iff_eq_zero_of_vadd_eq.mpr fun n p h ↦
    (vadd_eq_self_iff data n p).mp h

/-- Proper discontinuity follows solely from bounded real projections of compact sets. -/
instance (data : MappingTorusData X) :
    ProperlyDiscontinuousVAdd ℤ (MappingTorusCover data) where
  finite_disjoint_inter_image {K L} hK hL := by
    have hKBounded : BddAbove ((fun p : MappingTorusCover data ↦ |p.time|) '' K) :=
      hK.bddAbove_image ((continuous_time data).abs.continuousOn)
    have hLBounded : BddAbove ((fun p : MappingTorusCover data ↦ |p.time|) '' L) :=
      hL.bddAbove_image ((continuous_time data).abs.continuousOn)
    rcases hKBounded with ⟨boundK, hBoundK⟩
    rcases hLBounded with ⟨boundL, hBoundL⟩
    obtain ⟨N : ℕ, hN⟩ :=
      exists_nat_gt ((|boundK| + |boundL|) / |data.period|)
    refine (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset ?_
    intro n hn
    rcases hn with ⟨q, ⟨p, hpK, rfl⟩, hqL⟩
    have hpBound : |p.time| ≤ boundK :=
      hBoundK (mem_image_of_mem _ hpK)
    have hqBound : |(n +ᵥ p).time| ≤ boundL :=
      hBoundL (mem_image_of_mem _ hqL)
    have hTranslate : |(n : ℝ) * data.period| ≤ |boundK| + |boundL| := by
      calc
        |(n : ℝ) * data.period| = |(n +ᵥ p).time - p.time| := by
          rw [vadd_time]
          congr 2
          ring
        _ ≤ |(n +ᵥ p).time| + |p.time| := abs_sub _ _
        _ ≤ boundL + boundK := add_le_add hqBound hpBound
        _ ≤ |boundK| + |boundL| := by
          linarith [le_abs_self boundK, le_abs_self boundL]
    have hPeriodPositive : 0 < |data.period| := abs_pos.mpr data.period_ne_zero
    have hnAbsMul : |(n : ℝ)| * |data.period| ≤ |boundK| + |boundL| := by
      simpa [abs_mul] using hTranslate
    have hnAbsLe : |(n : ℝ)| ≤ (|boundK| + |boundL|) / |data.period| :=
      (le_div_iff₀ hPeriodPositive).2 hnAbsMul
    have hnAbsLt : |(n : ℝ)| < (N : ℝ) := hnAbsLe.trans_lt hN
    have hnInterval : -(N : ℝ) < (n : ℝ) ∧ (n : ℝ) < (N : ℝ) :=
      (abs_lt).mp hnAbsLt
    constructor
    · exact_mod_cast hnInterval.1.le
    · exact_mod_cast hnInterval.2.le

instance (data : MappingTorusData X) [T2Space X] :
    T2Space (MappingTorusCover data) :=
  (coverHomeomorphProd data).symm.t2Space

instance (data : MappingTorusData X) [LocallyCompactSpace X] :
    LocallyCompactSpace (MappingTorusCover data) :=
  (coverHomeomorphProd data).locallyCompactSpace_iff.mpr inferInstance

instance (data : MappingTorusData X) [SecondCountableTopology X] :
    SecondCountableTopology (MappingTorusCover data) :=
  (coverHomeomorphProd data).secondCountableTopology

/-- The effective mapping torus: the orbit quotient of `X × ℝ` by the combined action. -/
abbrev MappingTorus (data : MappingTorusData X) :=
  AddAction.orbitRel.Quotient ℤ (MappingTorusCover data)

/-- Quotient projection to the effective mapping torus. -/
abbrev mappingTorusMk (data : MappingTorusData X) :
    MappingTorusCover data → MappingTorus data :=
  Quotient.mk (AddAction.orbitRel ℤ (MappingTorusCover data))

theorem mappingTorusMk_surjective (data : MappingTorusData X) :
    Function.Surjective (mappingTorusMk data) :=
  Quotient.mk_surjective

/-- Two cover points define the same quotient point exactly when one integer iterate joins them. -/
theorem mappingTorusMk_eq_iff_exists_vadd (data : MappingTorusData X)
    (p q : MappingTorusCover data) :
    mappingTorusMk data p = mappingTorusMk data q ↔
      ∃ n : ℤ, n +ᵥ q = p := by
  rw [Quotient.eq'', AddAction.orbitRel_apply, AddAction.mem_orbit_iff]

/-- Because the translation is nonzero, the joining iterate is unique. -/
theorem mappingTorusMk_eq_iff_existsUnique_vadd (data : MappingTorusData X)
    (p q : MappingTorusCover data) :
    mappingTorusMk data p = mappingTorusMk data q ↔
      ∃! n : ℤ, n +ᵥ q = p := by
  rw [mappingTorusMk_eq_iff_exists_vadd]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, hn, ?_⟩
    intro m hm
    exact IsCancelVAdd.right_cancel m n q (hm.trans hn.symm)
  · rintro ⟨n, hn, -⟩
    exact ⟨n, hn⟩

/-- The quotient projection is a quotient covering map. -/
theorem mappingTorusMk_isAddQuotientCoveringMap
    (data : MappingTorusData X) [T2Space X] [LocallyCompactSpace X] :
    IsAddQuotientCoveringMap (mappingTorusMk data) ℤ :=
  isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd

/-- In particular the projection `X × ℝ → MappingTorus` is a covering map. -/
theorem mappingTorusMk_isCoveringMap
    (data : MappingTorusData X) [T2Space X] [LocallyCompactSpace X] :
    IsCoveringMap (mappingTorusMk data) :=
  (mappingTorusMk_isAddQuotientCoveringMap data).isCoveringMap

/-- The quotient is Hausdorff under the standard locally compact Hausdorff hypotheses on `X`. -/
theorem mappingTorus_t2Space
    (data : MappingTorusData X) [T2Space X] [LocallyCompactSpace X] :
    T2Space (MappingTorus data) :=
  inferInstance

noncomputable instance mappingTorusCoverChartedSpace
    (data : MappingTorusData X) {H : Type*} [TopologicalSpace H]
    [ChartedSpace H (X × ℝ)] :
    ChartedSpace H (MappingTorusCover data) :=
  (coverHomeomorphProd data).symm.isLocalHomeomorph.chartedSpace
    (coverHomeomorphProd data).symm.surjective

/-- Mathlib transports charts through the covering quotient; no smoothness claim is made here. -/
theorem mappingTorus_has_chartedSpace
    (data : MappingTorusData X) [T2Space X] [LocallyCompactSpace X]
    {H : Type*} [TopologicalSpace H] [ChartedSpace H (X × ℝ)] :
    Nonempty (ChartedSpace H (MappingTorus data)) :=
  ⟨inferInstance⟩

section ReflectedSphere

open P0EFTJanusReflectionFixedThroat

/-- The algebraic unit three-sphere, now used as a topological subtype. -/
abbrev UnitThreeSphere := {x : R4Point // OnUnitThreeSphere x}

/-- The equatorial fixed two-sphere, as a topological subtype. -/
abbrev EquatorialTwoSphere := {x : R4Point // OnEquatorialTwoSphere x}

theorem continuous_reflectPoint : Continuous reflectPoint := by
  apply continuous_pi
  intro i
  have hEval : Continuous (fun x : R4Point ↦ x i) := continuous_apply i
  by_cases hi : i = 0
  · simpa [reflectPoint, hi] using hEval.neg
  · simpa [reflectPoint, hi] using hEval

/-- Reflection is an explicit homeomorphism of ambient `ℝ⁴`. -/
def reflectPointHomeomorph : R4Point ≃ₜ R4Point where
  toFun := reflectPoint
  invFun := reflectPoint
  left_inv := reflect_point_involutive
  right_inv := reflect_point_involutive
  continuous_toFun := continuous_reflectPoint
  continuous_invFun := continuous_reflectPoint

/-- Restriction of the coordinate reflection to the unit three-sphere. -/
def sphereReflection : UnitThreeSphere ≃ₜ UnitThreeSphere where
  toFun x := ⟨reflectPoint x.1, reflection_preserves_unit_three_sphere x.1 x.2⟩
  invFun x := ⟨reflectPoint x.1, reflection_preserves_unit_three_sphere x.1 x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact reflect_point_involutive x.1
  right_inv x := by
    apply Subtype.ext
    exact reflect_point_involutive x.1
  continuous_toFun :=
    (continuous_reflectPoint.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_reflectPoint.comp continuous_subtype_val).subtype_mk _

/-- Inclusion of the fixed equator into the unit sphere. -/
def equatorialSphereInclusion : EquatorialTwoSphere → UnitThreeSphere :=
  fun x ↦ ⟨x.1, x.2.1⟩

theorem continuous_equatorialSphereInclusion :
    Continuous equatorialSphereInclusion :=
  continuous_subtype_val.subtype_mk _

theorem equatorialSphereInclusion_injective :
    Function.Injective equatorialSphereInclusion := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : UnitThreeSphere ↦ z.1) h

@[simp] theorem sphereReflection_fixes_equator (x : EquatorialTwoSphere) :
    sphereReflection (equatorialSphereInclusion x) = equatorialSphereInclusion x := by
  apply Subtype.ext
  exact (reflect_point_fixed_iff_first_coordinate_zero x.1).mpr x.2.2

theorem sphereReflection_zpow_fixes_equator (n : ℤ) (x : EquatorialTwoSphere) :
    (sphereReflection ^ n) (equatorialSphereInclusion x) =
      equatorialSphereInclusion x := by
  rw [show (sphereReflection ^ n) (equatorialSphereInclusion x) =
      (sphereReflection ^ n).toEquiv (equatorialSphereInclusion x) from rfl,
    homeomorph_toEquiv_zpow]
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
    (sphereReflection_fixes_equator x) n

/-- Mapping-torus data for reflection of the unit three-sphere. -/
def reflectedSphereData (period : ℝ) (hPeriod : period ≠ 0) :
    MappingTorusData UnitThreeSphere where
  monodromy := sphereReflection
  period := period
  period_ne_zero := hPeriod

/-- On the fixed equator the monodromy is the identity. -/
def fixedEquatorData (period : ℝ) (hPeriod : period ≠ 0) :
    MappingTorusData EquatorialTwoSphere where
  monodromy := Homeomorph.refl EquatorialTwoSphere
  period := period
  period_ne_zero := hPeriod

/-- Equivariant inclusion of the fixed-equator cover into the reflected-sphere cover. -/
def fixedThroatCoverInclusion (period : ℝ) (hPeriod : period ≠ 0) :
    MappingTorusCover (fixedEquatorData period hPeriod) →
      MappingTorusCover (reflectedSphereData period hPeriod) :=
  fun p ↦ ⟨equatorialSphereInclusion p.fiber, p.time⟩

theorem continuous_fixedThroatCoverInclusion (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (fixedThroatCoverInclusion period hPeriod) := by
  have hFiber : Continuous (fun p : MappingTorusCover (fixedEquatorData period hPeriod) ↦
      equatorialSphereInclusion p.fiber) :=
    continuous_equatorialSphereInclusion.comp (continuous_fiber _)
  have hTime := continuous_time (fixedEquatorData period hPeriod)
  have h := (coverHomeomorphProd (reflectedSphereData period hPeriod)).symm.continuous.comp
    (hFiber.prodMk hTime)
  exact h.congr fun _ ↦ rfl

theorem fixedThroatCoverInclusion_injective (period : ℝ) (hPeriod : period ≠ 0) :
    Function.Injective (fixedThroatCoverInclusion period hPeriod) := by
  intro p q h
  apply MappingTorusCover.ext
  · exact equatorialSphereInclusion_injective
      (congrArg (fun z : MappingTorusCover (reflectedSphereData period hPeriod) ↦
        z.fiber) h)
  · exact congrArg
      (fun z : MappingTorusCover (reflectedSphereData period hPeriod) ↦ z.time) h

theorem fixedThroatCoverInclusion_equivariant
    (period : ℝ) (hPeriod : period ≠ 0) (n : ℤ)
    (p : MappingTorusCover (fixedEquatorData period hPeriod)) :
    fixedThroatCoverInclusion period hPeriod (n +ᵥ p) =
      n +ᵥ fixedThroatCoverInclusion period hPeriod p := by
  change fixedThroatCoverInclusion period hPeriod
      (mappingTorusVAdd (fixedEquatorData period hPeriod) n p) =
    mappingTorusVAdd (reflectedSphereData period hPeriod) n
      (fixedThroatCoverInclusion period hPeriod p)
  apply MappingTorusCover.ext
  · change equatorialSphereInclusion
        (((Homeomorph.refl EquatorialTwoSphere) ^ n) p.fiber) =
      (sphereReflection ^ n) (equatorialSphereInclusion p.fiber)
    have hRefl : ((Homeomorph.refl EquatorialTwoSphere) ^ n) p.fiber = p.fiber := by
      rw [show ((Homeomorph.refl EquatorialTwoSphere) ^ n) p.fiber =
          ((Homeomorph.refl EquatorialTwoSphere) ^ n).toEquiv p.fiber from rfl,
        homeomorph_toEquiv_zpow]
      rw [show (Homeomorph.refl EquatorialTwoSphere).toEquiv = 1 from rfl,
        one_zpow]
      rfl
    rw [hRefl]
    exact (sphereReflection_zpow_fixes_equator n p.fiber).symm
  · simp [fixedThroatCoverInclusion, mappingTorusVAdd, fixedEquatorData,
      reflectedSphereData]

/-- The fixed equator induces an actual map between the two effective orbit quotients. -/
def fixedThroatQuotientInclusion (period : ℝ) (hPeriod : period ≠ 0) :
    MappingTorus (fixedEquatorData period hPeriod) →
      MappingTorus (reflectedSphereData period hPeriod) :=
  Quotient.map (fixedThroatCoverInclusion period hPeriod) fun a b hab ↦ by
    change AddAction.orbitRel ℤ
      (MappingTorusCover (fixedEquatorData period hPeriod)) a b at hab
    change AddAction.orbitRel ℤ
      (MappingTorusCover (reflectedSphereData period hPeriod))
      (fixedThroatCoverInclusion period hPeriod a)
      (fixedThroatCoverInclusion period hPeriod b)
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hab ⊢
    rcases hab with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← fixedThroatCoverInclusion_equivariant]
    exact congrArg (fixedThroatCoverInclusion period hPeriod) hn

@[simp] theorem fixedThroatQuotientInclusion_mk
    (period : ℝ) (hPeriod : period ≠ 0)
    (p : MappingTorusCover (fixedEquatorData period hPeriod)) :
    fixedThroatQuotientInclusion period hPeriod (mappingTorusMk _ p) =
      mappingTorusMk _ (fixedThroatCoverInclusion period hPeriod p) :=
  rfl

theorem continuous_fixedThroatQuotientInclusion
    (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (fixedThroatQuotientInclusion period hPeriod) := by
  apply (continuous_quotient_mk'.comp
    (continuous_fixedThroatCoverInclusion period hPeriod)).quotient_lift

/-- The quotient map induced by the fixed equator is injective. -/
theorem fixedThroatQuotientInclusion_injective
    (period : ℝ) (hPeriod : period ≠ 0) :
    Function.Injective (fixedThroatQuotientInclusion period hPeriod) := by
  intro a
  refine Quotient.inductionOn a ?_
  intro p b
  refine Quotient.inductionOn b ?_
  intro q h
  apply Quotient.sound
  change AddAction.orbitRel ℤ
    (MappingTorusCover (fixedEquatorData period hPeriod)) p q
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  rw [fixedThroatQuotientInclusion_mk, fixedThroatQuotientInclusion_mk,
    mappingTorusMk_eq_iff_exists_vadd] at h
  rcases h with ⟨n, hn⟩
  refine ⟨n, fixedThroatCoverInclusion_injective period hPeriod ?_⟩
  rw [fixedThroatCoverInclusion_equivariant]
  exact hn

end ReflectedSphere

end P0EFTJanusMappingTorusQuotient
end JanusFormal
