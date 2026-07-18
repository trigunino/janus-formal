import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusQuotient
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusNormalBundleOrientationCover

namespace JanusFormal
namespace P0EFTJanusMappingTorusNormalLine

set_option autoImplicit false

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusNormalBundleOrientationCover

/-- Cover presentation of the normal line over the effective fixed throat. -/
@[ext] structure ThroatNormalCover (period : ℝ) (hPeriod : period ≠ 0) where
  base : MappingTorusCover (fixedEquatorData period hPeriod)
  normal : ℝ

/-- The cover is the product of the fixed-throat cover and the normal coordinate. -/
def throatNormalCoverEquivProd (period : ℝ) (hPeriod : period ≠ 0) :
    ThroatNormalCover period hPeriod ≃
      MappingTorusCover (fixedEquatorData period hPeriod) × ℝ where
  toFun point := (point.base, point.normal)
  invFun point := ⟨point.1, point.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (period : ℝ) (hPeriod : period ≠ 0) :
    TopologicalSpace (ThroatNormalCover period hPeriod) :=
  (throatNormalCoverEquivProd period hPeriod).topologicalSpace

/-- Explicit product homeomorphism for the normal cover. -/
def throatNormalCoverHomeomorphProd (period : ℝ) (hPeriod : period ≠ 0) :
    ThroatNormalCover period hPeriod ≃ₜ
      MappingTorusCover (fixedEquatorData period hPeriod) × ℝ :=
  (throatNormalCoverEquivProd period hPeriod).homeomorph

theorem continuous_base (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (ThroatNormalCover.base :
      ThroatNormalCover period hPeriod →
        MappingTorusCover (fixedEquatorData period hPeriod)) := by
  change Continuous (fun point ↦
    ((throatNormalCoverHomeomorphProd period hPeriod) point).1)
  exact continuous_fst.comp
    (throatNormalCoverHomeomorphProd period hPeriod).continuous

theorem continuous_normal (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (ThroatNormalCover.normal : ThroatNormalCover period hPeriod → ℝ) := by
  change Continuous (fun point ↦
    ((throatNormalCoverHomeomorphProd period hPeriod) point).2)
  exact continuous_snd.comp
    (throatNormalCoverHomeomorphProd period hPeriod).continuous

/-- The deck action combines throat translation with the sign representation. -/
def throatNormalVAdd (period : ℝ) (hPeriod : period ≠ 0) (winding : ℤ)
    (point : ThroatNormalCover period hPeriod) : ThroatNormalCover period hPeriod :=
  { base := winding +ᵥ point.base
    normal := (normalSignRepresentation winding : ℝ) * point.normal }

instance (period : ℝ) (hPeriod : period ≠ 0) :
    VAdd ℤ (ThroatNormalCover period hPeriod) :=
  ⟨throatNormalVAdd period hPeriod⟩

instance (period : ℝ) (hPeriod : period ≠ 0) :
    AddAction ℤ (ThroatNormalCover period hPeriod) where
  zero_vadd point := by
    change throatNormalVAdd period hPeriod 0 point = point
    apply ThroatNormalCover.ext
    · simp [throatNormalVAdd]
    · simp [throatNormalVAdd, normalSignRepresentation]
  add_vadd first second point := by
    change throatNormalVAdd period hPeriod (first + second) point =
      throatNormalVAdd period hPeriod first
        (throatNormalVAdd period hPeriod second point)
    apply ThroatNormalCover.ext
    · simp [throatNormalVAdd, add_vadd]
    · simp [throatNormalVAdd, normal_sign_add]
      ring

@[simp] theorem vadd_base (period : ℝ) (hPeriod : period ≠ 0)
    (winding : ℤ) (point : ThroatNormalCover period hPeriod) :
    (winding +ᵥ point).base = winding +ᵥ point.base := rfl

@[simp] theorem vadd_normal (period : ℝ) (hPeriod : period ≠ 0)
    (winding : ℤ) (point : ThroatNormalCover period hPeriod) :
    (winding +ᵥ point).normal =
      (normalSignRepresentation winding : ℝ) * point.normal := rfl

/-- Freeness of the base translation makes the associated-line action free. -/
instance (period : ℝ) (hPeriod : period ≠ 0) :
    IsCancelVAdd ℤ (ThroatNormalCover period hPeriod) :=
  isCancelVAdd_iff_eq_zero_of_vadd_eq.mpr fun winding point hEq ↦ by
    have hBase := congrArg ThroatNormalCover.base hEq
    exact (vadd_eq_self_iff (fixedEquatorData period hPeriod) winding point.base).mp hBase

theorem continuous_const_vadd (period : ℝ) (hPeriod : period ≠ 0)
    (winding : ℤ) :
    Continuous (winding +ᵥ · :
      ThroatNormalCover period hPeriod → ThroatNormalCover period hPeriod) := by
  have hBase : Continuous (fun point : ThroatNormalCover period hPeriod ↦
      winding +ᵥ point.base) :=
    (P0EFTJanusMappingTorusQuotient.continuous_const_vadd
      (fixedEquatorData period hPeriod) winding).comp
      (continuous_base period hPeriod)
  have hNormal : Continuous (fun point : ThroatNormalCover period hPeriod ↦
      (normalSignRepresentation winding : ℝ) * point.normal) :=
    continuous_const.mul (continuous_normal period hPeriod)
  exact ((throatNormalCoverHomeomorphProd period hPeriod).symm.continuous.comp
    (hBase.prodMk hNormal)).congr fun _ ↦ rfl

instance (period : ℝ) (hPeriod : period ≠ 0) :
    ContinuousConstVAdd ℤ (ThroatNormalCover period hPeriod) where
  continuous_const_vadd := continuous_const_vadd period hPeriod

/-- The actual associated normal line as an orbit quotient. -/
abbrev MappingTorusNormalLine (period : ℝ) (hPeriod : period ≠ 0) :=
  AddAction.orbitRel.Quotient ℤ (ThroatNormalCover period hPeriod)

/-- Quotient projection from the normal-line cover. -/
abbrev normalLineMk (period : ℝ) (hPeriod : period ≠ 0) :
    ThroatNormalCover period hPeriod → MappingTorusNormalLine period hPeriod :=
  Quotient.mk (AddAction.orbitRel ℤ (ThroatNormalCover period hPeriod))

/-- The associated-line projection lands on the same effective fixed-throat quotient. -/
def normalLineProjection (period : ℝ) (hPeriod : period ≠ 0) :
    MappingTorusNormalLine period hPeriod →
      MappingTorus (fixedEquatorData period hPeriod) :=
  Quotient.map ThroatNormalCover.base fun first second hOrbit ↦ by
    change AddAction.orbitRel ℤ (ThroatNormalCover period hPeriod) first second at hOrbit
    change AddAction.orbitRel ℤ
      (MappingTorusCover (fixedEquatorData period hPeriod)) first.base second.base
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
    rcases hOrbit with ⟨winding, hWinding⟩
    exact ⟨winding, congrArg ThroatNormalCover.base hWinding⟩

@[simp] theorem normalLineProjection_mk (period : ℝ) (hPeriod : period ≠ 0)
    (point : ThroatNormalCover period hPeriod) :
    normalLineProjection period hPeriod (normalLineMk period hPeriod point) =
      mappingTorusMk (fixedEquatorData period hPeriod) point.base := rfl

theorem continuous_normalLineProjection (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (normalLineProjection period hPeriod) := by
  apply (continuous_quotient_mk'.comp (continuous_base period hPeriod)).quotient_lift

/-- The zero section is defined on the same quotient, not on a surrogate circle. -/
def normalLineZeroSection (period : ℝ) (hPeriod : period ≠ 0) :
    MappingTorus (fixedEquatorData period hPeriod) →
      MappingTorusNormalLine period hPeriod :=
  Quotient.map (fun base ↦ (⟨base, 0⟩ : ThroatNormalCover period hPeriod))
    fun first second hOrbit ↦ by
      change AddAction.orbitRel ℤ
        (MappingTorusCover (fixedEquatorData period hPeriod)) first second at hOrbit
      change AddAction.orbitRel ℤ (ThroatNormalCover period hPeriod)
        ⟨first, 0⟩ ⟨second, 0⟩
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
      rcases hOrbit with ⟨winding, hWinding⟩
      refine ⟨winding, ?_⟩
      apply ThroatNormalCover.ext
      · change winding +ᵥ second = first
        exact hWinding
      · change (normalSignRepresentation winding : ℝ) * 0 = 0
        ring

@[simp] theorem normalLineZeroSection_mk (period : ℝ) (hPeriod : period ≠ 0)
    (base : MappingTorusCover (fixedEquatorData period hPeriod)) :
    normalLineZeroSection period hPeriod
        (mappingTorusMk (fixedEquatorData period hPeriod) base) =
      normalLineMk period hPeriod ⟨base, 0⟩ := rfl

theorem continuous_normalLineZeroSection (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (normalLineZeroSection period hPeriod) := by
  have hLift : Continuous (fun base : MappingTorusCover
      (fixedEquatorData period hPeriod) ↦
        (⟨base, 0⟩ : ThroatNormalCover period hPeriod)) := by
    exact ((throatNormalCoverHomeomorphProd period hPeriod).symm.continuous.comp
      (continuous_id.prodMk continuous_const)).congr fun _ ↦ rfl
  apply (continuous_quotient_mk'.comp hLift).quotient_lift

@[simp] theorem normalLineProjection_zeroSection
    (period : ℝ) (hPeriod : period ≠ 0) :
    normalLineProjection period hPeriod ∘ normalLineZeroSection period hPeriod = id := by
  funext base
  refine Quotient.inductionOn base ?_
  intro representative
  rfl

/-- One circuit reverses the actual quotient normal coordinate. -/
theorem one_loop_normal_flip (period : ℝ) (hPeriod : period ≠ 0)
    (base : MappingTorusCover (fixedEquatorData period hPeriod)) (normal : ℝ) :
    normalLineMk period hPeriod ⟨(1 : ℤ) +ᵥ base, -normal⟩ =
      normalLineMk period hPeriod ⟨base, normal⟩ := by
  apply Quotient.sound
  change AddAction.orbitRel ℤ (ThroatNormalCover period hPeriod)
    ⟨(1 : ℤ) +ᵥ base, -normal⟩ ⟨base, normal⟩
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  refine ⟨1, ?_⟩
  apply ThroatNormalCover.ext
  · rfl
  · simp [normalSignRepresentation]

/-- Two circuits restore the normal coordinate in the actual quotient. -/
theorem two_loops_restore_normal (period : ℝ) (hPeriod : period ≠ 0)
    (base : MappingTorusCover (fixedEquatorData period hPeriod)) (normal : ℝ) :
    normalLineMk period hPeriod ⟨(2 : ℤ) +ᵥ base, normal⟩ =
      normalLineMk period hPeriod ⟨base, normal⟩ := by
  apply Quotient.sound
  change AddAction.orbitRel ℤ (ThroatNormalCover period hPeriod)
    ⟨(2 : ℤ) +ᵥ base, normal⟩ ⟨base, normal⟩
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  refine ⟨2, ?_⟩
  apply ThroatNormalCover.ext
  · rfl
  · norm_num [normalSignRepresentation]

/-- Concrete closure delivered by the quotient construction. -/
theorem mapping_torus_normal_line_closure
    (period : ℝ) (hPeriod : period ≠ 0) :
    Function.Surjective (normalLineProjection period hPeriod) ∧
      Continuous (normalLineProjection period hPeriod) ∧
      Continuous (normalLineZeroSection period hPeriod) ∧
      normalLineProjection period hPeriod ∘ normalLineZeroSection period hPeriod = id := by
  refine ⟨?_, continuous_normalLineProjection period hPeriod,
    continuous_normalLineZeroSection period hPeriod,
    normalLineProjection_zeroSection period hPeriod⟩
  intro base
  exact ⟨normalLineZeroSection period hPeriod base,
    congrFun (normalLineProjection_zeroSection period hPeriod) base⟩

end P0EFTJanusMappingTorusNormalLine
end JanusFormal
