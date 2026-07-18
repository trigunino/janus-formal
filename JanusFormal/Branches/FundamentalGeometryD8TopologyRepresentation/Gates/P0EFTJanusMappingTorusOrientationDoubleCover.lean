import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusNormalLine

namespace JanusFormal
namespace P0EFTJanusMappingTorusOrientationDoubleCover

set_option autoImplicit false

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusNormalLine
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusReflectionFixedThroat

/-- The orientation cover uses the even subgroup, hence the doubled period. -/
def doubledPeriod (period : ℝ) : ℝ := 2 * period

theorem doubledPeriod_ne_zero (period : ℝ) (hPeriod : period ≠ 0) :
    doubledPeriod period ≠ 0 :=
  mul_ne_zero (by norm_num) hPeriod

private theorem continuous_radiusSquared : Continuous radiusSquared := by
  unfold radiusSquared
  fun_prop

private theorem isClosed_equatorialTwoSphere :
    IsClosed {point : R4Point | OnEquatorialTwoSphere point} := by
  change IsClosed
    ({point : R4Point | radiusSquared point = 1} ∩ {point : R4Point | point 0 = 0})
  exact (isClosed_eq continuous_radiusSquared continuous_const).inter
    (isClosed_eq (continuous_apply 0) continuous_const)

@[implicit_reducible] private def equatorialTwoSphereLocallyCompactSpace :
    LocallyCompactSpace EquatorialTwoSphere :=
  isClosed_equatorialTwoSphere.locallyCompactSpace

/-- Mapping-torus data presenting the even-winding orientation cover. -/
def orientationDoubleData (period : ℝ) (hPeriod : period ≠ 0) :
    MappingTorusData EquatorialTwoSphere :=
  fixedEquatorData (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

/-- The actual quotient by even windings. -/
abbrev OrientationDoubleThroat (period : ℝ) (hPeriod : period ≠ 0) :=
  MappingTorus (orientationDoubleData period hPeriod)

/-- The two cover presentations have the same coordinates. -/
def orientationDoubleCoverHomeomorph (period : ℝ) (hPeriod : period ≠ 0) :
    MappingTorusCover (orientationDoubleData period hPeriod) ≃ₜ
      MappingTorusCover (fixedEquatorData period hPeriod) :=
  (coverHomeomorphProd (orientationDoubleData period hPeriod)).trans
    (coverHomeomorphProd (fixedEquatorData period hPeriod)).symm

@[simp] theorem orientationDoubleCoverHomeomorph_fiber
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : MappingTorusCover (orientationDoubleData period hPeriod)) :
    (orientationDoubleCoverHomeomorph period hPeriod point).fiber = point.fiber := rfl

@[simp] theorem orientationDoubleCoverHomeomorph_time
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : MappingTorusCover (orientationDoubleData period hPeriod)) :
    (orientationDoubleCoverHomeomorph period hPeriod point).time = point.time := rfl

private theorem refl_zpow_apply (winding : ℤ) (point : EquatorialTwoSphere) :
    ((Homeomorph.refl EquatorialTwoSphere) ^ winding) point = point := by
  rw [show ((Homeomorph.refl EquatorialTwoSphere) ^ winding) point =
      ((Homeomorph.refl EquatorialTwoSphere) ^ winding).toEquiv point from rfl,
    homeomorph_toEquiv_zpow]
  rw [show (Homeomorph.refl EquatorialTwoSphere).toEquiv = 1 from rfl, one_zpow]
  rfl

/-- A source winding becomes the even target winding `2n`. -/
theorem orientationDoubleCover_even_equivariant
    (period : ℝ) (hPeriod : period ≠ 0) (winding : ℤ)
    (point : MappingTorusCover (orientationDoubleData period hPeriod)) :
    orientationDoubleCoverHomeomorph period hPeriod (winding +ᵥ point) =
      (2 * winding) +ᵥ orientationDoubleCoverHomeomorph period hPeriod point := by
  apply MappingTorusCover.ext
  · change ((Homeomorph.refl EquatorialTwoSphere) ^ winding) point.fiber =
      ((Homeomorph.refl EquatorialTwoSphere) ^ (2 * winding)) point.fiber
    rw [refl_zpow_apply, refl_zpow_apply]
  · change point.time + (winding : ℝ) * (2 * period) =
      point.time + ((2 * winding : ℤ) : ℝ) * period
    push_cast
    ring

/-- Quotient map from the even-winding quotient to the effective throat. -/
def orientationDoubleToThroat (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationDoubleThroat period hPeriod →
      MappingTorus (fixedEquatorData period hPeriod) :=
  Quotient.map (orientationDoubleCoverHomeomorph period hPeriod) fun first second hOrbit ↦ by
    change AddAction.orbitRel ℤ
      (MappingTorusCover (orientationDoubleData period hPeriod)) first second at hOrbit
    change AddAction.orbitRel ℤ
      (MappingTorusCover (fixedEquatorData period hPeriod))
      (orientationDoubleCoverHomeomorph period hPeriod first)
      (orientationDoubleCoverHomeomorph period hPeriod second)
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
    rcases hOrbit with ⟨winding, hWinding⟩
    refine ⟨2 * winding, ?_⟩
    rw [← orientationDoubleCover_even_equivariant]
    exact congrArg (orientationDoubleCoverHomeomorph period hPeriod) hWinding

@[simp] theorem orientationDoubleToThroat_mk
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : MappingTorusCover (orientationDoubleData period hPeriod)) :
    orientationDoubleToThroat period hPeriod
        (mappingTorusMk (orientationDoubleData period hPeriod) point) =
      mappingTorusMk (fixedEquatorData period hPeriod)
        (orientationDoubleCoverHomeomorph period hPeriod point) := rfl

theorem continuous_orientationDoubleToThroat
    (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (orientationDoubleToThroat period hPeriod) := by
  apply (continuous_quotient_mk'.comp
    (orientationDoubleCoverHomeomorph period hPeriod).continuous).quotient_lift

theorem orientationDoubleToThroat_surjective
    (period : ℝ) (hPeriod : period ≠ 0) :
    Function.Surjective (orientationDoubleToThroat period hPeriod) := by
  intro throat
  refine Quotient.inductionOn throat ?_
  intro point
  exact ⟨mappingTorusMk (orientationDoubleData period hPeriod)
      ((orientationDoubleCoverHomeomorph period hPeriod).symm point), by
        simp⟩

/-- Half-period translation is the nontrivial deck map of the double cover. -/
def orientationDeckCover (period : ℝ) (hPeriod : period ≠ 0) :
    MappingTorusCover (orientationDoubleData period hPeriod) ≃ₜ
      MappingTorusCover (orientationDoubleData period hPeriod) where
  toFun point := ⟨point.fiber, point.time + period⟩
  invFun point := ⟨point.fiber, point.time - period⟩
  left_inv point := by ext <;> simp
  right_inv point := by ext <;> simp
  continuous_toFun := by
    have hFiber : Continuous (fun point :
        MappingTorusCover (orientationDoubleData period hPeriod) ↦ point.fiber) :=
      continuous_fiber _
    have hTime : Continuous (fun point :
        MappingTorusCover (orientationDoubleData period hPeriod) ↦
          point.time + period) :=
      (continuous_time _).add continuous_const
    have h := (coverHomeomorphProd (orientationDoubleData period hPeriod)).symm.continuous.comp
      (hFiber.prodMk hTime)
    exact h.congr fun _ ↦ rfl
  continuous_invFun := by
    have hFiber : Continuous (fun point :
        MappingTorusCover (orientationDoubleData period hPeriod) ↦ point.fiber) :=
      continuous_fiber _
    have hTime : Continuous (fun point :
        MappingTorusCover (orientationDoubleData period hPeriod) ↦
          point.time - period) :=
      (continuous_time _).sub continuous_const
    have h := (coverHomeomorphProd (orientationDoubleData period hPeriod)).symm.continuous.comp
      (hFiber.prodMk hTime)
    exact h.congr fun _ ↦ rfl

@[simp] theorem orientationDeckCover_fiber
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : MappingTorusCover (orientationDoubleData period hPeriod)) :
    (orientationDeckCover period hPeriod point).fiber = point.fiber := rfl

@[simp] theorem orientationDeckCover_time
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : MappingTorusCover (orientationDoubleData period hPeriod)) :
    (orientationDeckCover period hPeriod point).time = point.time + period := rfl

theorem orientationDeckCover_equivariant
    (period : ℝ) (hPeriod : period ≠ 0) (winding : ℤ)
    (point : MappingTorusCover (orientationDoubleData period hPeriod)) :
    orientationDeckCover period hPeriod (winding +ᵥ point) =
      winding +ᵥ orientationDeckCover period hPeriod point := by
  apply MappingTorusCover.ext
  · change ((Homeomorph.refl EquatorialTwoSphere) ^ winding) point.fiber =
      ((Homeomorph.refl EquatorialTwoSphere) ^ winding) point.fiber
    rfl
  · change point.time + (winding : ℝ) * (2 * period) + period =
      point.time + period + (winding : ℝ) * (2 * period)
    ring

/-- The nontrivial deck involution on the quotient. -/
def orientationDeck (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationDoubleThroat period hPeriod → OrientationDoubleThroat period hPeriod :=
  Quotient.lift (fun point ↦ mappingTorusMk (orientationDoubleData period hPeriod)
      (orientationDeckCover period hPeriod point)) fun first second hOrbit ↦ by
    apply Quotient.sound
    change AddAction.orbitRel ℤ
      (MappingTorusCover (orientationDoubleData period hPeriod)) first second at hOrbit
    change AddAction.orbitRel ℤ
      (MappingTorusCover (orientationDoubleData period hPeriod))
      (orientationDeckCover period hPeriod first)
      (orientationDeckCover period hPeriod second)
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
    rcases hOrbit with ⟨winding, hWinding⟩
    refine ⟨winding, ?_⟩
    rw [← orientationDeckCover_equivariant]
    exact congrArg (orientationDeckCover period hPeriod) hWinding

@[simp] theorem orientationDeck_mk
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : MappingTorusCover (orientationDoubleData period hPeriod)) :
    orientationDeck period hPeriod
        (mappingTorusMk (orientationDoubleData period hPeriod) point) =
      mappingTorusMk (orientationDoubleData period hPeriod)
        (orientationDeckCover period hPeriod point) := rfl

theorem continuous_orientationDeck
    (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (orientationDeck period hPeriod) := by
  apply (continuous_quotient_mk'.comp
    (orientationDeckCover period hPeriod).continuous).quotient_lift

@[simp] theorem orientationDeck_involutive
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : OrientationDoubleThroat period hPeriod) :
    orientationDeck period hPeriod (orientationDeck period hPeriod point) = point := by
  refine Quotient.inductionOn point ?_
  intro representative
  apply Quotient.sound
  change AddAction.orbitRel ℤ
    (MappingTorusCover (orientationDoubleData period hPeriod))
    (orientationDeckCover period hPeriod
      (orientationDeckCover period hPeriod representative)) representative
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  refine ⟨1, ?_⟩
  apply MappingTorusCover.ext
  · change ((Homeomorph.refl EquatorialTwoSphere) ^ (1 : ℤ)) representative.fiber =
      representative.fiber
    rw [refl_zpow_apply]
  · simp only [vadd_time, orientationDeckCover_time]
    simp only [orientationDoubleData, fixedEquatorData, doubledPeriod]
    ring

@[simp] theorem orientationDoubleToThroat_deck
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : OrientationDoubleThroat period hPeriod) :
    orientationDoubleToThroat period hPeriod (orientationDeck period hPeriod point) =
      orientationDoubleToThroat period hPeriod point := by
  refine Quotient.inductionOn point ?_
  intro representative
  apply Quotient.sound
  change AddAction.orbitRel ℤ
    (MappingTorusCover (fixedEquatorData period hPeriod))
    (orientationDoubleCoverHomeomorph period hPeriod
      (orientationDeckCover period hPeriod representative))
    (orientationDoubleCoverHomeomorph period hPeriod representative)
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  refine ⟨1, ?_⟩
  apply MappingTorusCover.ext
  · change ((Homeomorph.refl EquatorialTwoSphere) ^ (1 : ℤ)) representative.fiber =
      representative.fiber
    rw [refl_zpow_apply]
  · simp only [vadd_time, orientationDoubleCoverHomeomorph_time,
      orientationDeckCover_time]
    simp only [fixedEquatorData]
    ring

theorem orientationDeck_ne_self
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : OrientationDoubleThroat period hPeriod) :
    orientationDeck period hPeriod point ≠ point := by
  refine Quotient.inductionOn point ?_
  intro representative hFixed
  have hOrbit := (mappingTorusMk_eq_iff_exists_vadd
    (orientationDoubleData period hPeriod)
    (orientationDeckCover period hPeriod representative) representative).mp hFixed
  rcases hOrbit with ⟨winding, hWinding⟩
  have hTime := congrArg MappingTorusCover.time hWinding
  change representative.time + (winding : ℝ) * (2 * period) =
    representative.time + period at hTime
  have hProduct : (2 * (winding : ℝ) - 1) * period = 0 := by
    calc
      (2 * (winding : ℝ) - 1) * period =
          (representative.time + (winding : ℝ) * (2 * period)) -
            (representative.time + period) := by ring
      _ = 0 := by rw [hTime]; ring
  have hReal : 2 * (winding : ℝ) = 1 := by
    rcases mul_eq_zero.mp hProduct with hImpossible | hFactor
    · linarith
    · exact (hPeriod hFactor).elim
  have hInt : 2 * winding = 1 := by exact_mod_cast hReal
  omega

/-- Equality over the effective throat is exactly equality or the deck mate. -/
theorem orientationDouble_fiber_iff
    (period : ℝ) (hPeriod : period ≠ 0)
    (first second : OrientationDoubleThroat period hPeriod) :
    orientationDoubleToThroat period hPeriod first =
        orientationDoubleToThroat period hPeriod second ↔
      first = second ∨ first = orientationDeck period hPeriod second := by
  refine Quotient.inductionOn first ?_
  intro firstRepresentative
  refine Quotient.inductionOn second ?_
  intro secondRepresentative
  constructor
  · intro hSame
    rw [orientationDoubleToThroat_mk, orientationDoubleToThroat_mk,
      mappingTorusMk_eq_iff_exists_vadd] at hSame
    rcases hSame with ⟨winding, hWinding⟩
    rcases Int.even_or_odd' winding with ⟨half, hEven | hOdd⟩
    · left
      rw [mappingTorusMk_eq_iff_exists_vadd]
      refine ⟨half, ?_⟩
      apply (orientationDoubleCoverHomeomorph period hPeriod).injective
      rw [orientationDoubleCover_even_equivariant, ← hEven]
      exact hWinding
    · right
      rw [orientationDeck_mk, mappingTorusMk_eq_iff_exists_vadd]
      refine ⟨half, ?_⟩
      apply MappingTorusCover.ext
      · have hFiber := congrArg MappingTorusCover.fiber hWinding
        change ((Homeomorph.refl EquatorialTwoSphere) ^ winding)
          secondRepresentative.fiber = firstRepresentative.fiber at hFiber
        change ((Homeomorph.refl EquatorialTwoSphere) ^ half)
          secondRepresentative.fiber = firstRepresentative.fiber
        rw [refl_zpow_apply]
        rw [refl_zpow_apply] at hFiber
        exact hFiber
      · have hTime := congrArg MappingTorusCover.time hWinding
        change secondRepresentative.time + (winding : ℝ) * period =
          firstRepresentative.time at hTime
        change secondRepresentative.time + period + (half : ℝ) * (2 * period) =
          firstRepresentative.time
        rw [hOdd] at hTime
        push_cast at hTime
        calc
          secondRepresentative.time + period + (half : ℝ) * (2 * period) =
              secondRepresentative.time + (2 * (half : ℝ) + 1) * period := by ring
          _ = firstRepresentative.time := hTime
  · intro hCases
    rcases hCases with hSame | hDeck
    · exact congrArg (orientationDoubleToThroat period hPeriod) hSame
    · rw [hDeck]
      exact orientationDoubleToThroat_deck period hPeriod _

/-- The half-period deck map as a homeomorphism. -/
def orientationDeckHomeomorph
    (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationDoubleThroat period hPeriod ≃ₜ
      OrientationDoubleThroat period hPeriod where
  toFun := orientationDeck period hPeriod
  invFun := orientationDeck period hPeriod
  left_inv := orientationDeck_involutive period hPeriod
  right_inv := orientationDeck_involutive period hPeriod
  continuous_toFun := continuous_orientationDeck period hPeriod
  continuous_invFun := continuous_orientationDeck period hPeriod

/-- The deck involution as a permutation. -/
def orientationDeckPerm
    (period : ℝ) (hPeriod : period ≠ 0) :
    Equiv.Perm (OrientationDoubleThroat period hPeriod) :=
  (orientationDeckHomeomorph period hPeriod).toEquiv

/-- Integer iterates of the deck involution, written additively. -/
def orientationDeckIntHom
    (period : ℝ) (hPeriod : period ≠ 0) :
    ℤ →+ Additive (Equiv.Perm (OrientationDoubleThroat period hPeriod)) where
  toFun winding := Additive.ofMul ((orientationDeckPerm period hPeriod) ^ winding)
  map_zero' := by simp
  map_add' first second := by simp [zpow_add]

/-- The integer action factors through parity because the deck map squares to the identity. -/
def orientationParityPermHom
    (period : ℝ) (hPeriod : period ≠ 0) :
    ZMod 2 →+ Additive (Equiv.Perm (OrientationDoubleThroat period hPeriod)) :=
  ZMod.lift 2 ⟨orientationDeckIntHom period hPeriod, by
    change Additive.ofMul ((orientationDeckPerm period hPeriod) ^ (2 : ℤ)) = 0
    apply Additive.ext
    apply Equiv.ext
    intro point
    exact orientationDeck_involutive period hPeriod point⟩

private theorem zmod2_eq_zero_or_one (parity : ZMod 2) :
    parity = 0 ∨ parity = 1 := by
  by_cases hZero : parity = 0
  · exact Or.inl hZero
  · right
    apply (ZMod.val_eq_one (by norm_num) parity).mp
    have hValNe : parity.val ≠ 0 := (ZMod.val_eq_zero parity).not.mpr hZero
    have hValLt := parity.val_lt
    omega

/-- The residual `ZMod 2` action on the even-winding quotient. -/
def orientationParityVAdd
    (period : ℝ) (hPeriod : period ≠ 0) (parity : ZMod 2)
    (point : OrientationDoubleThroat period hPeriod) :
    OrientationDoubleThroat period hPeriod :=
  (orientationParityPermHom period hPeriod parity).toMul point

instance (period : ℝ) (hPeriod : period ≠ 0) :
    VAdd (ZMod 2) (OrientationDoubleThroat period hPeriod) :=
  ⟨orientationParityVAdd period hPeriod⟩

instance (period : ℝ) (hPeriod : period ≠ 0) :
    AddAction (ZMod 2) (OrientationDoubleThroat period hPeriod) where
  zero_vadd point := by
    change (orientationParityPermHom period hPeriod 0).toMul point = point
    simp
  add_vadd first second point := by
    change (orientationParityPermHom period hPeriod (first + second)).toMul point =
      (orientationParityPermHom period hPeriod first).toMul
        ((orientationParityPermHom period hPeriod second).toMul point)
    rw [map_add]
    rfl

@[simp] theorem one_vadd_orientationDouble
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : OrientationDoubleThroat period hPeriod) :
    (1 : ZMod 2) +ᵥ point = orientationDeck period hPeriod point := by
  change (orientationParityPermHom period hPeriod 1).toMul point =
    orientationDeck period hPeriod point
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num,
    orientationParityPermHom, ZMod.lift_coe]
  rfl

instance (period : ℝ) (hPeriod : period ≠ 0) :
    ContinuousConstVAdd (ZMod 2) (OrientationDoubleThroat period hPeriod) where
  continuous_const_vadd parity := by
    rcases zmod2_eq_zero_or_one parity with rfl | rfl
    · have hFunction : (fun point : OrientationDoubleThroat period hPeriod ↦
          (0 : ZMod 2) +ᵥ point) = id := by
        funext point
        simp
      rw [hFunction]
      exact continuous_id
    · have hFunction : (fun point : OrientationDoubleThroat period hPeriod ↦
          (1 : ZMod 2) +ᵥ point) = orientationDeck period hPeriod := by
        funext point
        exact one_vadd_orientationDouble period hPeriod point
      rw [hFunction]
      exact continuous_orientationDeck period hPeriod

instance (period : ℝ) (hPeriod : period ≠ 0) :
    IsCancelVAdd (ZMod 2) (OrientationDoubleThroat period hPeriod) :=
  isCancelVAdd_iff_eq_zero_of_vadd_eq.mpr fun parity point hFixed ↦ by
    rcases zmod2_eq_zero_or_one parity with rfl | rfl
    · rfl
    · rw [one_vadd_orientationDouble] at hFixed
      exact (orientationDeck_ne_self period hPeriod point hFixed).elim

theorem orientationDoubleToThroat_isQuotientMap
    (period : ℝ) (hPeriod : period ≠ 0) :
    IsQuotientMap (orientationDoubleToThroat period hPeriod) := by
  have hComposite : IsQuotientMap
      (orientationDoubleToThroat period hPeriod ∘
        mappingTorusMk (orientationDoubleData period hPeriod)) := by
    have hTarget : IsQuotientMap
        (mappingTorusMk (fixedEquatorData period hPeriod) ∘
          orientationDoubleCoverHomeomorph period hPeriod) :=
      isQuotientMap_quotient_mk'.comp
        (orientationDoubleCoverHomeomorph period hPeriod).isQuotientMap
    rw [show orientationDoubleToThroat period hPeriod ∘
        mappingTorusMk (orientationDoubleData period hPeriod) =
      mappingTorusMk (fixedEquatorData period hPeriod) ∘
        orientationDoubleCoverHomeomorph period hPeriod by
          funext point
          rfl]
    exact hTarget
  exact IsQuotientMap.of_comp_isQuotientMap isQuotientMap_quotient_mk' hComposite

theorem orientationDoubleToThroat_eq_iff_mem_orbit
    (period : ℝ) (hPeriod : period ≠ 0)
    {first second : OrientationDoubleThroat period hPeriod} :
    orientationDoubleToThroat period hPeriod first =
        orientationDoubleToThroat period hPeriod second ↔
      first ∈ AddAction.orbit (ZMod 2) second := by
  rw [orientationDouble_fiber_iff, AddAction.mem_orbit_iff]
  constructor
  · rintro (hSame | hDeck)
    · exact ⟨0, by simpa using hSame.symm⟩
    · exact ⟨1, by simpa using hDeck.symm⟩
  · rintro ⟨parity, hParity⟩
    rcases zmod2_eq_zero_or_one parity with rfl | rfl
    · exact Or.inl (by simpa only [zero_vadd] using hParity.symm)
    · exact Or.inr (by
        simpa only [one_vadd_orientationDouble] using hParity.symm)

/-- The residual free two-element action exhibits the throat map as a quotient covering. -/
theorem orientationDoubleToThroat_isAddQuotientCoveringMap
    (period : ℝ) (hPeriod : period ≠ 0) :
    IsAddQuotientCoveringMap (orientationDoubleToThroat period hPeriod) (ZMod 2) := by
  letI : LocallyCompactSpace EquatorialTwoSphere :=
    equatorialTwoSphereLocallyCompactSpace
  refine
    { toIsQuotientMap := orientationDoubleToThroat_isQuotientMap period hPeriod
      continuous_const_vadd := continuous_const_vadd
      apply_eq_iff_mem_orbit := orientationDoubleToThroat_eq_iff_mem_orbit period hPeriod
      disjoint := ?_ }
  intro point
  letI : T2Space (OrientationDoubleThroat period hPeriod) :=
    mappingTorus_t2Space (orientationDoubleData period hPeriod)
  obtain ⟨u, v, hu, hv, huv⟩ :=
    t2_separation_nhds (orientationDeck_ne_self period hPeriod point)
  let U := v ∩ (orientationDeck period hPeriod) ⁻¹' u
  have hU : U ∈ nhds point := Filter.inter_mem hv
    ((continuous_orientationDeck period hPeriod).continuousAt hu)
  refine ⟨U, hU, ?_⟩
  intro parity hIntersect
  rcases zmod2_eq_zero_or_one parity with rfl | rfl
  · rfl
  · have hDeckIntersect :
        (((orientationDeck period hPeriod) '' U) ∩ U).Nonempty := by
      simpa only [one_vadd_orientationDouble] using hIntersect
    rcases hDeckIntersect with ⟨-, ⟨source, hSource, rfl⟩, hDeckSource⟩
    exact (Set.disjoint_left.mp huv hSource.2 hDeckSource.1).elim

/-- The quotient by even windings is a genuine two-sheeted covering of the throat. -/
theorem orientationDoubleToThroat_isCoveringMap
    (period : ℝ) (hPeriod : period ≠ 0) :
    IsCoveringMap (orientationDoubleToThroat period hPeriod) :=
  (orientationDoubleToThroat_isAddQuotientCoveringMap period hPeriod).isCoveringMap

/-- Every fiber is (noncanonically) the two-element residual deck group. -/
theorem orientationDouble_fiber_equiv_two
    (period : ℝ) (hPeriod : period ≠ 0)
    (throat : MappingTorus (fixedEquatorData period hPeriod)) :
    Nonempty
      ((orientationDoubleToThroat period hPeriod ⁻¹' {throat}) ≃ ZMod 2) := by
  let hCover := orientationDoubleToThroat_isAddQuotientCoveringMap period hPeriod
  rcases orientationDoubleToThroat_surjective period hPeriod throat with ⟨point, hPoint⟩
  exact ⟨hCover.fiberEquivAddGroup ⟨point, hPoint⟩⟩

/-- Cover presentation of the normal line after pullback to even windings. -/
@[ext] structure OrientationNormalCover (period : ℝ) (hPeriod : period ≠ 0) where
  base : MappingTorusCover (orientationDoubleData period hPeriod)
  normal : ℝ

def orientationNormalCoverEquivProd
    (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationNormalCover period hPeriod ≃
      MappingTorusCover (orientationDoubleData period hPeriod) × ℝ where
  toFun point := (point.base, point.normal)
  invFun point := ⟨point.1, point.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (period : ℝ) (hPeriod : period ≠ 0) :
    TopologicalSpace (OrientationNormalCover period hPeriod) :=
  (orientationNormalCoverEquivProd period hPeriod).topologicalSpace

def orientationNormalCoverHomeomorphProd
    (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationNormalCover period hPeriod ≃ₜ
      MappingTorusCover (orientationDoubleData period hPeriod) × ℝ :=
  (orientationNormalCoverEquivProd period hPeriod).homeomorph

theorem continuous_orientationNormalBase
    (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (OrientationNormalCover.base : OrientationNormalCover period hPeriod →
      MappingTorusCover (orientationDoubleData period hPeriod)) := by
  change Continuous (fun point ↦
    ((orientationNormalCoverHomeomorphProd period hPeriod) point).1)
  exact continuous_fst.comp
    (orientationNormalCoverHomeomorphProd period hPeriod).continuous

theorem continuous_orientationNormalCoordinate
    (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (OrientationNormalCover.normal : OrientationNormalCover period hPeriod → ℝ) := by
  change Continuous (fun point ↦
    ((orientationNormalCoverHomeomorphProd period hPeriod) point).2)
  exact continuous_snd.comp
    (orientationNormalCoverHomeomorphProd period hPeriod).continuous

/-- Even deck translations leave the pulled-back normal coordinate unchanged. -/
def orientationNormalVAdd
    (period : ℝ) (hPeriod : period ≠ 0) (winding : ℤ)
    (point : OrientationNormalCover period hPeriod) :
    OrientationNormalCover period hPeriod :=
  ⟨winding +ᵥ point.base, point.normal⟩

instance (period : ℝ) (hPeriod : period ≠ 0) :
    VAdd ℤ (OrientationNormalCover period hPeriod) :=
  ⟨orientationNormalVAdd period hPeriod⟩

instance (period : ℝ) (hPeriod : period ≠ 0) :
    AddAction ℤ (OrientationNormalCover period hPeriod) where
  zero_vadd point := by
    apply OrientationNormalCover.ext
    · change (0 : ℤ) +ᵥ point.base = point.base
      exact zero_vadd _ _
    · rfl
  add_vadd first second point := by
    apply OrientationNormalCover.ext
    · change (first + second) +ᵥ point.base =
        first +ᵥ (second +ᵥ point.base)
      exact add_vadd first second point.base
    · rfl

@[simp] theorem orientationNormal_vadd_base
    (period : ℝ) (hPeriod : period ≠ 0) (winding : ℤ)
    (point : OrientationNormalCover period hPeriod) :
    (winding +ᵥ point).base = winding +ᵥ point.base := rfl

@[simp] theorem orientationNormal_vadd_normal
    (period : ℝ) (hPeriod : period ≠ 0) (winding : ℤ)
    (point : OrientationNormalCover period hPeriod) :
    (winding +ᵥ point).normal = point.normal := rfl

/-- Actual associated normal line on the orientation double quotient. -/
abbrev OrientationPulledBackNormalLine
    (period : ℝ) (hPeriod : period ≠ 0) :=
  AddAction.orbitRel.Quotient ℤ (OrientationNormalCover period hPeriod)

abbrev orientationNormalMk
    (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationNormalCover period hPeriod →
      OrientationPulledBackNormalLine period hPeriod :=
  Quotient.mk (AddAction.orbitRel ℤ (OrientationNormalCover period hPeriod))

/-- Projection of the pulled-back normal line to the orientation cover. -/
def orientationNormalProjection
    (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationPulledBackNormalLine period hPeriod →
      OrientationDoubleThroat period hPeriod :=
  Quotient.map OrientationNormalCover.base fun first second hOrbit ↦ by
    change AddAction.orbitRel ℤ (OrientationNormalCover period hPeriod)
      first second at hOrbit
    change AddAction.orbitRel ℤ
      (MappingTorusCover (orientationDoubleData period hPeriod)) first.base second.base
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
    rcases hOrbit with ⟨winding, hWinding⟩
    exact ⟨winding, congrArg OrientationNormalCover.base hWinding⟩

@[simp] theorem orientationNormalProjection_mk
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : OrientationNormalCover period hPeriod) :
    orientationNormalProjection period hPeriod
        (orientationNormalMk period hPeriod point) =
      mappingTorusMk (orientationDoubleData period hPeriod) point.base := rfl

theorem continuous_orientationNormalProjection
    (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (orientationNormalProjection period hPeriod) := by
  apply (continuous_quotient_mk'.comp
    (continuous_orientationNormalBase period hPeriod)).quotient_lift

/-- Coordinate-forgetting map from the even cover to the original normal cover. -/
def orientationNormalForget
    (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationNormalCover period hPeriod → ThroatNormalCover period hPeriod :=
  fun point ↦
    ⟨orientationDoubleCoverHomeomorph period hPeriod point.base, point.normal⟩

theorem continuous_orientationNormalForget
    (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (orientationNormalForget period hPeriod) := by
  have hBase : Continuous (fun point : OrientationNormalCover period hPeriod ↦
      orientationDoubleCoverHomeomorph period hPeriod point.base) :=
    (orientationDoubleCoverHomeomorph period hPeriod).continuous.comp
      (continuous_orientationNormalBase period hPeriod)
  have hNormal := continuous_orientationNormalCoordinate period hPeriod
  exact ((throatNormalCoverHomeomorphProd period hPeriod).symm.continuous.comp
    (hBase.prodMk hNormal)).congr fun _ ↦ rfl

/-- Pullback of the sign character to every even winding is trivial. -/
theorem pulledBack_normal_sign_trivial (winding : ℤ) :
    normalSignRepresentation (2 * winding) = 1 :=
  doubled_deck_action_trivial winding

theorem orientationNormalForget_even_equivariant
    (period : ℝ) (hPeriod : period ≠ 0) (winding : ℤ)
    (point : OrientationNormalCover period hPeriod) :
    orientationNormalForget period hPeriod (winding +ᵥ point) =
      (2 * winding) +ᵥ orientationNormalForget period hPeriod point := by
  apply ThroatNormalCover.ext
  · exact orientationDoubleCover_even_equivariant period hPeriod winding point.base
  · change point.normal =
      (normalSignRepresentation (2 * winding) : ℝ) * point.normal
    rw [pulledBack_normal_sign_trivial]
    simp

/-- Map from the pulled-back associated line to the original associated line. -/
def orientationNormalToOriginal
    (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationPulledBackNormalLine period hPeriod →
      MappingTorusNormalLine period hPeriod :=
  Quotient.map (orientationNormalForget period hPeriod) fun first second hOrbit ↦ by
    change AddAction.orbitRel ℤ (OrientationNormalCover period hPeriod)
      first second at hOrbit
    change AddAction.orbitRel ℤ (ThroatNormalCover period hPeriod)
      (orientationNormalForget period hPeriod first)
      (orientationNormalForget period hPeriod second)
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
    rcases hOrbit with ⟨winding, hWinding⟩
    refine ⟨2 * winding, ?_⟩
    rw [← orientationNormalForget_even_equivariant]
    exact congrArg (orientationNormalForget period hPeriod) hWinding

@[simp] theorem orientationNormalToOriginal_mk
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : OrientationNormalCover period hPeriod) :
    orientationNormalToOriginal period hPeriod
        (orientationNormalMk period hPeriod point) =
      normalLineMk period hPeriod (orientationNormalForget period hPeriod point) := rfl

theorem continuous_orientationNormalToOriginal
    (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (orientationNormalToOriginal period hPeriod) := by
  apply (continuous_quotient_mk'.comp
    (continuous_orientationNormalForget period hPeriod)).quotient_lift

/-- The associated-line map covers the orientation double-cover map. -/
theorem orientationNormal_pullback_square
    (period : ℝ) (hPeriod : period ≠ 0) :
    normalLineProjection period hPeriod ∘ orientationNormalToOriginal period hPeriod =
      orientationDoubleToThroat period hPeriod ∘
        orientationNormalProjection period hPeriod := by
  funext point
  refine Quotient.inductionOn point ?_
  intro representative
  rfl

/-- Explicit fiber coordinate on the even quotient. -/
def orientationNormalTrivializationTo
    (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationPulledBackNormalLine period hPeriod →
      OrientationDoubleThroat period hPeriod × ℝ :=
  Quotient.lift (fun point ↦
      (mappingTorusMk (orientationDoubleData period hPeriod) point.base, point.normal))
    (by
      intro first second hOrbit
      change AddAction.orbitRel ℤ (OrientationNormalCover period hPeriod)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      apply Prod.ext
      · apply Quotient.sound
        change AddAction.orbitRel ℤ
          (MappingTorusCover (orientationDoubleData period hPeriod)) first.base second.base
        rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
        exact ⟨winding, congrArg OrientationNormalCover.base hWinding⟩
      · have hNormal := congrArg OrientationNormalCover.normal hWinding
        change second.normal = first.normal at hNormal
        exact hNormal.symm)

@[simp] theorem orientationNormalTrivializationTo_mk
    (period : ℝ) (hPeriod : period ≠ 0)
    (point : OrientationNormalCover period hPeriod) :
    orientationNormalTrivializationTo period hPeriod
        (orientationNormalMk period hPeriod point) =
      (mappingTorusMk (orientationDoubleData period hPeriod) point.base, point.normal) := rfl

/-- Inverse to the explicit fiber coordinate, descending only in the base variable. -/
def orientationNormalTrivializationInv
    (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationDoubleThroat period hPeriod × ℝ →
      OrientationPulledBackNormalLine period hPeriod :=
  fun pair ↦
    Quotient.lift
      (fun base ↦ orientationNormalMk period hPeriod ⟨base, pair.2⟩)
      (by
        intro first second hOrbit
        apply Quotient.sound
        change AddAction.orbitRel ℤ (OrientationNormalCover period hPeriod)
          ⟨first, pair.2⟩ ⟨second, pair.2⟩
        change AddAction.orbitRel ℤ
          (MappingTorusCover (orientationDoubleData period hPeriod)) first second at hOrbit
        rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
        rcases hOrbit with ⟨winding, hWinding⟩
        refine ⟨winding, ?_⟩
        apply OrientationNormalCover.ext
        · exact hWinding
        · rfl)
      pair.1

@[simp] theorem orientationNormalTrivializationInv_mk
    (period : ℝ) (hPeriod : period ≠ 0)
    (base : MappingTorusCover (orientationDoubleData period hPeriod)) (normal : ℝ) :
    orientationNormalTrivializationInv period hPeriod
        (mappingTorusMk (orientationDoubleData period hPeriod) base, normal) =
      orientationNormalMk period hPeriod ⟨base, normal⟩ := rfl

/-- Algebraic global trivialization of the pulled-back associated normal line. -/
def orientationNormalTrivializationEquiv
    (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationPulledBackNormalLine period hPeriod ≃
      OrientationDoubleThroat period hPeriod × ℝ where
  toFun := orientationNormalTrivializationTo period hPeriod
  invFun := orientationNormalTrivializationInv period hPeriod
  left_inv point := by
    refine Quotient.inductionOn point ?_
    intro representative
    rfl
  right_inv pair := by
    rcases pair with ⟨base, normal⟩
    refine Quotient.inductionOn base ?_
    intro representative
    rfl

theorem continuous_orientationNormalTrivializationTo
    (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (orientationNormalTrivializationTo period hPeriod) := by
  have hBase : Continuous (fun point : OrientationNormalCover period hPeriod ↦
      mappingTorusMk (orientationDoubleData period hPeriod) point.base) :=
    continuous_quotient_mk'.comp (continuous_orientationNormalBase period hPeriod)
  apply (hBase.prodMk (continuous_orientationNormalCoordinate period hPeriod)).quotient_lift

theorem continuous_orientationNormalTrivializationInv
    (period : ℝ) (hPeriod : period ≠ 0) :
    Continuous (orientationNormalTrivializationInv period hPeriod) := by
  letI : LocallyCompactSpace EquatorialTwoSphere :=
    equatorialTwoSphereLocallyCompactSpace
  have hBaseOpen : IsOpenQuotientMap
      (mappingTorusMk (orientationDoubleData period hPeriod)) :=
    (mappingTorusMk_isAddQuotientCoveringMap
      (orientationDoubleData period hPeriod)).isOpenQuotientMap
  have hProdOpen : IsOpenQuotientMap
      (Prod.map (mappingTorusMk (orientationDoubleData period hPeriod)) (id : ℝ → ℝ)) :=
    hBaseOpen.prodMap IsOpenQuotientMap.id
  rw [← hProdOpen.continuous_comp_iff]
  have hLift : Continuous
      (orientationNormalMk period hPeriod ∘
        (orientationNormalCoverHomeomorphProd period hPeriod).symm) :=
    continuous_quotient_mk'.comp
      (orientationNormalCoverHomeomorphProd period hPeriod).symm.continuous
  exact hLift.congr fun _ ↦ rfl

/-- Topological global trivialization; no vector-bundle or manifold structure is asserted. -/
def orientationNormalTrivialization
    (period : ℝ) (hPeriod : period ≠ 0) :
    OrientationPulledBackNormalLine period hPeriod ≃ₜ
      OrientationDoubleThroat period hPeriod × ℝ where
  toEquiv := orientationNormalTrivializationEquiv period hPeriod
  continuous_toFun := continuous_orientationNormalTrivializationTo period hPeriod
  continuous_invFun := continuous_orientationNormalTrivializationInv period hPeriod

@[simp] theorem orientationNormalTrivialization_fiberwise
    (period : ℝ) (hPeriod : period ≠ 0) :
    Prod.fst ∘ orientationNormalTrivialization period hPeriod =
      orientationNormalProjection period hPeriod := by
  funext point
  refine Quotient.inductionOn point ?_
  intro representative
  rfl

/-- Honest closure: a two-sheeted topological cover and a trivial associated normal pullback. -/
theorem orientationDouble_normal_pullback_closure
    (period : ℝ) (hPeriod : period ≠ 0) :
    IsCoveringMap (orientationDoubleToThroat period hPeriod) ∧
      (∀ winding : ℤ, normalSignRepresentation (2 * winding) = 1) ∧
      Continuous (orientationNormalToOriginal period hPeriod) ∧
      normalLineProjection period hPeriod ∘ orientationNormalToOriginal period hPeriod =
        orientationDoubleToThroat period hPeriod ∘
          orientationNormalProjection period hPeriod ∧
      Nonempty (OrientationPulledBackNormalLine period hPeriod ≃ₜ
        OrientationDoubleThroat period hPeriod × ℝ) := by
  exact ⟨orientationDoubleToThroat_isCoveringMap period hPeriod,
    pulledBack_normal_sign_trivial,
    continuous_orientationNormalToOriginal period hPeriod,
    orientationNormal_pullback_square period hPeriod,
    ⟨orientationNormalTrivialization period hPeriod⟩⟩

end P0EFTJanusMappingTorusOrientationDoubleCover
end JanusFormal
