import Mathlib

namespace JanusFormal
namespace P0EFTJanusStructuredJetActionGroupoid

set_option autoImplicit false

universe u v w

section ActionGroupoid

variable {Symmetry : Type u}
variable {Base : Type v}
variable [Group Symmetry]
variable [MulAction Symmetry Base]

/-- An arrow in the action groupoid of a symmetry group acting on a background
space. In the intended application, `Base` is a finite-order structured-jet
space and `Symmetry` is a finite jet group of coordinate/frame/gauge changes. -/
structure ActionArrow (source target : Base) where
  element : Symmetry
  maps_source : element • source = target

@[ext]
theorem ActionArrow.ext
    {source target : Base}
    {first second : ActionArrow (Symmetry := Symmetry) source target}
    (hElement : first.element = second.element) :
    first = second := by
  cases first with
  | mk firstElement firstMap =>
      cases second with
      | mk secondElement secondMap =>
          dsimp at hElement
          subst secondElement
          rfl

/-- Identity arrow of the action groupoid. -/
def idArrow (base : Base) :
    ActionArrow (Symmetry := Symmetry) base base where
  element := 1
  maps_source := by simp

/-- Composition of action-groupoid arrows. The order is categorical:
`comp second first` first applies `first`, then `second`. -/
def comp
    {source middle target : Base}
    (second : ActionArrow (Symmetry := Symmetry) middle target)
    (first : ActionArrow (Symmetry := Symmetry) source middle) :
    ActionArrow (Symmetry := Symmetry) source target where
  element := second.element * first.element
  maps_source := by
    rw [mul_smul, first.maps_source, second.maps_source]

/-- Every action-groupoid arrow is invertible. -/
def inverse
    {source target : Base}
    (arrow : ActionArrow (Symmetry := Symmetry) source target) :
    ActionArrow (Symmetry := Symmetry) target source where
  element := arrow.element⁻¹
  maps_source := by
    calc
      arrow.element⁻¹ • target =
          arrow.element⁻¹ • (arrow.element • source) := by
        rw [arrow.maps_source]
      _ = (arrow.element⁻¹ * arrow.element) • source := by
        rw [mul_smul]
      _ = source := by simp

@[simp]
theorem comp_id
    {source target : Base}
    (arrow : ActionArrow (Symmetry := Symmetry) source target) :
    comp arrow (idArrow source) = arrow := by
  apply ActionArrow.ext
  simp [comp, idArrow]

@[simp]
theorem id_comp
    {source target : Base}
    (arrow : ActionArrow (Symmetry := Symmetry) source target) :
    comp (idArrow target) arrow = arrow := by
  apply ActionArrow.ext
  simp [comp, idArrow]

@[simp]
theorem comp_assoc
    {firstBase secondBase thirdBase fourthBase : Base}
    (first :
      ActionArrow (Symmetry := Symmetry) firstBase secondBase)
    (second :
      ActionArrow (Symmetry := Symmetry) secondBase thirdBase)
    (third :
      ActionArrow (Symmetry := Symmetry) thirdBase fourthBase) :
    comp third (comp second first) =
      comp (comp third second) first := by
  apply ActionArrow.ext
  simp [comp, mul_assoc]

@[simp]
theorem inverse_comp
    {source target : Base}
    (arrow : ActionArrow (Symmetry := Symmetry) source target) :
    comp (inverse arrow) arrow = idArrow source := by
  apply ActionArrow.ext
  simp [comp, inverse, idArrow]

@[simp]
theorem comp_inverse
    {source target : Base}
    (arrow : ActionArrow (Symmetry := Symmetry) source target) :
    comp arrow (inverse arrow) = idArrow target := by
  apply ActionArrow.ext
  simp [comp, inverse, idArrow]

/-- Isotropy group as a subtype of symmetry elements fixing one background. -/
def Stabilizer (base : Base) : Type u :=
  {element : Symmetry // element • base = base}

/-- Endomorphisms of one action-groupoid object are exactly its stabilizer. -/
def endomorphismEquivStabilizer (base : Base) :
    ActionArrow (Symmetry := Symmetry) base base ≃ Stabilizer base where
  toFun arrow := ⟨arrow.element, arrow.maps_source⟩
  invFun element := ⟨element.1, element.2⟩
  left_inv arrow := by
    cases arrow
    rfl
  right_inv element := by
    cases element
    rfl

/-- Orbit equivalence expressed intrinsically as existence of a groupoid arrow. -/
def SameOrbit (first second : Base) : Prop :=
  Nonempty (ActionArrow (Symmetry := Symmetry) first second)

@[refl]
theorem sameOrbit_refl (base : Base) : SameOrbit base base :=
  ⟨idArrow base⟩

@[symm]
theorem sameOrbit_symm
    {first second : Base}
    (hOrbit : SameOrbit (Symmetry := Symmetry) first second) :
    SameOrbit (Symmetry := Symmetry) second first := by
  rcases hOrbit with ⟨arrow⟩
  exact ⟨inverse arrow⟩

@[trans]
theorem sameOrbit_trans
    {first second third : Base}
    (hFirst : SameOrbit (Symmetry := Symmetry) first second)
    (hSecond : SameOrbit (Symmetry := Symmetry) second third) :
    SameOrbit (Symmetry := Symmetry) first third := by
  rcases hFirst with ⟨firstArrow⟩
  rcases hSecond with ⟨secondArrow⟩
  exact ⟨comp secondArrow firstArrow⟩

/-- Descent data for a field family over an action groupoid. This is the
algebraic core of a structured-jet equivariant bundle; smoothness and the actual
Janus jet spaces remain separate geometric obligations. -/
structure EquivariantFamily
    (Symmetry : Type u)
    (Base : Type v)
    [Group Symmetry]
    [MulAction Symmetry Base] where
  Fiber : Base → Type w
  transport :
    ∀ {source target : Base},
      ActionArrow (Symmetry := Symmetry) source target →
      Fiber source → Fiber target
  transport_id :
    ∀ (base : Base) (value : Fiber base),
      transport (idArrow (Symmetry := Symmetry) base) value = value
  transport_comp :
    ∀ {source middle target : Base}
      (first : ActionArrow (Symmetry := Symmetry) source middle)
      (second : ActionArrow (Symmetry := Symmetry) middle target)
      (value : Fiber source),
      transport (comp second first) value =
        transport second (transport first value)

/-- A section is equivariant when transport along every groupoid arrow sends its
source value to its target value. -/
def IsEquivariantSection
    (family : EquivariantFamily Symmetry Base)
    (section : ∀ base, family.Fiber base) : Prop :=
  ∀ {source target : Base}
    (arrow : ActionArrow (Symmetry := Symmetry) source target),
    family.transport arrow (section source) = section target

/-- Every equivariant section is fixed by every isotropy arrow at each base
point. This is the exact bridge from global equivariance to pointwise stabilizer
representations. -/
theorem equivariant_section_is_isotropy_fixed
    (family : EquivariantFamily Symmetry Base)
    (section : ∀ base, family.Fiber base)
    (hSection : IsEquivariantSection family section)
    (base : Base)
    (arrow : ActionArrow (Symmetry := Symmetry) base base) :
    family.transport arrow (section base) = section base :=
  hSection arrow

end ActionGroupoid

/-- Remaining obligations before the abstract action-groupoid core becomes the
actual structured SpinC-immersion jet groupoid. -/
structure StructuredJetGroupoidStatus where
  finiteJetBaseConstructed : Prop
  finiteJetSymmetryGroupConstructed : Prop
  symmetryActionOnJetsConstructed : Prop
  actionGroupoidCoreInstantiated : Prop
  naturalFieldDescentDataConstructed : Prop
  smoothnessAndFiniteDimensionalityProved : Prop
  effectiveDescentProved : Prop
  globalTopologicalDataSeparated : Prop

/-- Closure predicate for the genuine Janus structured-jet groupoid theorem. -/
def structuredJetGroupoidClosed
    (s : StructuredJetGroupoidStatus) : Prop :=
  s.finiteJetBaseConstructed /\
  s.finiteJetSymmetryGroupConstructed /\
  s.symmetryActionOnJetsConstructed /\
  s.actionGroupoidCoreInstantiated /\
  s.naturalFieldDescentDataConstructed /\
  s.smoothnessAndFiniteDimensionalityProved /\
  s.effectiveDescentProved /\
  s.globalTopologicalDataSeparated

/-- The abstract groupoid algebra does not construct the geometric action on
admissible Janus jets. -/
theorem missing_jet_action_blocks_structured_groupoid
    (s : StructuredJetGroupoidStatus)
    (hMissing : Not s.symmetryActionOnJetsConstructed) :
    Not (structuredJetGroupoidClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.1

end P0EFTJanusStructuredJetActionGroupoid
end JanusFormal
