import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusStructuredJetActionGroupoid

namespace JanusFormal
namespace P0EFTJanusOrbitwiseDescent

set_option autoImplicit false

universe u v w

open P0EFTJanusStructuredJetActionGroupoid

section OrbitwiseDescent

variable {Symmetry : Type u}
variable {Base : Type v}
variable [Group Symmetry]
variable [MulAction Symmetry Base]

/-- A fiber value is isotropy-fixed when transport along every endomorphism of
the base object leaves it unchanged. -/
def IsIsotropyFixed
    (family : EquivariantFamily Symmetry Base)
    (base : Base)
    (value : family.Fiber base) : Prop :=
  ∀ arrow : ActionArrow (Symmetry := Symmetry) base base,
    family.transport arrow value = value

/-- Type of global equivariant sections of an equivariant family. -/
def EquivariantSectionSpace
    (family : EquivariantFamily Symmetry Base) :=
  {fieldSection : ∀ base, family.Fiber base //
    IsEquivariantSection family fieldSection}

/-- Type of isotropy-fixed values in one chosen fiber. -/
def FixedFiber
    (family : EquivariantFamily Symmetry Base)
    (base : Base) :=
  {value : family.Fiber base // IsIsotropyFixed family base value}

/-- Evaluation of an equivariant section at one base point lands in the
isotropy-fixed subspace. -/
def evaluateAtBase
    (family : EquivariantFamily Symmetry Base)
    (base : Base) :
    EquivariantSectionSpace family → FixedFiber family base :=
  fun fieldSection =>
    ⟨fieldSection.1 base,
      fun arrow =>
        equivariant_section_is_isotropy_fixed
          family fieldSection.1 fieldSection.2 base arrow⟩

/-- Chosen arrow from a base point to each target on a transitive orbit. -/
noncomputable def chosenOrbitArrow
    (base : Base)
    (hTransitive : ∀ target : Base,
      Nonempty (ActionArrow (Symmetry := Symmetry) base target))
    (target : Base) :
    ActionArrow (Symmetry := Symmetry) base target :=
  Classical.choice (hTransitive target)

/-- Two arrows with the same source and target differ by isotropy at the source.
The displayed formula is the exact action-groupoid decomposition used in descent. -/
theorem arrow_decomposes_through_source_isotropy
    {base target : Base}
    (first second :
      ActionArrow (Symmetry := Symmetry) base target) :
    first = comp second (comp (inverse second) first) := by
  apply ActionArrow.ext
  simp [comp, inverse, mul_assoc]

/-- Extend one isotropy-fixed value over a transitive orbit using chosen arrows. -/
noncomputable def extendFixedValue
    (family : EquivariantFamily Symmetry Base)
    (base : Base)
    (hTransitive : ∀ target : Base,
      Nonempty (ActionArrow (Symmetry := Symmetry) base target))
    (value : FixedFiber family base) :
    ∀ target, family.Fiber target :=
  fun target =>
    family.transport (chosenOrbitArrow base hTransitive target) value.1

/-- Extension returns the original fixed value at the base point, even though
the chosen base-to-base arrow need not be the identity. -/
theorem extendFixedValue_at_base
    (family : EquivariantFamily Symmetry Base)
    (base : Base)
    (hTransitive : ∀ target : Base,
      Nonempty (ActionArrow (Symmetry := Symmetry) base target))
    (value : FixedFiber family base) :
    extendFixedValue family base hTransitive value base = value.1 := by
  exact value.2 (chosenOrbitArrow base hTransitive base)

/-- Isotropy-fixedness makes the extension independent enough of chosen arrows
to satisfy equivariance along every action-groupoid arrow. -/
theorem extendFixedValue_is_equivariant
    (family : EquivariantFamily Symmetry Base)
    (base : Base)
    (hTransitive : ∀ target : Base,
      Nonempty (ActionArrow (Symmetry := Symmetry) base target))
    (value : FixedFiber family base) :
    IsEquivariantSection family
      (extendFixedValue family base hTransitive value) := by
  intro source target arrow
  let sourceArrow := chosenOrbitArrow base hTransitive source
  let targetArrow := chosenOrbitArrow base hTransitive target
  let compositeArrow :
      ActionArrow (Symmetry := Symmetry) base target :=
    comp arrow sourceArrow
  let isotropyArrow :
      ActionArrow (Symmetry := Symmetry) base base :=
    comp (inverse targetArrow) compositeArrow
  have hDecomposition :
      compositeArrow = comp targetArrow isotropyArrow := by
    exact arrow_decomposes_through_source_isotropy
      compositeArrow targetArrow
  calc
    family.transport arrow
        (extendFixedValue family base hTransitive value source) =
      family.transport arrow
        (family.transport sourceArrow value.1) := by
      rfl
    _ = family.transport compositeArrow value.1 := by
      exact (family.transport_comp sourceArrow arrow value.1).symm
    _ = family.transport (comp targetArrow isotropyArrow) value.1 := by
      rw [hDecomposition]
    _ = family.transport targetArrow
        (family.transport isotropyArrow value.1) := by
      exact family.transport_comp isotropyArrow targetArrow value.1
    _ = family.transport targetArrow value.1 := by
      rw [value.2 isotropyArrow]
    _ = extendFixedValue family base hTransitive value target := by
      rfl

/-- On a transitive orbit, two equivariant sections agreeing at one base point
agree everywhere. -/
theorem equivariant_sections_determined_by_base
    (family : EquivariantFamily Symmetry Base)
    (base : Base)
    (hTransitive : ∀ target : Base,
      Nonempty (ActionArrow (Symmetry := Symmetry) base target))
    (first second : EquivariantSectionSpace family)
    (hBase : first.1 base = second.1 base) :
    first = second := by
  apply Subtype.ext
  funext target
  let arrow := chosenOrbitArrow base hTransitive target
  calc
    first.1 target = family.transport arrow (first.1 base) := by
      exact (first.2 arrow).symm
    _ = family.transport arrow (second.1 base) := by
      rw [hBase]
    _ = second.1 target := second.2 arrow

/-- Orbitwise descent equivalence: global equivariant sections over a transitive
action-groupoid orbit are exactly isotropy-fixed values in one chosen fiber. -/
noncomputable def orbitwiseDescentEquiv
    (family : EquivariantFamily Symmetry Base)
    (base : Base)
    (hTransitive : ∀ target : Base,
      Nonempty (ActionArrow (Symmetry := Symmetry) base target)) :
    EquivariantSectionSpace family ≃ FixedFiber family base where
  toFun := evaluateAtBase family base
  invFun value :=
    ⟨extendFixedValue family base hTransitive value,
      extendFixedValue_is_equivariant family base hTransitive value⟩
  left_inv fieldSection := by
    apply equivariant_sections_determined_by_base
      family base hTransitive
    exact extendFixedValue_at_base family base hTransitive
      (evaluateAtBase family base fieldSection)
  right_inv value := by
    apply Subtype.ext
    exact extendFixedValue_at_base family base hTransitive value

end OrbitwiseDescent

/-- The orbitwise theorem is exact, but a global Janus field space may have many
orbit types and singular strata. -/
structure OrbitwiseDescentStatus where
  abstractActionGroupoidConstructed : Prop
  transitiveOrbitDescentProved : Prop
  janusOrbitTypesClassified : Prop
  isotropyRepresentationsComputed : Prop
  equivariantFamiliesConstructed : Prop
  descentAppliedOnEachOrbit : Prop
  smoothCompatibilityAcrossStrataProved : Prop
  globalTopologicalSectorsReattached : Prop

/-- Closure of global stratified descent for the Janus structured-jet groupoid. -/
def stratifiedDescentClosed
    (s : OrbitwiseDescentStatus) : Prop :=
  s.abstractActionGroupoidConstructed /\
  s.transitiveOrbitDescentProved /\
  s.janusOrbitTypesClassified /\
  s.isotropyRepresentationsComputed /\
  s.equivariantFamiliesConstructed /\
  s.descentAppliedOnEachOrbit /\
  s.smoothCompatibilityAcrossStrataProved /\
  s.globalTopologicalSectorsReattached

/-- Orbitwise reconstruction does not solve extension between different
isotropy strata. -/
theorem missing_cross_stratum_compatibility_blocks_global_descent
    (s : OrbitwiseDescentStatus)
    (hMissing : Not s.smoothCompatibilityAcrossStrataProved) :
    Not (stratifiedDescentClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.1

end P0EFTJanusOrbitwiseDescent
end JanusFormal
