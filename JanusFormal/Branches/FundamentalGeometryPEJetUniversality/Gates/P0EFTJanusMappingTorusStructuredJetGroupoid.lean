import Mathlib.CategoryTheory.Groupoid
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusStructuredJetActionGroupoid
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusActualStructuredJetExtraction

/-!
# The deck groupoid and smooth structured-jet descent on the D8 quotient

This gate connects the actual smooth mapping-torus quotient to the existing
structured action-groupoid core.  The deck action gives a genuine small
groupoid, each integer component is an etale smooth correspondence, and smooth
deck-invariant maps descend uniquely to the installed quotient manifold.

The arrow manifold is recorded componentwise (one copy of the cover for every
integer).  No claim about higher-order holonomic surjectivity, SpinC gluing, or
global vector/principal bundles is made here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusStructuredJetGroupoid

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff
open CategoryTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusStructuredJetActionGroupoid
open P0EFTJanusActualStructuredJetExtraction
open P0EFTJanusRieszShapeOperatorSmoothReducedJetBase
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction

universe u v w y z

section DeckCategory

variable {X : Type u} [TopologicalSpace X]

/-- Objects of the Janus deck category.  The type synonym prevents the
category instance from changing the ambient category on the cover itself. -/
def JanusDeckObject (data : MappingTorusData X) := MappingTorusCover data

instance (data : MappingTorusData X) : VAdd ℤ (JanusDeckObject data) :=
  inferInstanceAs (VAdd ℤ (MappingTorusCover data))

instance (data : MappingTorusData X) : AddAction ℤ (JanusDeckObject data) :=
  inferInstanceAs (AddAction ℤ (MappingTorusCover data))

instance (data : MappingTorusData X) : IsCancelVAdd ℤ (JanusDeckObject data) :=
  inferInstanceAs (IsCancelVAdd ℤ (MappingTorusCover data))

/-- A morphism is exactly an arrow of the already established action-groupoid
core, for the multiplicative type tag of the integer deck group. -/
abbrev JanusDeckArrow (data : MappingTorusData X)
    (source target : JanusDeckObject data) :=
  ActionArrow (Symmetry := Multiplicative ℤ) source target

instance janusDeckCategoryStruct (data : MappingTorusData X) :
    CategoryStruct (JanusDeckObject data) where
  Hom := JanusDeckArrow data
  id base := idArrow base
  comp first second := P0EFTJanusStructuredJetActionGroupoid.comp second first

instance janusDeckCategory (data : MappingTorusData X) :
    Category (JanusDeckObject data) where
  id_comp arrow := P0EFTJanusStructuredJetActionGroupoid.comp_id arrow
  comp_id arrow := P0EFTJanusStructuredJetActionGroupoid.id_comp arrow
  assoc first second third :=
    P0EFTJanusStructuredJetActionGroupoid.comp_assoc first second third

instance janusDeckGroupoid (data : MappingTorusData X) :
    Groupoid (JanusDeckObject data) where
  inv arrow := P0EFTJanusStructuredJetActionGroupoid.inverse arrow
  inv_comp arrow := P0EFTJanusStructuredJetActionGroupoid.comp_inverse arrow
  comp_inv arrow := P0EFTJanusStructuredJetActionGroupoid.inverse_comp arrow

/-- The orbit quotient identifies precisely the objects connected by a deck
groupoid morphism. -/
theorem mappingTorusMk_eq_iff_nonempty_deck_hom
    (data : MappingTorusData X)
    (source target : JanusDeckObject data) :
    mappingTorusMk data source = mappingTorusMk data target ↔
      Nonempty (source ⟶ target) := by
  constructor
  · intro h
    obtain ⟨winding, hWinding⟩ :=
      (mappingTorusMk_eq_iff_exists_vadd data target source).1 h.symm
    exact ⟨⟨Multiplicative.ofAdd winding, hWinding⟩⟩
  · rintro ⟨arrow⟩
    exact (mappingTorusMk_eq_iff_exists_vadd data target source).2
      ⟨arrow.element.toAdd, arrow.maps_source⟩ |>.symm

/-- Freeness of the deck action makes every hom type a subsingleton. -/
instance janusDeckHomSubsingleton
    (data : MappingTorusData X)
    (source target : JanusDeckObject data) :
    Subsingleton (source ⟶ target) where
  allEq first second := by
    apply ActionArrow.ext
    apply Multiplicative.ext
    exact IsCancelVAdd.right_cancel
      first.element.toAdd second.element.toAdd source
      (first.maps_source.trans second.maps_source.symm)

/-- Every isotropy arrow of the effective D8 deck groupoid is the identity. -/
theorem janusDeck_endomorphism_eq_id
    (data : MappingTorusData X)
    (base : JanusDeckObject data)
    (arrow : base ⟶ base) :
    arrow = 𝟙 base :=
  Subsingleton.elim _ _

/-- Each deck isotropy group is a singleton, uniformly over the cover. -/
def janusDeckEndomorphismEquivPUnit
    (data : MappingTorusData X)
    (base : JanusDeckObject data) :
    (base ⟶ base) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := 𝟙 base
  left_inv arrow := (janusDeck_endomorphism_eq_id data base arrow).symm
  right_inv point := by cases point; rfl

/-- Hence the effective D8 deck presentation has one isotropy stratum: the
trivial orbit type at every object.  This statement concerns deck isotropy;
residual frame or SpinC isotropy on structured-jet fibers is separate. -/
theorem janusDeck_isotropy_stratification_single_stratum
    (data : MappingTorusData X) :
    ∀ base : JanusDeckObject data,
      Nonempty ((base ⟶ base) ≃ PUnit) := by
  intro base
  exact ⟨janusDeckEndomorphismEquivPUnit data base⟩

end DeckCategory

section NaturalSourceTargetFamilies

variable {X : Type u} [TopologicalSpace X]

/-- One smooth component of the total deck-arrow space. -/
abbrev DeckArrowComponent (data : MappingTorusData X) :=
  Multiplicative ℤ × MappingTorusCover data

/-- Source map on the componentwise arrow presentation. -/
def deckSource (data : MappingTorusData X) :
    DeckArrowComponent data → MappingTorusCover data := fun arrow => arrow.2

/-- Target map on the componentwise arrow presentation. -/
def deckTarget (data : MappingTorusData X) :
    DeckArrowComponent data → MappingTorusCover data :=
  fun arrow => arrow.1.toAdd +ᵥ arrow.2

/-- The total-space presentation produces the corresponding dependent
action-groupoid arrow. -/
def deckComponentArrow (data : MappingTorusData X)
    (arrow : DeckArrowComponent data) :
    ActionArrow (Symmetry := Multiplicative ℤ)
      (deckSource data arrow) (deckTarget data arrow) where
  element := arrow.1
  maps_source := rfl

/-- Pullback of a dependent fiber family by the source map. -/
def SourcePullbackFiber (data : MappingTorusData X)
    (Fiber : MappingTorusCover data → Type v)
    (arrow : DeckArrowComponent data) : Type v :=
  Fiber (deckSource data arrow)

/-- Pullback of a dependent fiber family by the target map. -/
def TargetPullbackFiber (data : MappingTorusData X)
    (Fiber : MappingTorusCover data → Type v)
    (arrow : DeckArrowComponent data) : Type v :=
  Fiber (deckTarget data arrow)

/-- Natural transport from the source pullback family to the target pullback
family, reusing the existing equivariant-family descent core. -/
def sourceToTargetTransport
    (data : MappingTorusData X)
    (family : EquivariantFamily (Multiplicative ℤ)
      (MappingTorusCover data))
    (arrow : DeckArrowComponent data) :
    SourcePullbackFiber data family.Fiber arrow →
      TargetPullbackFiber data family.Fiber arrow :=
  family.transport (deckComponentArrow data arrow)

end NaturalSourceTargetFamilies

section StructuredJetFunctor

variable {X : Type u} [TopologicalSpace X]
variable {Symmetry : Type v} {Jet : Type w}

/-- Wrapper carrying the existing structured action groupoid as a Mathlib
category without installing a category instance on the ambient jet type. -/
structure StructuredJetActionObject (Symmetry : Type v) (Jet : Type w) where
  val : Jet

@[ext]
theorem StructuredJetActionObject.ext
    {first second : StructuredJetActionObject Symmetry Jet}
    (h : first.val = second.val) : first = second := by
  cases first
  cases second
  cases h
  rfl

variable [Group Symmetry] [MulAction Symmetry Jet]

instance structuredJetObjectMulAction :
    MulAction Symmetry (StructuredJetActionObject Symmetry Jet) where
  smul symmetry jet := ⟨symmetry • jet.val⟩
  one_smul jet := by
    apply StructuredJetActionObject.ext
    exact one_smul Symmetry jet.val
  mul_smul first second jet := by
    apply StructuredJetActionObject.ext
    exact mul_smul first second jet.val

instance structuredJetCategoryStruct :
    CategoryStruct (StructuredJetActionObject Symmetry Jet) where
  Hom source target := ActionArrow (Symmetry := Symmetry) source target
  id base := idArrow base
  comp first second := P0EFTJanusStructuredJetActionGroupoid.comp second first

instance structuredJetCategory :
    Category (StructuredJetActionObject Symmetry Jet) where
  id_comp arrow := P0EFTJanusStructuredJetActionGroupoid.comp_id arrow
  comp_id arrow := P0EFTJanusStructuredJetActionGroupoid.id_comp arrow
  assoc first second third :=
    P0EFTJanusStructuredJetActionGroupoid.comp_assoc first second third

instance structuredJetGroupoid :
    Groupoid (StructuredJetActionObject Symmetry Jet) where
  inv arrow := P0EFTJanusStructuredJetActionGroupoid.inverse arrow
  inv_comp arrow := P0EFTJanusStructuredJetActionGroupoid.comp_inverse arrow
  comp_inv arrow := P0EFTJanusStructuredJetActionGroupoid.inverse_comp arrow

/-- A structured-jet family equivariant for a representation of the deck
group.  This is the exact datum needed to send deck arrows to structured-jet
action arrows. -/
structure StructuredJetDeckRepresentation (data : MappingTorusData X) where
  symmetryHom : Multiplicative ℤ →* Symmetry
  jet : MappingTorusCover data → Jet
  equivariant : ∀ (deck : Multiplicative ℤ)
      (point : MappingTorusCover data),
    symmetryHom deck • jet point = jet (deck.toAdd +ᵥ point)

/-- The deck presentation acts functorially on structured jets.  Identity and
composition are inherited from the existing action-groupoid core. -/
def StructuredJetDeckRepresentation.toFunctor
    (data : MappingTorusData X)
    (representation : StructuredJetDeckRepresentation
      (Symmetry := Symmetry) (Jet := Jet) data) :
    JanusDeckObject data ⥤ StructuredJetActionObject Symmetry Jet where
  obj point := ⟨representation.jet point⟩
  map {source target} arrow :=
    { element := representation.symmetryHom arrow.element
      maps_source := by
        apply StructuredJetActionObject.ext
        exact (representation.equivariant arrow.element source).trans
          (congrArg representation.jet arrow.maps_source) }
  map_id base := by
    apply ActionArrow.ext
    exact representation.symmetryHom.map_one
  map_comp first second := by
    apply ActionArrow.ext
    exact representation.symmetryHom.map_mul second.element first.element

/-- The underlying symmetry element of the image arrow is exactly the deck
representation, with no extra choice of overlap transition. -/
@[simp]
theorem StructuredJetDeckRepresentation.toFunctor_map_element
    (data : MappingTorusData X)
    (representation : StructuredJetDeckRepresentation
      (Symmetry := Symmetry) (Jet := Jet) data)
    {source target : JanusDeckObject data}
    (arrow : source ⟶ target) :
    ((representation.toFunctor data).map arrow).element =
      representation.symmetryHom arrow.element :=
  rfl

end StructuredJetFunctor

section ComponentwiseSmoothGroupoid

variable {𝕜 E H X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace X]

variable (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

/-- A smooth deck transformation as an actual diffeomorphism of the cover. -/
def deckDiffeomorph
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data))
    (winding : ℤ) :
    MappingTorusCover data ≃ₘ^n⟮I, I⟯ MappingTorusCover data where
  toEquiv := (Homeomorph.vadd winding).toEquiv
  contMDiff_toFun := hDeck winding
  contMDiff_invFun := by
    convert hDeck (-winding) using 1
    funext point
    simp

/-- Every target component of the deck groupoid is etale.  The source
component is the identity, so the componentwise arrow presentation is an
etale differentiable groupoid. -/
theorem deckTargetComponent_isLocalDiffeomorph
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data))
    (winding : ℤ) :
    IsLocalDiffeomorph I I n
      (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data) := by
  exact (deckDiffeomorph I n data hDeck winding).isLocalDiffeomorph

/-- The source component is an etale map as well. -/
theorem deckSourceComponent_isLocalDiffeomorph
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)] :
    IsLocalDiffeomorph I I n
      (id : MappingTorusCover data → MappingTorusCover data) := by
  exact (Diffeomorph.refl I (MappingTorusCover data) n).isLocalDiffeomorph

end ComponentwiseSmoothGroupoid

section SmoothEffectiveDescent

variable {𝕜 E H E' H' X Target : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace X] [TopologicalSpace Target]

variable (I : ModelWithCorners 𝕜 E H)
  (J : ModelWithCorners 𝕜 E' H') (n : ℕ∞ω)

/-- A smooth map on the cover satisfying the exact deck cocycle needed for
descent to the effective quotient. -/
structure SmoothDeckInvariantMap
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)]
    [ChartedSpace H' Target] where
  toFun : MappingTorusCover data → Target
  invariant : ∀ (winding : ℤ) (point : MappingTorusCover data),
    toFun (winding +ᵥ point) = toFun point
  contMDiff : ContMDiff I J n toFun

instance (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)] [ChartedSpace H' Target] :
    CoeFun (SmoothDeckInvariantMap (Target := Target)
      (I := I) (J := J) (n := n) data) fun _ =>
      MappingTorusCover data → Target := ⟨SmoothDeckInvariantMap.toFun⟩

/-- Set-theoretic descent through the orbit quotient. -/
def SmoothDeckInvariantMap.descended
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)] [ChartedSpace H' Target]
    (family : SmoothDeckInvariantMap (Target := Target)
      (I := I) (J := J) (n := n) data) :
    MappingTorus data → Target :=
  Quotient.lift family.toFun (by
    intro first second hOrbit
    change AddAction.orbitRel ℤ (MappingTorusCover data) first second at hOrbit
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
    obtain ⟨winding, hWinding⟩ := hOrbit
    calc
      family.toFun first = family.toFun (winding +ᵥ second) :=
        congrArg family.toFun hWinding.symm
      _ = family.toFun second := family.invariant winding second)

@[simp]
theorem SmoothDeckInvariantMap.descended_mk
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)] [ChartedSpace H' Target]
    (family : SmoothDeckInvariantMap (Target := Target)
      (I := I) (J := J) (n := n) data)
    (point : MappingTorusCover data) :
    family.descended I J n data (mappingTorusMk data point) = family.toFun point :=
  rfl

/-- Smooth deck-invariant data descend smoothly to the actual quotient
manifold.  Smoothness is proved with the local inverses of the quotient local
diffeomorphism, rather than postulated as quotient regularity. -/
theorem SmoothDeckInvariantMap.descended_contMDiff
    (data : MappingTorusData X)
    [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace H (MappingTorusCover data)]
    [IsManifold I n (MappingTorusCover data)] [ChartedSpace H' Target]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data))
    (family : SmoothDeckInvariantMap (Target := Target)
      (I := I) (J := J) (n := n) data) :
    letI : ChartedSpace H (MappingTorus data) :=
      mappingTorusSmoothChartedSpace data
    ContMDiff I J n (family.descended I J n data) := by
  letI : ChartedSpace H (MappingTorus data) :=
    mappingTorusSmoothChartedSpace data
  letI : IsManifold I n (MappingTorus data) :=
    mappingTorus_isManifold_of_smooth_deck I n data hDeck
  intro quotientPoint
  obtain ⟨anchor, rfl⟩ := mappingTorusMk_surjective data quotientPoint
  have hProjection :=
    mappingTorus_projection_isLocalDiffeomorph I n data hDeck
  have hLocal := hProjection anchor
  have hRepresentative : ContMDiffAt I J n
      (family.toFun ∘ hLocal.localInverse)
      (mappingTorusMk data anchor) :=
    family.contMDiff.contMDiffAt.comp _ hLocal.localInverse_contMDiffAt
  apply hRepresentative.congr_of_eventuallyEq
  filter_upwards [hLocal.localInverse_eventuallyEq_right] with point hPoint
  change family.descended I J n data point = family.toFun (hLocal.localInverse point)
  simpa using congrArg (family.descended I J n data) hPoint.symm

/-- Effective smooth descent: the descended map is the unique smooth map with
the prescribed pullback. -/
theorem SmoothDeckInvariantMap.existsUnique_descended_contMDiff
    (data : MappingTorusData X)
    [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace H (MappingTorusCover data)]
    [IsManifold I n (MappingTorusCover data)] [ChartedSpace H' Target]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data))
    (family : SmoothDeckInvariantMap (Target := Target)
      (I := I) (J := J) (n := n) data) :
    letI : ChartedSpace H (MappingTorus data) :=
      mappingTorusSmoothChartedSpace data
    ∃! descended : MappingTorus data → Target,
      ContMDiff I J n descended ∧
      ∀ point : MappingTorusCover data,
        descended (mappingTorusMk data point) = family.toFun point := by
  letI : ChartedSpace H (MappingTorus data) :=
    mappingTorusSmoothChartedSpace data
  refine ⟨family.descended I J n data, ?_, ?_⟩
  · exact ⟨family.descended_contMDiff I J n data hDeck,
      family.descended_mk I J n data⟩
  · intro other hOther
    funext quotientPoint
    obtain ⟨point, rfl⟩ := mappingTorusMk_surjective data quotientPoint
    rw [hOther.2]
    exact (family.descended_mk I J n data point).symm

end SmoothEffectiveDescent

section D8SmoothQuotients

open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient

variable (period : ℝ) (hPeriod : period ≠ 0)

/-- The integer-arrow components presenting the actual reflected-sphere D8
quotient are analytic local diffeomorphisms. -/
theorem reflectedSphereDeckComponent_isLocalDiffeomorph
    (winding : ℤ) :
    letI : ChartedSpace CoverModel
        (MappingTorusCover (reflectedSphereData period hPeriod)) :=
      reflectedSphereCoverChartedSpace period hPeriod
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ω
      (winding +ᵥ · :
        MappingTorusCover (reflectedSphereData period hPeriod) →
          MappingTorusCover (reflectedSphereData period hPeriod)) := by
  letI : ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCoverChartedSpace period hPeriod
  exact deckTargetComponent_isLocalDiffeomorph coverModelWithCorners ω
    (reflectedSphereData period hPeriod)
    (reflectedSphereCover_deck_contMDiff period hPeriod) winding

/-- The integer-arrow components presenting the actual fixed-throat quotient
are analytic local diffeomorphisms. -/
theorem fixedThroatDeckComponent_isLocalDiffeomorph
    (winding : ℤ) :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorusCover (fixedEquatorData period hPeriod)) :=
      fixedThroatCoverChartedSpace period hPeriod
    IsLocalDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners ω
      (winding +ᵥ · :
        MappingTorusCover (fixedEquatorData period hPeriod) →
          MappingTorusCover (fixedEquatorData period hPeriod)) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCoverChartedSpace period hPeriod
  exact deckTargetComponent_isLocalDiffeomorph throatCoverModelWithCorners ω
    (fixedEquatorData period hPeriod)
    (fixedThroatCover_deck_contMDiff period hPeriod) winding

variable {F TargetModel Target : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace TargetModel] [TopologicalSpace Target]
  [ChartedSpace TargetModel Target]

/-- Effective analytic descent specialized to the actual reflected-sphere D8
quotient. -/
theorem reflectedSphere_existsUnique_smooth_descent
    (J : ModelWithCorners ℝ F TargetModel) :
    letI : ChartedSpace CoverModel
        (MappingTorusCover (reflectedSphereData period hPeriod)) :=
      reflectedSphereCoverChartedSpace period hPeriod
    ∀ family : SmoothDeckInvariantMap (Target := Target)
        (I := coverModelWithCorners) (J := J) (n := ω)
        (reflectedSphereData period hPeriod),
      letI : ChartedSpace CoverModel
          (MappingTorus (reflectedSphereData period hPeriod)) :=
        reflectedSphereQuotientChartedSpace period hPeriod
      ∃! descended : MappingTorus (reflectedSphereData period hPeriod) → Target,
        ContMDiff coverModelWithCorners J ω descended ∧
        ∀ point : MappingTorusCover (reflectedSphereData period hPeriod),
          descended (mappingTorusMk (reflectedSphereData period hPeriod) point) =
            family.toFun point := by
  letI : ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCover_isManifold period hPeriod
  intro family
  letI : ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  exact family.existsUnique_descended_contMDiff
    coverModelWithCorners J ω (reflectedSphereData period hPeriod)
      (reflectedSphereCover_deck_contMDiff period hPeriod)

end D8SmoothQuotients

section StructuredJets

variable {E H X Tangent Normal : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X]
  [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
  [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]

variable (I : ModelWithCorners ℝ E H) (n : ℕ∞)

/-- A deck-invariant smooth low-order structured jet together with a genuine
local coefficient realization at every cover point. -/
structure SmoothDeckHolonomicStructuredJetFamily
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)] extends
    SmoothDeckInvariantMap
      (Target := SmoothLowOrderStructuredJet Tangent Normal) (I := I)
      (J := 𝓘(ℝ, SmoothLowOrderStructuredJet Tangent Normal))
      (n := n) data where
  localRealization : ∀ point : MappingTorusCover data,
    ∃ localData : ActualJanusLocalJetData
        (Tangent := Tangent) (Normal := Normal),
      localData.toStructuredJet = toFun point

variable (data : MappingTorusData X)
variable [ChartedSpace H (MappingTorusCover data)]

/-- Forget the pointwise holonomic witness and retain the smooth descent
datum. -/
def SmoothDeckHolonomicStructuredJetFamily.toInvariantMap
    (family : SmoothDeckHolonomicStructuredJetFamily
      (Tangent := Tangent) (Normal := Normal) I n data) :
    SmoothDeckInvariantMap
      (Target := SmoothLowOrderStructuredJet Tangent Normal) (I := I)
      (J := 𝓘(ℝ, SmoothLowOrderStructuredJet Tangent Normal))
      (n := n) data :=
  family.toSmoothDeckInvariantMap

/-- The descended structured jet remains pointwise holonomic: choose any
cover representative and reuse its actual local coefficient package. -/
theorem SmoothDeckHolonomicStructuredJetFamily.descended_is_holonomic
    (family : SmoothDeckHolonomicStructuredJetFamily
      (Tangent := Tangent) (Normal := Normal) I n data)
    (quotientPoint : MappingTorus data) :
    ∃ localData : ActualJanusLocalJetData
        (Tangent := Tangent) (Normal := Normal),
      localData.toStructuredJet =
        (family.toInvariantMap I n data).descended I _ n data quotientPoint := by
  obtain ⟨point, rfl⟩ := mappingTorusMk_surjective data quotientPoint
  obtain ⟨localData, hLocal⟩ := family.localRealization point
  exact ⟨localData, hLocal.trans
    ((family.toInvariantMap I n data).descended_mk I _ n data point).symm⟩

/-- Reduction to `(II,F)` commutes exactly with quotient descent. -/
def SmoothDeckHolonomicStructuredJetFamily.descendedReducedJet
    (family : SmoothDeckHolonomicStructuredJetFamily
      (Tangent := Tangent) (Normal := Normal) I n data) :
    MappingTorus data → SmoothLowOrderReducedJet
      (Tangent := Tangent) (Normal := Normal) :=
  smoothLowOrderReduction ∘
    (family.toInvariantMap I n data).descended I _ n data

@[simp]
theorem SmoothDeckHolonomicStructuredJetFamily.descendedReducedJet_mk
    (family : SmoothDeckHolonomicStructuredJetFamily
      (Tangent := Tangent) (Normal := Normal) I n data)
    (point : MappingTorusCover data) :
    family.descendedReducedJet I n data (mappingTorusMk data point) =
      smoothLowOrderReduction (family.toFun point) := by
  rfl

/-- Smooth integrability of the reduced low-order jet on the installed
quotient manifold. -/
theorem SmoothDeckHolonomicStructuredJetFamily.descendedReducedJet_contMDiff
    [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal]
    [T2Space X] [LocallyCompactSpace X]
    [IsManifold I n (MappingTorusCover data)]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data))
    (family : SmoothDeckHolonomicStructuredJetFamily
      (Tangent := Tangent) (Normal := Normal) I n data) :
    letI : ChartedSpace H (MappingTorus data) :=
      mappingTorusSmoothChartedSpace data
    ContMDiff I
      𝓘(ℝ, SmoothLowOrderReducedJet
        (Tangent := Tangent) (Normal := Normal)) n
      (family.descendedReducedJet I n data) := by
  letI : ChartedSpace H (MappingTorus data) :=
    mappingTorusSmoothChartedSpace data
  have hReduction : ContDiff ℝ (n : ℕ∞ω)
      (smoothLowOrderReduction
        (Tangent := Tangent) (Normal := Normal)) :=
    (smoothLowOrderReduction_contDiff
      (Tangent := Tangent) (Normal := Normal)).of_le
        (WithTop.coe_le_coe.mpr le_top)
  exact hReduction.comp_contMDiff
    ((family.toInvariantMap I n data).descended_contMDiff
      I _ n data hDeck)

end StructuredJets

end

end P0EFTJanusMappingTorusStructuredJetGroupoid
end JanusFormal
