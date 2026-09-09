import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFaceMobileGeometricRealization4D

/-!
# Canonical faithfulness of the mobile finite null-face projection

The mobile geometric realization has a canonical map from its admissible
physical coordinates to the existing reduced null-face action data.  The
geometric laws alone do not make this map injective: the target remembers the
area, expansion, inaffinity, normalization and endpoint-joint actions, but it
does not store the embedding, defining function or ambient metric.

This gate records the exact observational kernel of that canonical map.  It
then isolates the minimal additional condition needed by a terminal physical
null block: equality of all reduced action data on every face must recover the
original position/screen coordinate.  An optional explicit recovery map gives
a constructive sufficient witness and produces the required injectivity.

No injectivity is inferred from the geometric equations themselves.  A later
mapping-torus construction must prove the recovery law for its chosen mobile
chart, or use the collision theorem below to expose a genuine obstruction.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFacePhysicalActionRealization4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D

/-- Admissible coordinates of one mobile null-face chart. -/
abbrev FiniteNullFaceMobileAdmissibleState
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace) :=
  { input : FiniteNullFacePhysicalHilbert NullFace //
      input ∈ geometry.domain }

/-- Canonical projection of an admissible mobile coordinate to all reduced
finite null-face action data. -/
def finiteNullFaceMobileCanonicalActionDatumMap
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace) :
    FiniteNullFaceMobileAdmissibleState geometry →
      (NullFace → FiniteNullFaceActionDatum) :=
  fun input face =>
    geometry.toFiniteNullFaceActionDatum input.1 face

/-- Two mobile coordinates are indistinguishable by the complete reduced
action datum precisely when every face has the same projected datum. -/
def FiniteNullFaceMobileActionIndistinguishable
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (first second : FiniteNullFacePhysicalHilbert NullFace) : Prop :=
  ∀ face,
    geometry.toFiniteNullFaceActionDatum first face =
      geometry.toFiniteNullFaceActionDatum second face

/-- Action indistinguishability is the equivalence relation which the reduced
null-face projection necessarily quotients by. -/
theorem finiteNullFaceMobileActionIndistinguishable_equivalence
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace) :
    Equivalence
      (FiniteNullFaceMobileActionIndistinguishable geometry) := by
  constructor
  · intro input face
    rfl
  · intro first second hEqual face
    exact (hEqual face).symm
  · intro first second third hFirst hSecond face
    exact (hFirst face).trans (hSecond face)

/-- The observational relation above is exactly the kernel pair of the
canonical action-datum map; no geometric field omitted by that map can refine
this relation. -/
theorem finiteNullFaceMobileCanonicalActionDatumMap_eq_iff
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (first second : FiniteNullFaceMobileAdmissibleState geometry) :
    finiteNullFaceMobileCanonicalActionDatumMap geometry first =
        finiteNullFaceMobileCanonicalActionDatumMap geometry second ↔
      FiniteNullFaceMobileActionIndistinguishable geometry first.1 second.1 := by
  constructor
  · intro hEqual face
    exact congrFun hEqual face
  · intro hEqual
    funext face
    exact hEqual face

/-- Minimal faithfulness condition for a physical mobile null chart: the
canonical reduced action data separate all admissible position/screen
coordinates. -/
def FiniteNullFaceMobileCanonicalActionFaithful
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace) : Prop :=
  Function.Injective
    (finiteNullFaceMobileCanonicalActionDatumMap geometry)

/-- Coordinate separation is an equivalent raw-state formulation of
canonical action faithfulness. -/
theorem finiteNullFaceMobileCanonicalActionFaithful_iff_separates
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace) :
    FiniteNullFaceMobileCanonicalActionFaithful geometry ↔
      ∀ first, first ∈ geometry.domain →
        ∀ second, second ∈ geometry.domain →
          FiniteNullFaceMobileActionIndistinguishable geometry first second →
            first = second := by
  constructor
  · intro hFaithful first hFirst second hSecond hEqual
    have hSubtype :
        (⟨first, hFirst⟩ : FiniteNullFaceMobileAdmissibleState geometry) =
          ⟨second, hSecond⟩ := by
      apply hFaithful
      funext face
      exact hEqual face
    exact congrArg Subtype.val hSubtype
  · intro hSeparates first second hEqual
    apply Subtype.ext
    apply hSeparates first.1 first.2 second.1 second.2
    intro face
    exact congrFun hEqual face

/-- Exact obstruction: one collision of distinct admissible coordinates in
the reduced action data rules out a faithful mobile realization. -/
theorem finiteNullFaceMobileCanonicalActionFaithful_not_of_collision
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (first second : FiniteNullFacePhysicalHilbert NullFace)
    (hFirst : first ∈ geometry.domain)
    (hSecond : second ∈ geometry.domain)
    (hDistinct : first ≠ second)
    (hCollision :
      FiniteNullFaceMobileActionIndistinguishable geometry first second) :
    ¬ FiniteNullFaceMobileCanonicalActionFaithful geometry := by
  intro hFaithful
  apply hDistinct
  exact
    (finiteNullFaceMobileCanonicalActionFaithful_iff_separates geometry).mp
      hFaithful first hFirst second hSecond hCollision

/-- Constructive recovery of the physical position/screen coordinate from
the canonical family of reduced face data.  The law is required only on the
open admissible domain. -/
structure FiniteNullFaceMobileActionCoordinateRecovery
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace) where
  recover :
    (NullFace → FiniteNullFaceActionDatum) →
      FiniteNullFacePhysicalHilbert NullFace
  recover_canonicalDatum :
    ∀ input, input ∈ geometry.domain →
      recover
          (fun face => geometry.toFiniteNullFaceActionDatum input face) =
        input

/-- An explicit coordinate recovery is a sufficient constructive witness of
canonical faithfulness. -/
theorem finiteNullFaceMobileCanonicalActionFaithful_of_recovery
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (recovery : FiniteNullFaceMobileActionCoordinateRecovery geometry) :
    FiniteNullFaceMobileCanonicalActionFaithful geometry := by
  intro first second hEqual
  apply Subtype.ext
  have hFirst := recovery.recover_canonicalDatum first.1 first.2
  have hSecond := recovery.recover_canonicalDatum second.1 second.2
  exact hFirst.symm.trans ((congrArg recovery.recover hEqual).trans hSecond)

/-- Classical recovery associated with an injective canonical datum map.  It
chooses the unique admissible preimage on the range and returns zero off the
range. -/
noncomputable def finiteNullFaceMobileActionCoordinateRecoveryOfFaithful
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (hFaithful : FiniteNullFaceMobileCanonicalActionFaithful geometry) :
    FiniteNullFaceMobileActionCoordinateRecovery geometry := by
  classical
  exact
    { recover := fun data =>
        if hPreimage : ∃ input : FiniteNullFaceMobileAdmissibleState geometry,
            finiteNullFaceMobileCanonicalActionDatumMap geometry input = data then
          (Classical.choose hPreimage).1
        else
          0
      recover_canonicalDatum := by
        intro input hInput
        have hPreimage :
            ∃ candidate : FiniteNullFaceMobileAdmissibleState geometry,
              finiteNullFaceMobileCanonicalActionDatumMap geometry candidate =
                (fun face =>
                  geometry.toFiniteNullFaceActionDatum input face) :=
          ⟨⟨input, hInput⟩, rfl⟩
        rw [dif_pos hPreimage]
        have hEqual :
            finiteNullFaceMobileCanonicalActionDatumMap geometry
                (Classical.choose hPreimage) =
              finiteNullFaceMobileCanonicalActionDatumMap geometry
                (⟨input, hInput⟩ : FiniteNullFaceMobileAdmissibleState geometry) :=
          Classical.choose_spec hPreimage
        exact congrArg Subtype.val
          (hFaithful hEqual) }

/-- Recovery and injectivity contain exactly the same information.  Thus the
recovery package adds no hidden geometric assumption beyond separation of the
physical coordinates by the canonical reduced data. -/
theorem finiteNullFaceMobileCanonicalActionFaithful_iff_recovery
    {NullFace : Type*} [Fintype NullFace]
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace) :
    FiniteNullFaceMobileCanonicalActionFaithful geometry ↔
      Nonempty (FiniteNullFaceMobileActionCoordinateRecovery geometry) := by
  constructor
  · intro hFaithful
    exact ⟨finiteNullFaceMobileActionCoordinateRecoveryOfFaithful
      geometry hFaithful⟩
  · rintro ⟨recovery⟩
    exact finiteNullFaceMobileCanonicalActionFaithful_of_recovery
      geometry recovery

/-- A mobile geometric action realization together with the missing faithful
coordinate-recovery certificate.  This is the minimal honest physical-null
package consumed by a terminal T03 construction. -/
structure FiniteNullFaceMobileCanonicalFaithfulActionRealization
    (NullFace : Type*) [Fintype NullFace] where
  realization : FiniteNullFaceMobileGeometricActionRealization NullFace
  coordinateRecovery :
    FiniteNullFaceMobileActionCoordinateRecovery realization.geometry

/-- The bundled recovery makes the canonical mobile action-datum projection
injective on its admissible domain. -/
theorem FiniteNullFaceMobileCanonicalFaithfulActionRealization.actionDatum_injective
    {NullFace : Type*} [Fintype NullFace]
    (faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace) :
    FiniteNullFaceMobileCanonicalActionFaithful
      faithful.realization.geometry :=
  finiteNullFaceMobileCanonicalActionFaithful_of_recovery
    faithful.realization.geometry faithful.coordinateRecovery

/-- Forgetting only the recovery certificate gives the already constructed
physical action realization, so all action and Euler agreement theorems remain
available definitionally. -/
def FiniteNullFaceMobileCanonicalFaithfulActionRealization.toPhysicalActionRealization
    {NullFace : Type*} [Fintype NullFace]
    (faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace) :
    FiniteNullFacePhysicalActionRealization NullFace :=
  faithful.realization.toPhysicalActionRealization

@[simp] theorem FiniteNullFaceMobileCanonicalFaithfulActionRealization.toPhysicalActionRealization_domain
    {NullFace : Type*} [Fintype NullFace]
    (faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace) :
    faithful.toPhysicalActionRealization.domain =
      faithful.realization.geometry.domain :=
  rfl

/-- Equality of canonical reduced data recovers equality of the underlying
admissible physical null coordinates. -/
theorem FiniteNullFaceMobileCanonicalFaithfulActionRealization.eq_of_toDatum_eq
    {NullFace : Type*} [Fintype NullFace]
    (faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (first second : FiniteNullFacePhysicalHilbert NullFace)
    (hFirst : first ∈ faithful.realization.geometry.domain)
    (hSecond : second ∈ faithful.realization.geometry.domain)
    (hEqual : ∀ face,
      faithful.realization.geometry.toFiniteNullFaceActionDatum first face =
        faithful.realization.geometry.toFiniteNullFaceActionDatum second face) :
    first = second :=
  (finiteNullFaceMobileCanonicalActionFaithful_iff_separates
      faithful.realization.geometry).mp
    faithful.actionDatum_injective first hFirst second hSecond hEqual

/-- The faithful wrapper retains exact agreement with the concrete mobile
geometric relative action. -/
theorem FiniteNullFaceMobileCanonicalFaithfulActionRealization.action_eq_geometric
    {NullFace : Type*} [Fintype NullFace]
    (faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    faithful.toPhysicalActionRealization.toActionModel.action input =
      finiteNullFaceMobileGeometricRelativeAction faithful.realization input :=
  rfl

/-- On the admissible domain, the faithful physical-null Euler covector is
still the derivative of the concrete finite face-plus-joint action. -/
theorem FiniteNullFaceMobileCanonicalFaithfulActionRealization.euler_eq_fderiv
    {NullFace : Type*} [Fintype NullFace]
    (faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ faithful.realization.geometry.domain) :
    finiteNullFacePhysicalEuler
        faithful.toPhysicalActionRealization.toActionModel input =
      fderiv Real
        (finiteNullFaceMobileGeometricTotalAction
          faithful.realization.geometry) input :=
  finiteNullFacePhysicalEuler_geometric_eq_fderiv
    faithful.realization input hInput

end
end P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
end JanusFormal
