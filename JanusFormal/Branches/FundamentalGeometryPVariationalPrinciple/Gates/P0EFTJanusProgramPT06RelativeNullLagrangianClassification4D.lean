import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D

/-!
# Relative null-Lagrangian classification for T06

This gate classifies every horizontal density in the concrete relative
four-stratum bicomplex used by T05.  Vanishing of its Euler class is equivalent
to being an actual horizontal boundary.  Boundary primitives have one
canonical normalized representative; the remaining freedom is exactly a
closed boundary cochain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D

local notation "C" => ProgramPT05PhysicalJetComponent
local notation "Bicomplex" => programPT05ExactT03RelativeBicomplex

/-- Top-degree relative densities in the T05 realization. -/
abbrev ProgramPT06RelativeDensity4D := RelativeJetCochain C 4 0

/-- Relative boundary primitives in the T05 realization. -/
abbrev ProgramPT06RelativeBoundaryPrimitive4D := RelativeJetCochain C 3 0

/-- A degree-zero horizontal density uses the density coordinate of each
T05 pair and has no contact coordinate. -/
def IsHorizontalDensity
    (density : ProgramPT06RelativeDensity4D) : Prop :=
  ∀ stratum, (density stratum).2 = 0

/-- A relative density is variationally null when its vertical variation is
an actual horizontal boundary. -/
def IsRelativeNullLagrangian
    (density : ProgramPT06RelativeDensity4D) : Prop :=
  ∃ boundaryPotential : RelativeJetCochain C 3 1,
    (Bicomplex).dV 4 0 density =
      (Bicomplex).dH 3 1 boundaryPotential

/-- A top relative density is a boundary term when it is in the image of the
horizontal differential. -/
def IsRelativeBoundaryTerm
    (density : ProgramPT06RelativeDensity4D) : Prop :=
  ∃ primitive : ProgramPT06RelativeBoundaryPrimitive4D,
    (Bicomplex).dH 3 0 primitive = density

/-- Closed relative boundary primitives are precisely the ambiguity between
two primitives representing the same boundary density. -/
def IsClosedRelativeBoundaryPrimitive
    (primitive : ProgramPT06RelativeBoundaryPrimitive4D) : Prop :=
  (Bicomplex).dH 3 0 primitive = 0

/-- Normalization fixes the components invisible to the outgoing incidence
map. -/
def IsNormalizedRelativeBoundaryPrimitive
    (primitive : ProgramPT06RelativeBoundaryPrimitive4D) : Prop :=
  primitive .nullBoundary = 0 ∧ primitive .joint = 0

/-- Complete component test for variational nullity in the concrete T05
bicomplex. -/
theorem isRelativeNullLagrangian_iff_components
    (density : ProgramPT06RelativeDensity4D) :
    IsRelativeNullLagrangian density ↔
      (density .bulk).1 = 0 ∧
        (density .nonNullBoundary).1 = (density .nullBoundary).1 := by
  constructor
  · rintro ⟨boundaryPotential, hVariation⟩
    have hBulk := congrArg Prod.snd (congrFun hVariation .bulk)
    have hNonNull :=
      congrArg Prod.snd (congrFun hVariation .nonNullBoundary)
    have hNull := congrArg Prod.snd (congrFun hVariation .nullBoundary)
    norm_num [programPT05ExactT03RelativeBicomplex,
      programPT05RelativeVerticalDifferential,
      programPT05RelativeHorizontalDifferential] at hBulk hNonNull hNull
    exact ⟨hBulk, hNonNull.trans hNull.symm⟩
  · rintro ⟨hBulk, hFaces⟩
    let boundaryPotential : RelativeJetCochain C 3 1 := fun
      | .bulk => (0, (density .nonNullBoundary).1)
      | .nonNullBoundary => (0, (density .joint).1)
      | .nullBoundary => 0
      | .joint => 0
    refine ⟨boundaryPotential, ?_⟩
    funext stratum
    cases stratum <;>
      apply Prod.ext <;>
      norm_num [boundaryPotential, programPT05ExactT03RelativeBicomplex,
        programPT05RelativeVerticalDifferential,
        programPT05RelativeHorizontalDifferential, hBulk, hFaces]

/-- Complete image test for relative boundary densities. -/
theorem isRelativeBoundaryTerm_iff_components
    (density : ProgramPT06RelativeDensity4D) :
    IsRelativeBoundaryTerm density ↔
      density .bulk = 0 ∧
        density .nonNullBoundary = density .nullBoundary := by
  constructor
  · rintro ⟨primitive, hPrimitive⟩
    have hBulk := congrFun hPrimitive .bulk
    have hNonNull := congrFun hPrimitive .nonNullBoundary
    have hNull := congrFun hPrimitive .nullBoundary
    simp [programPT05ExactT03RelativeBicomplex,
      programPT05RelativeHorizontalDifferential] at hBulk hNonNull hNull
    exact ⟨hBulk.symm, hNonNull.symm.trans hNull⟩
  · rintro ⟨hBulk, hFaces⟩
    let primitive : ProgramPT06RelativeBoundaryPrimitive4D := fun
      | .bulk => density .nonNullBoundary
      | .nonNullBoundary => density .joint
      | .nullBoundary => 0
      | .joint => 0
    refine ⟨primitive, ?_⟩
    funext stratum
    cases stratum <;>
      simp [primitive, programPT05ExactT03RelativeBicomplex,
        programPT05RelativeHorizontalDifferential, hBulk, hFaces]

/-- Exhaustion theorem: among all horizontal densities in the relative T05
carrier, the null Lagrangians are exactly the boundary terms. -/
theorem horizontalDensity_null_iff_boundary
    (density : ProgramPT06RelativeDensity4D)
    (hHorizontal : IsHorizontalDensity density) :
    IsRelativeNullLagrangian density ↔ IsRelativeBoundaryTerm density := by
  rw [isRelativeNullLagrangian_iff_components,
    isRelativeBoundaryTerm_iff_components]
  constructor
  · rintro ⟨hBulk, hFaces⟩
    constructor
    · apply Prod.ext
      · exact hBulk
      · exact hHorizontal .bulk
    · apply Prod.ext
      · exact hFaces
      · exact (hHorizontal .nonNullBoundary).trans
          (hHorizontal .nullBoundary).symm
  · rintro ⟨hBulk, hFaces⟩
    exact ⟨congrArg Prod.fst hBulk,
      congrArg Prod.fst hFaces⟩

/-- Closed boundary primitives have no bulk component and equal non-null and
null face components; the joint component is the expected free cocycle. -/
theorem isClosedRelativeBoundaryPrimitive_iff_components
    (primitive : ProgramPT06RelativeBoundaryPrimitive4D) :
    IsClosedRelativeBoundaryPrimitive primitive ↔
      primitive .bulk = 0 ∧
        primitive .nonNullBoundary = primitive .nullBoundary := by
  change (Bicomplex).dH 3 0 primitive = 0 ↔ _
  constructor
  · intro hClosed
    have hNonNull := congrFun hClosed .nonNullBoundary
    have hNull := congrFun hClosed .nullBoundary
    have hJoint := congrFun hClosed .joint
    simp [programPT05ExactT03RelativeBicomplex,
      programPT05RelativeHorizontalDifferential] at hNonNull hNull hJoint
    exact ⟨hNonNull, sub_eq_zero.mp hJoint⟩
  · rintro ⟨hBulk, hFaces⟩
    funext stratum
    cases stratum <;>
      simp [programPT05ExactT03RelativeBicomplex,
        programPT05RelativeHorizontalDifferential, hBulk, hFaces]

/-- Canonical representative of a boundary density. -/
def canonicalRelativeBoundaryPrimitive
    (density : ProgramPT06RelativeDensity4D) :
    ProgramPT06RelativeBoundaryPrimitive4D
  | .bulk => density .nonNullBoundary
  | .nonNullBoundary => density .joint
  | .nullBoundary => 0
  | .joint => 0

@[simp] theorem canonicalRelativeBoundaryPrimitive_normalized
    (density : ProgramPT06RelativeDensity4D) :
    IsNormalizedRelativeBoundaryPrimitive
      (canonicalRelativeBoundaryPrimitive density) := by
  simp [IsNormalizedRelativeBoundaryPrimitive,
    canonicalRelativeBoundaryPrimitive]

/-- Every relative boundary term has a unique normalized primitive. -/
theorem relativeBoundaryTerm_existsUnique_normalizedPrimitive
    (density : ProgramPT06RelativeDensity4D)
    (hBoundary : IsRelativeBoundaryTerm density) :
    ∃! primitive : ProgramPT06RelativeBoundaryPrimitive4D,
      IsNormalizedRelativeBoundaryPrimitive primitive ∧
        (Bicomplex).dH 3 0 primitive = density := by
  have hComponents :=
    (isRelativeBoundaryTerm_iff_components density).1 hBoundary
  refine ⟨canonicalRelativeBoundaryPrimitive density, ?_, ?_⟩
  · constructor
    · exact canonicalRelativeBoundaryPrimitive_normalized density
    · funext stratum
      cases stratum <;>
        simp [canonicalRelativeBoundaryPrimitive,
          programPT05ExactT03RelativeBicomplex,
          programPT05RelativeHorizontalDifferential,
          hComponents.1, hComponents.2]
  · intro primitive hPrimitive
    rcases hPrimitive.1 with ⟨hNull, hJoint⟩
    funext stratum
    cases stratum with
    | bulk =>
        have hComponent := congrFun hPrimitive.2 .nonNullBoundary
        simpa [canonicalRelativeBoundaryPrimitive,
          programPT05ExactT03RelativeBicomplex,
          programPT05RelativeHorizontalDifferential] using hComponent
    | nonNullBoundary =>
        have hComponent := congrFun hPrimitive.2 .joint
        simpa [canonicalRelativeBoundaryPrimitive,
          programPT05ExactT03RelativeBicomplex,
          programPT05RelativeHorizontalDifferential, hNull] using hComponent
    | nullBoundary =>
        simpa [canonicalRelativeBoundaryPrimitive] using hNull
    | joint =>
        simpa [canonicalRelativeBoundaryPrimitive] using hJoint

end

end P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D
end JanusFormal
