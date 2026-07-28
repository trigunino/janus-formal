import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D

/-!
# Coadjoint antifield BRST representation

Every geometric ghost representation induces canonically the contragredient
representation on algebraic antifields.  This gate constructs that action,
proves its bracket identity, and obtains the corresponding nonlinear BRST
square-zero statement without a new assumption.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCoadjointAntifieldBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev Ghost :=
  CInfinityDiffeomorphismGhost period hPeriod

/-- Algebraic antifields paired linearly with a geometric field module. -/
abbrev AlgebraicAntifield (Field : Type*) [AddCommGroup Field]
    [Module Real Field] :=
  Field →ₗ[Real] Real

/-- Coadjoint convention `L_c^* α = - α ∘ L_c`. -/
def coadjointGhostAction
    {Field : Type*} [AddCommGroup Field] [Module Real Field]
    (representation :
      SmoothGhostLieRepresentation period hPeriod Field) :
    Ghost period hPeriod →ₗ[Real]
      AlgebraicAntifield Field →ₗ[Real] AlgebraicAntifield Field where
  toFun ghost :=
    { toFun := fun antifield =>
        { toFun := fun field =>
            -antifield (representation.action ghost field)
          map_add' := by
            intro first second
            simp
            abel
          map_smul' := by
            intro coefficient field
            simp }
      map_add' := by
        intro first second
        ext field
        simp
        abel
      map_smul' := by
        intro coefficient antifield
        ext field
        simp }
  map_add' := by
    intro first second
    ext antifield field
    simp
    abel
  map_smul' := by
    intro coefficient ghost
    ext antifield field
    simp

@[simp]
theorem coadjointGhostAction_apply
    {Field : Type*} [AddCommGroup Field] [Module Real Field]
    (representation :
      SmoothGhostLieRepresentation period hPeriod Field)
    (ghost : Ghost period hPeriod)
    (antifield : AlgebraicAntifield Field)
    (field : Field) :
    coadjointGhostAction period hPeriod representation ghost antifield field =
      -antifield (representation.action ghost field) :=
  rfl

/-- The coadjoint action is itself a genuine Lie representation. -/
theorem coadjointGhostAction_bracket
    {Field : Type*} [AddCommGroup Field] [Module Real Field]
    (representation :
      SmoothGhostLieRepresentation period hPeriod Field)
    (first second : Ghost period hPeriod)
    (antifield : AlgebraicAntifield Field) :
    coadjointGhostAction period hPeriod representation
        (smoothGhostLieBracket period hPeriod first second) antifield =
      coadjointGhostAction period hPeriod representation first
          (coadjointGhostAction period hPeriod representation second
            antifield) -
        coadjointGhostAction period hPeriod representation second
          (coadjointGhostAction period hPeriod representation first
            antifield) := by
  apply LinearMap.ext
  intro field
  simp only [coadjointGhostAction_apply, LinearMap.sub_apply, neg_neg]
  rw [representation.bracket_action]
  simp

def coadjointGhostLieRepresentation
    {Field : Type*} [AddCommGroup Field] [Module Real Field]
    (representation :
      SmoothGhostLieRepresentation period hPeriod Field) :
    SmoothGhostLieRepresentation period hPeriod
      (AlgebraicAntifield Field) where
  action := coadjointGhostAction period hPeriod representation
  bracket_action :=
    coadjointGhostAction_bracket period hPeriod representation

/-- Field and antifield representations are now produced from one datum. -/
structure FieldAntifieldLieRepresentation
    (Field : Type*) [AddCommGroup Field] [Module Real Field] where
  field :
    SmoothGhostLieRepresentation period hPeriod Field
  antifield :
    SmoothGhostLieRepresentation period hPeriod
      (AlgebraicAntifield Field)
  antifield_eq_coadjoint :
    antifield = coadjointGhostLieRepresentation period hPeriod field

def canonicalFieldAntifieldLieRepresentation
    {Field : Type*} [AddCommGroup Field] [Module Real Field]
    (representation :
      SmoothGhostLieRepresentation period hPeriod Field) :
    FieldAntifieldLieRepresentation period hPeriod Field where
  field := representation
  antifield :=
    coadjointGhostLieRepresentation period hPeriod representation
  antifield_eq_coadjoint := rfl

theorem coadjoint_antifield_nonlinear_brst_pair_square_zero
    {Field : Type*} [AddCommGroup Field] [Module Real Field]
    (representation :
      SmoothGhostLieRepresentation period hPeriod Field)
    (first second : Ghost period hPeriod)
    (antifield : AlgebraicAntifield Field) :
    lieRepresentationBRSTPairObstruction period hPeriod
      (coadjointGhostLieRepresentation period hPeriod representation)
      first second antifield = 0 :=
  lieRepresentationBRSTPairObstruction_zero period hPeriod
    (coadjointGhostLieRepresentation period hPeriod representation)
    first second antifield

/-- Canonical field-antifield evaluation pairing. -/
def fieldAntifieldPairing
    {Field : Type*} [AddCommGroup Field] [Module Real Field]
    (antifield : AlgebraicAntifield Field) (field : Field) : Real :=
  antifield field

/-- The coadjoint sign makes the canonical BV pairing exactly invariant. -/
theorem fieldAntifieldPairing_brst_invariant
    {Field : Type*} [AddCommGroup Field] [Module Real Field]
    (representation :
      SmoothGhostLieRepresentation period hPeriod Field)
    (ghost : Ghost period hPeriod)
    (antifield : AlgebraicAntifield Field)
    (field : Field) :
    fieldAntifieldPairing
        (coadjointGhostAction period hPeriod representation ghost antifield)
        field +
      fieldAntifieldPairing antifield
        (representation.action ghost field) = 0 := by
  simp [fieldAntifieldPairing]

/-- Unconditional scalar field/antifield nonlinear BRST pair. -/
def smoothScalarFieldAntifieldLieRepresentation :
    FieldAntifieldLieRepresentation period hPeriod
      (CInfinityScalarField period hPeriod) :=
  canonicalFieldAntifieldLieRepresentation period hPeriod
    (smoothScalarGhostLieRepresentation period hPeriod)

theorem scalar_algebraic_antifield_brst_pair_square_zero
    (first second : Ghost period hPeriod)
    (antifield :
      AlgebraicAntifield (CInfinityScalarField period hPeriod)) :
    lieRepresentationBRSTPairObstruction period hPeriod
      (smoothScalarFieldAntifieldLieRepresentation
        period hPeriod).antifield first second antifield = 0 :=
  coadjoint_antifield_nonlinear_brst_pair_square_zero period hPeriod
    (smoothScalarGhostLieRepresentation period hPeriod)
    first second antifield

theorem scalar_field_antifield_pairing_brst_invariant
    (ghost : Ghost period hPeriod)
    (antifield :
      AlgebraicAntifield (CInfinityScalarField period hPeriod))
    (scalar : CInfinityScalarField period hPeriod) :
    fieldAntifieldPairing
        (coadjointGhostAction period hPeriod
          (smoothScalarGhostLieRepresentation period hPeriod)
          ghost antifield) scalar +
      fieldAntifieldPairing antifield
        ((smoothScalarGhostLieRepresentation period hPeriod).action
          ghost scalar) = 0 :=
  fieldAntifieldPairing_brst_invariant period hPeriod
    (smoothScalarGhostLieRepresentation period hPeriod)
    ghost antifield scalar

end
end P0EFTJanusProgramPCoadjointAntifieldBRST4D
end JanusFormal
