import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

/-!
# Coadjoint BRST action on fixed-throat scalar antifields

The fixed-throat scalar Lie derivative already satisfies the full bracket
identity.  This gate reuses it to construct the corresponding algebraic
antifield action, prove its nonlinear closure, and prove invariance of the
canonical boundary field-antifield pairing.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusThroatScalarCoadjointBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatScalar :=
  CInfinityThroatScalarField period hPeriod

private abbrev ThroatGhost :=
  CInfinityThroatGhost period hPeriod

/-- Algebraic antifields of smooth scalar fields on the fixed throat. -/
abbrev ThroatScalarAlgebraicAntifield :=
  ThroatScalar period hPeriod →ₗ[Real] Real

/-- Coadjoint boundary action `L_c^* α = - α ∘ L_c`. -/
def throatScalarCoadjointGhostAction
    (ghost : ThroatGhost period hPeriod)
    (antifield : ThroatScalarAlgebraicAntifield period hPeriod) :
    ThroatScalarAlgebraicAntifield period hPeriod where
  toFun := fun scalar =>
    -antifield (throatScalarLieDerivative period hPeriod ghost scalar)
  map_add' := by
    intro first second
    rw [throatScalarLieDerivative_addScalar]
    simp
    abel
  map_smul' := by
    intro coefficient scalar
    rw [throatScalarLieDerivative_smulScalar]
    simp

@[simp]
theorem throatScalarCoadjointGhostAction_apply
    (ghost : ThroatGhost period hPeriod)
    (antifield : ThroatScalarAlgebraicAntifield period hPeriod)
    (scalar : ThroatScalar period hPeriod) :
    throatScalarCoadjointGhostAction period hPeriod ghost antifield scalar =
      -antifield
        (throatScalarLieDerivative period hPeriod ghost scalar) :=
  rfl

/-- The coadjoint throat action represents the intrinsic throat bracket. -/
theorem throatScalarCoadjointGhostAction_bracket
    (first second : ThroatGhost period hPeriod)
    (antifield : ThroatScalarAlgebraicAntifield period hPeriod) :
    throatScalarCoadjointGhostAction period hPeriod
        (throatGhostLieBracket period hPeriod first second) antifield =
      throatScalarCoadjointGhostAction period hPeriod first
          (throatScalarCoadjointGhostAction period hPeriod second antifield) -
        throatScalarCoadjointGhostAction period hPeriod second
          (throatScalarCoadjointGhostAction period hPeriod first antifield) := by
  apply LinearMap.ext
  intro scalar
  simp only [throatScalarCoadjointGhostAction_apply, LinearMap.sub_apply,
    neg_neg]
  rw [throatScalarLieDerivative_bracket]
  simp

/-- Pairwise nonlinear BRST obstruction on throat scalar antifields. -/
def throatScalarAntifieldBRSTPairObstruction
    (first second : ThroatGhost period hPeriod)
    (antifield : ThroatScalarAlgebraicAntifield period hPeriod) :
    ThroatScalarAlgebraicAntifield period hPeriod :=
  throatScalarCoadjointGhostAction period hPeriod first
      (throatScalarCoadjointGhostAction period hPeriod second antifield) -
    throatScalarCoadjointGhostAction period hPeriod second
      (throatScalarCoadjointGhostAction period hPeriod first antifield) -
    throatScalarCoadjointGhostAction period hPeriod
      (throatGhostLieBracket period hPeriod first second) antifield

@[simp]
theorem throatScalarAntifieldBRSTPairObstruction_zero
    (first second : ThroatGhost period hPeriod)
    (antifield : ThroatScalarAlgebraicAntifield period hPeriod) :
    throatScalarAntifieldBRSTPairObstruction period hPeriod
      first second antifield = 0 := by
  rw [throatScalarAntifieldBRSTPairObstruction,
    throatScalarCoadjointGhostAction_bracket]
  abel

/-- The canonical boundary field-antifield evaluation is BRST invariant. -/
theorem throatScalarFieldAntifieldPairing_brst_invariant
    (ghost : ThroatGhost period hPeriod)
    (antifield : ThroatScalarAlgebraicAntifield period hPeriod)
    (scalar : ThroatScalar period hPeriod) :
    throatScalarCoadjointGhostAction period hPeriod ghost antifield scalar +
      antifield (throatScalarLieDerivative period hPeriod ghost scalar) = 0 := by
  simp

/-- Closed scalar-antifield part of the fixed-throat nonlinear BRST sector. -/
structure ThroatScalarCoadjointBRSTCertificate4D : Prop where
  bracket :
    ∀ first second antifield,
      throatScalarCoadjointGhostAction period hPeriod
          (throatGhostLieBracket period hPeriod first second) antifield =
        throatScalarCoadjointGhostAction period hPeriod first
            (throatScalarCoadjointGhostAction period hPeriod second antifield) -
          throatScalarCoadjointGhostAction period hPeriod second
            (throatScalarCoadjointGhostAction period hPeriod first antifield)
  squareZero :
    ∀ first second antifield,
      throatScalarAntifieldBRSTPairObstruction period hPeriod
        first second antifield = 0
  pairingInvariant :
    ∀ ghost antifield scalar,
      throatScalarCoadjointGhostAction period hPeriod ghost antifield scalar +
        antifield (throatScalarLieDerivative period hPeriod ghost scalar) = 0

def throatScalarCoadjointBRSTCertificate4D :
    ThroatScalarCoadjointBRSTCertificate4D period hPeriod where
  bracket := throatScalarCoadjointGhostAction_bracket period hPeriod
  squareZero :=
    throatScalarAntifieldBRSTPairObstruction_zero period hPeriod
  pairingInvariant :=
    throatScalarFieldAntifieldPairing_brst_invariant period hPeriod

end
end P0EFTJanusMappingTorusThroatScalarCoadjointBRST4D
end JanusFormal
