import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGaugePotentialCartanRepresentation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCoadjointAntifieldBRST4D

/-!
# Maxwell Cartan coadjoint antifield BRST

The concrete Maxwell Cartan Lie representation is connected directly to the
existing algebraic coadjoint construction.  This closes the field and
antifield pair obstructions and the canonical evaluation-pairing identity.
No geometric or integrated antifield dual is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPMaxwellCartanCoadjointAntifieldBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
open P0EFTJanusMappingTorusGaugePotentialCartanRepresentation4D
open P0EFTJanusProgramPCoadjointAntifieldBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The concrete Maxwell field representation has zero nonlinear BRST pair
obstruction. -/
theorem maxwellCartanField_brstPairObstruction_zero
    (first second : CInfinityDiffeomorphismGhost period hPeriod)
    (field : SmoothAbelianGaugePotential period hPeriod) :
    lieRepresentationBRSTPairObstruction period hPeriod
      (smoothGaugePotentialCartanLieRepresentation period hPeriod)
      first second field = 0 :=
  lieRepresentationBRSTPairObstruction_zero period hPeriod
    (smoothGaugePotentialCartanLieRepresentation period hPeriod)
    first second field

/-- Canonical algebraic coadjoint representation on Maxwell antifields. -/
def maxwellCartanCoadjointGhostLieRepresentation :
    SmoothGhostLieRepresentation period hPeriod
      (AlgebraicAntifield
        (SmoothAbelianGaugePotential period hPeriod)) :=
  coadjointGhostLieRepresentation period hPeriod
    (smoothGaugePotentialCartanLieRepresentation period hPeriod)

/-- The induced Maxwell antifield representation has zero nonlinear BRST
pair obstruction. -/
theorem maxwellCartanAntifield_brstPairObstruction_zero
    (first second : CInfinityDiffeomorphismGhost period hPeriod)
    (antifield :
      AlgebraicAntifield
        (SmoothAbelianGaugePotential period hPeriod)) :
    lieRepresentationBRSTPairObstruction period hPeriod
      (maxwellCartanCoadjointGhostLieRepresentation period hPeriod)
      first second antifield = 0 :=
  coadjoint_antifield_nonlinear_brst_pair_square_zero
    period hPeriod
    (smoothGaugePotentialCartanLieRepresentation period hPeriod)
    first second antifield

/-- The canonical algebraic Maxwell field/antifield evaluation pairing is
BRST invariant. -/
theorem maxwellCartanFieldAntifieldPairing_brst_invariant
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (antifield :
      AlgebraicAntifield
        (SmoothAbelianGaugePotential period hPeriod))
    (field : SmoothAbelianGaugePotential period hPeriod) :
    fieldAntifieldPairing
        (coadjointGhostAction period hPeriod
          (smoothGaugePotentialCartanLieRepresentation period hPeriod)
          ghost antifield)
        field +
      fieldAntifieldPairing antifield
        ((smoothGaugePotentialCartanLieRepresentation
          period hPeriod).action ghost field) = 0 :=
  fieldAntifieldPairing_brst_invariant period hPeriod
    (smoothGaugePotentialCartanLieRepresentation period hPeriod)
    ghost antifield field

end

end P0EFTJanusProgramPMaxwellCartanCoadjointAntifieldBRST4D
end JanusFormal
