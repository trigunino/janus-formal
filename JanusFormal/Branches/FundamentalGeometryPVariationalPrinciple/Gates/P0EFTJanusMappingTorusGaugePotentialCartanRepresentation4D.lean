import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGaugePotentialCartanGlobalAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D

/-!
# Maxwell Cartan Lie representation

The unconditional smooth bilinear Cartan action is connected to the existing
generic Cartan-reduction interface.  Its Lie-bracket law is therefore inherited
from the already proved contraction-separation argument.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGaugePotentialCartanRepresentation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusGaugePotentialCartanGlobalAction4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D

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

/-- The genuine smooth Maxwell Cartan operation satisfies the existing
contraction formula, hence supplies the common representation contract. -/
def gaugePotentialCartanActionData :
    GaugePotentialCartanActionData period hPeriod where
  action := smoothGaugePotentialCartanActionBilinear period hPeriod
  cartan := by
    intro first potential second component
    apply ContMDiffMap.ext
    intro point
    change
      (smoothGaugePotentialCartanAction
        period hPeriod first potential).toFun component point (second point) =
        _
    rw [smoothGaugePotentialCartanAction_apply]
    rfl

/-- Unconditional Lie representation of smooth D8 diffeomorphism ghosts on
intrinsic Maxwell potentials. -/
def smoothGaugePotentialCartanLieRepresentation :
    SmoothGhostLieRepresentation period hPeriod
      (SmoothAbelianGaugePotential period hPeriod) :=
  (gaugePotentialCartanActionData period hPeriod).toSmoothGhostLieRepresentation
    period hPeriod

theorem smoothGaugePotentialCartanAction_bracket
    (first second : CInfinityDiffeomorphismGhost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    smoothGaugePotentialCartanAction period hPeriod
        (smoothGhostLieBracket period hPeriod first second) potential =
      smoothGaugePotentialCartanAction period hPeriod first
          (smoothGaugePotentialCartanAction period hPeriod second potential) -
        smoothGaugePotentialCartanAction period hPeriod second
          (smoothGaugePotentialCartanAction period hPeriod first potential) :=
  (gaugePotentialCartanActionData period hPeriod).bracket_action
    period hPeriod first second potential

end

end P0EFTJanusMappingTorusGaugePotentialCartanRepresentation4D
end JanusFormal
