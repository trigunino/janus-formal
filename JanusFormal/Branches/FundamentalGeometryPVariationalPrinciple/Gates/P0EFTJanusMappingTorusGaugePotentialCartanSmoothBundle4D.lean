import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGaugePotentialCartanFiberBridge4D

/-!
# Smooth Maxwell Cartan bundle interface

`TensorialAt.mkHom` constructs the Cartan covector in each fiber, but does
not by itself provide smooth dependence on the base point.  This file
isolates exactly that remaining regularity and bundles the componentwise
fiber covectors as an intrinsic smooth abelian gauge potential.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGaugePotentialCartanSmoothBundle4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGaugePotentialCartanFiber4D
open P0EFTJanusMappingTorusGaugePotentialCartanFiberBridge4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D

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

/-- Exact regularity still needed after the fiberwise tensoriality theorem.
It is deliberately stated on tangent-bundle evaluation, matching the
smoothness field of `SmoothAbelianGaugePotential`. -/
structure GaugePotentialCartanFiberSmoothness
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) : Prop where
  contMDiff_eval : ∀ component : Fin 2,
    ContMDiff coverModelWithCorners.tangent
      (modelWithCornersSelf Real Real) ∞
      (fun vector : TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod) =>
        smoothGaugePotentialCartanFiberCovector
          period hPeriod ghost potential component vector.1 vector.2)

/-- Componentwise Cartan fiber covectors bundled as a genuine smooth
abelian gauge potential, under exactly their missing base-point regularity. -/
def smoothGaugePotentialCartanBundle
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (regularity :
      GaugePotentialCartanFiberSmoothness period hPeriod ghost potential) :
    SmoothAbelianGaugePotential period hPeriod where
  toFun := fun component point =>
    smoothGaugePotentialCartanFiberCovector
      period hPeriod ghost potential component point
  contMDiff_eval := regularity.contMDiff_eval

@[simp]
theorem smoothGaugePotentialCartanBundle_toFun
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (regularity :
      GaugePotentialCartanFiberSmoothness period hPeriod ghost potential)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    (smoothGaugePotentialCartanBundle
      period hPeriod ghost potential regularity).toFun component point =
      smoothGaugePotentialCartanFiberCovector
        period hPeriod ghost potential component point :=
  rfl

/-- The smooth bundle still evaluates to the intrinsic Cartan residual on
every smooth diffeomorphism ghost. -/
@[simp]
theorem smoothGaugePotentialCartanBundle_apply
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (regularity :
      GaugePotentialCartanFiberSmoothness period hPeriod ghost potential)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod)
    (second : CInfinityDiffeomorphismGhost period hPeriod) :
    (smoothGaugePotentialCartanBundle
        period hPeriod ghost potential regularity).toFun
        component point (second point) =
      gaugePotentialCartanResidualAt coverModelWithCorners ghost
        (potential.toFun component) point second := by
  exact smoothGaugePotentialCartanFiberCovector_apply
    period hPeriod ghost potential component point second

end

end P0EFTJanusMappingTorusGaugePotentialCartanSmoothBundle4D
end JanusFormal
