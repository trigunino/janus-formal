import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGaugePotentialCartanFiber4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D

/-!
# Maxwell Cartan residual as a genuine D8 fiber covector

The generic tensoriality core is specialized componentwise to an intrinsic
smooth abelian gauge potential and a smooth diffeomorphism ghost.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGaugePotentialCartanFiberBridge4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGaugePotentialCartanFiber4D
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

local instance effectiveTangentFiniteDimensional
    (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real
      (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

/-- Evaluation of a smooth Maxwell component on a differentiable tangent
section is differentiable. -/
theorem smoothGaugePotentialEvaluation_mdifferentiableAt
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod)
    (tangentSection : ∀ current : EffectiveQuotient period hPeriod,
      TangentSpace coverModelWithCorners current)
    (hSection :
      MDifferentiableAt coverModelWithCorners
        coverModelWithCorners.tangent
        (fun current =>
          (⟨current, tangentSection current⟩ :
            TangentBundle coverModelWithCorners
              (EffectiveQuotient period hPeriod)))
        point) :
    MDifferentiableAt coverModelWithCorners
      (modelWithCornersSelf Real Real)
      (fun current =>
        potential.toFun component current (tangentSection current))
      point := by
  exact
    ((potential.contMDiff_eval component).mdifferentiableAt
      (by simp)).comp point hSection

/-- Componentwise cotangent-fiber value of the Maxwell Cartan residual. -/
def smoothGaugePotentialCartanFiberCovector
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    TangentSpace coverModelWithCorners point →L[Real] Real :=
  gaugePotentialCartanFiberCovector coverModelWithCorners ghost
    (potential.toFun component) point
    (smoothGaugePotentialEvaluation_mdifferentiableAt
      period hPeriod potential component point)

/-- Fiber evaluation recovers the intrinsic componentwise Cartan residual. -/
@[simp]
theorem smoothGaugePotentialCartanFiberCovector_apply
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod)
    (second : CInfinityDiffeomorphismGhost period hPeriod) :
    smoothGaugePotentialCartanFiberCovector
        period hPeriod ghost potential component point (second point) =
      gaugePotentialCartanResidualAt coverModelWithCorners ghost
        (potential.toFun component) point second := by
  exact gaugePotentialCartanFiberCovector_apply
    coverModelWithCorners ghost (potential.toFun component) point
    (smoothGaugePotentialEvaluation_mdifferentiableAt
      period hPeriod potential component point)
    second (second.contMDiff.mdifferentiableAt (by simp))

end

end P0EFTJanusMappingTorusGaugePotentialCartanFiberBridge4D
end JanusFormal
