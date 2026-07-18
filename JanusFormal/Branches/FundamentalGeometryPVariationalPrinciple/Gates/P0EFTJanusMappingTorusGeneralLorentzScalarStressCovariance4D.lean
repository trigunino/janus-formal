import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D

/-!
# Diffeomorphism covariance of the general Lorentz scalar stress tensor

The contravariant scalar stress is defined intrinsically as a bilinear form on
cotangent vectors.  Coherent pullback of the metric musical map, the scalar
differential, and the test covectors leaves it unchanged.  The final theorem
specializes this fiberwise naturality to every smooth D8 diffeomorphism.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzScalarStressCovariance4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

private abbrev MusicalFiber (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point ≃L[Real] CotangentFiber period hPeriod point

/-- Scalar Lagrangian without its frame-volume factor. -/
def fiberScalarLagrangian
    {point : EffectiveQuotient period hPeriod}
    (musical : MusicalFiber period hPeriod point)
    (massSquared fieldValue : Real)
    (differential : CotangentFiber period hPeriod point) : Real :=
  1 / 2 * fiberInverseMetricContraction period hPeriod musical
      differential differential -
    1 / 2 * massSquared * fieldValue ^ 2

theorem fiberScalarLagrangian_pullback
    {source target : EffectiveQuotient period hPeriod}
    (equivalence : TangentFiber period hPeriod source ≃L[Real]
      TangentFiber period hPeriod target)
    (musical : MusicalFiber period hPeriod target)
    (massSquared fieldValue : Real)
    (differential : CotangentFiber period hPeriod target) :
    fiberScalarLagrangian period hPeriod
        (pullbackMusical period hPeriod equivalence musical)
        massSquared fieldValue
        (pullbackCovector period hPeriod equivalence differential) =
      fiberScalarLagrangian period hPeriod musical massSquared fieldValue
        differential := by
  simp only [fiberScalarLagrangian,
    fiberInverseMetricContraction_pullback]

/-- Intrinsic contravariant scalar stress, evaluated on two covectors. -/
def fiberContravariantScalarStress
    {point : EffectiveQuotient period hPeriod}
    (musical : MusicalFiber period hPeriod point)
    (massSquared fieldValue : Real)
    (differential first second : CotangentFiber period hPeriod point) : Real :=
  fiberInverseMetricContraction period hPeriod musical first differential *
      fiberInverseMetricContraction period hPeriod musical second differential -
    fiberInverseMetricContraction period hPeriod musical first second *
      fiberScalarLagrangian period hPeriod musical massSquared fieldValue differential

/-- Exact tensor naturality under an arbitrary tangent-space equivalence. -/
theorem fiberContravariantScalarStress_pullback
    {source target : EffectiveQuotient period hPeriod}
    (equivalence : TangentFiber period hPeriod source ≃L[Real]
      TangentFiber period hPeriod target)
    (musical : MusicalFiber period hPeriod target)
    (massSquared fieldValue : Real)
    (differential first second : CotangentFiber period hPeriod target) :
    fiberContravariantScalarStress period hPeriod
        (pullbackMusical period hPeriod equivalence musical)
        massSquared fieldValue
        (pullbackCovector period hPeriod equivalence differential)
        (pullbackCovector period hPeriod equivalence first)
        (pullbackCovector period hPeriod equivalence second) =
      fiberContravariantScalarStress period hPeriod musical
        massSquared fieldValue differential first second := by
  simp only [fiberContravariantScalarStress,
    fiberInverseMetricContraction_pullback,
    fiberScalarLagrangian_pullback]

/-- Pointwise covariance of the holonomic scalar stress under every smooth D8
diffeomorphism. -/
theorem holonomicScalarStress_diffeomorphism
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : CotangentFiber period hPeriod (diffeomorphism point)) :
    fiberContravariantScalarStress period hPeriod
        (pullbackMusical period hPeriod
          (diffeomorphismDerivative period hPeriod diffeomorphism point)
          (metric.musical (diffeomorphism point)))
        massSquared (field (diffeomorphism point))
        (scalarDifferential period hPeriod
          (pullbackSmoothField period hPeriod Real diffeomorphism field) point)
        (pullbackCovector period hPeriod
          (diffeomorphismDerivative period hPeriod diffeomorphism point) first)
        (pullbackCovector period hPeriod
          (diffeomorphismDerivative period hPeriod diffeomorphism point) second) =
      fiberContravariantScalarStress period hPeriod
        (metric.musical (diffeomorphism point)) massSquared
        (field (diffeomorphism point))
        (scalarDifferential period hPeriod field (diffeomorphism point))
        first second := by
  rw [scalarDifferential_pullback]
  exact fiberContravariantScalarStress_pullback period hPeriod
    (diffeomorphismDerivative period hPeriod diffeomorphism point)
    (metric.musical (diffeomorphism point)) massSquared
    (field (diffeomorphism point))
    (scalarDifferential period hPeriod field (diffeomorphism point)) first second

end

end P0EFTJanusMappingTorusGeneralLorentzScalarStressCovariance4D
end JanusFormal
