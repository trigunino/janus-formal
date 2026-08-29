import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D

/-!
# Measured scalar densities in the nonlinear BRST complex

The existing global action convention stores a scalar coefficient and pulls
back the integration measure.  This gate records its finite functoriality,
uses the already proved scalar ghost representation for the infinitesimal
coefficient, and exposes the existing unconditional integrated covariance.
It does not introduce a second, weight-one density carrier.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMeasuredDensityBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Smooth coefficient of a density whose Jacobian is carried by the
simultaneously pulled-back measure. -/
abbrev SmoothMeasuredDensityCoefficient :=
  CInfinityScalarField period hPeriod

/-- Finite pullback of the scalar coefficient in the measured-density
convention. -/
def pullbackMeasuredDensityCoefficient
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (density : SmoothMeasuredDensityCoefficient period hPeriod) :
    SmoothMeasuredDensityCoefficient period hPeriod :=
  ⟨density ∘ diffeomorphism,
    density.contMDiff.comp (diffeomorphism.contMDiff.of_le (by simp))⟩

@[simp]
theorem pullbackMeasuredDensityCoefficient_refl
    (density : SmoothMeasuredDensityCoefficient period hPeriod) :
    pullbackMeasuredDensityCoefficient period hPeriod
      (Diffeomorph.refl coverModelWithCorners
        (EffectiveQuotient period hPeriod) ω) density = density := by
  ext point
  rfl

/-- Finite density-coefficient pullback is a contravariant action. -/
theorem pullbackMeasuredDensityCoefficient_trans
    (first second : SpacetimeDiffeomorphism period hPeriod)
    (density : SmoothMeasuredDensityCoefficient period hPeriod) :
    pullbackMeasuredDensityCoefficient period hPeriod first
        (pullbackMeasuredDensityCoefficient period hPeriod second density) =
      pullbackMeasuredDensityCoefficient period hPeriod
        (first.trans second) density := by
  ext point
  rfl

/-- The nonlinear two-ghost square vanishes on measured-density
coefficients by the existing scalar Lie-representation theorem. -/
theorem measuredDensityCoefficient_nonlinear_brst_pair_square_zero
    (first second :
      CInfinityDiffeomorphismGhost period hPeriod)
    (density : SmoothMeasuredDensityCoefficient period hPeriod) :
    lieRepresentationBRSTPairObstruction period hPeriod
      (smoothScalarGhostLieRepresentation period hPeriod)
      first second density = 0 :=
  scalar_geometric_nonlinear_brst_pair_square_zero
    period hPeriod first second density

/-- Existing finite covariance of the integrated holonomic scalar density:
the coefficient, metric, frame, and measure are pulled back together. -/
theorem measuredHolonomicScalarDensity_covariant
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    measuredGeneralLorentzHolonomicScalarAction period hPeriod
        (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
          diffeomorphism metric)
        massSquared
        (pullbackSmoothField period hPeriod Real diffeomorphism field)
        (diffeomorphismOrderedTangentVectorPullback period hPeriod
          diffeomorphism frame)
        (diffeomorphismMeasurePullback period hPeriod
          diffeomorphism measure) =
      measuredGeneralLorentzHolonomicScalarAction period hPeriod metric
        massSquared field frame measure :=
  measuredGeneralLorentzHolonomicScalarAction_diffeomorphism_unconditional
    period hPeriod diffeomorphism metric massSquared field frame measure

/-- Closed measured-density part of the nonlinear BRST frontier. -/
structure MeasuredDensityBRSTCertificate4D : Prop where
  finiteRepresentation :
    ∀ first second density,
      pullbackMeasuredDensityCoefficient period hPeriod first
          (pullbackMeasuredDensityCoefficient period hPeriod second density) =
        pullbackMeasuredDensityCoefficient period hPeriod
          (first.trans second) density
  infinitesimalSquareZero :
    ∀ first second density,
      lieRepresentationBRSTPairObstruction period hPeriod
        (smoothScalarGhostLieRepresentation period hPeriod)
        first second density = 0

def measuredDensityBRSTCertificate4D :
    MeasuredDensityBRSTCertificate4D period hPeriod where
  finiteRepresentation :=
    pullbackMeasuredDensityCoefficient_trans period hPeriod
  infinitesimalSquareZero :=
    measuredDensityCoefficient_nonlinear_brst_pair_square_zero
      period hPeriod

end
end P0EFTJanusMappingTorusMeasuredDensityBRST4D
end JanusFormal
