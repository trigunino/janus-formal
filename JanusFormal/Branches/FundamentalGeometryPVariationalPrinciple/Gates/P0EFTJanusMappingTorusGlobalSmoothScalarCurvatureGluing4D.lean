import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicScalarCurvatureNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D

/-!
# Global smooth scalar-curvature gluing

Chart independence of the local scalar curvature and the unconditional
canonical holonomic cover glue the local representatives to a genuine smooth
scalar field on the effective quotient.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D

set_option autoImplicit false

noncomputable section

open Filter
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusCanonicalHolonomicScalarCurvatureNaturality4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 :=
  P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Vector4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- A canonical holonomic representative of one quotient point. -/
structure ScalarCurvatureChartWitness
    (point : EffectiveQuotient period hPeriod) where
  patch : SmoothHolonomicFrameChart4 period hPeriod
  coordinate : Vector4
  coordinateMap_eq : patch.coordinateMap coordinate = point

private theorem scalarCurvatureChartWitness_nonempty
    (point : EffectiveQuotient period hPeriod) :
    Nonempty (ScalarCurvatureChartWitness period hPeriod point) := by
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  exact ⟨⟨patch, coordinate, hCoordinate⟩⟩

/-- An auxiliary classical representative; chart independence removes the
choice from every observable value. -/
def selectedScalarCurvatureChart
    (point : EffectiveQuotient period hPeriod) :
    ScalarCurvatureChartWitness period hPeriod point :=
  Classical.choice
    (scalarCurvatureChartWitness_nonempty period hPeriod point)

/-- Scalar curvature obtained from any selected canonical holonomic
representative. -/
def globalScalarCurvature
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  let witness := selectedScalarCurvatureChart period hPeriod point
  localScalarCurvature period hPeriod metric witness.patch witness.coordinate

/-- Every holonomic representative computes the selected global value. -/
theorem globalScalarCurvature_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    globalScalarCurvature period hPeriod metric
        (patch.coordinateMap coordinate) =
      localScalarCurvature period hPeriod metric patch coordinate := by
  let witness :=
    selectedScalarCurvatureChart period hPeriod
      (patch.coordinateMap coordinate)
  change
    localScalarCurvature period hPeriod metric witness.patch
        witness.coordinate =
      localScalarCurvature period hPeriod metric patch coordinate
  exact localScalarCurvature_transition period hPeriod metric witness.patch
    patch witness.coordinate coordinate witness.coordinateMap_eq

/-- The chart-independent scalar curvature is smooth on the quotient. -/
theorem globalScalarCurvature_contMDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (globalScalarCurvature period hPeriod metric) := by
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  let hLocal := patch.coordinateMap_isLocalDiffeomorph coordinate
  have hRepresentative :
      ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
        (localScalarCurvature period hPeriod metric patch ∘
          hLocal.localInverse)
        (patch.coordinateMap coordinate) :=
    (localScalarCurvature_contDiff period hPeriod metric patch).contMDiff
      |>.contMDiffAt.comp _ hLocal.localInverse_contMDiffAt
  apply hRepresentative.congr_of_eventuallyEq
  filter_upwards [hLocal.localInverse_eventuallyEq_right] with nearby hNearby
  have hRight :
      patch.coordinateMap (hLocal.localInverse nearby) = nearby := by
    simpa only [Function.comp_apply, id_eq] using hNearby
  change
    globalScalarCurvature period hPeriod metric nearby =
      localScalarCurvature period hPeriod metric patch
        (hLocal.localInverse nearby)
  calc
    globalScalarCurvature period hPeriod metric nearby =
        globalScalarCurvature period hPeriod metric
          (patch.coordinateMap (hLocal.localInverse nearby)) :=
      congrArg (globalScalarCurvature period hPeriod metric) hRight.symm
    _ = _ := globalScalarCurvature_eq_local period hPeriod metric patch
      (hLocal.localInverse nearby)

/-- Genuine smooth scalar-curvature field of a smooth Lorentz metric. -/
def globalSmoothScalarCurvature
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun := globalScalarCurvature period hPeriod metric
  contMDiff_toFun := globalScalarCurvature_contMDiff period hPeriod metric

@[simp]
theorem globalSmoothScalarCurvature_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalSmoothScalarCurvature period hPeriod metric point =
      globalScalarCurvature period hPeriod metric point :=
  rfl

@[simp]
theorem globalSmoothScalarCurvature_apply_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    globalSmoothScalarCurvature period hPeriod metric
        (patch.coordinateMap coordinate) =
      localScalarCurvature period hPeriod metric patch coordinate :=
  globalScalarCurvature_eq_local period hPeriod metric patch coordinate

/-- The computed global scalar fills the scalar-curvature slot of the legacy
regular Einstein--Hilbert metric domain.  All pre-existing requirements of
`RegularGeneralLorentzMetric`, including its frame field, remain explicit. -/
def RegularGeneralLorentzMetric.toRegularEinsteinHilbertMetric
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    RegularEinsteinHilbertMetric period hPeriod where
  metric := metric
  scalarCurvature :=
    globalSmoothScalarCurvature period hPeriod metric.metric
  scalarCurvature_eq := by
    intro patch coordinate
    exact globalSmoothScalarCurvature_apply_local period hPeriod metric.metric
      patch coordinate

end

end P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
end JanusFormal
