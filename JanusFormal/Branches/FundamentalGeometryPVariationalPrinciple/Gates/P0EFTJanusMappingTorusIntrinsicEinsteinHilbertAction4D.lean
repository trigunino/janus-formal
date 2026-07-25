import Mathlib.MeasureTheory.Integral.Bochner.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D

/-!
# Intrinsic Einstein--Hilbert action on the D8 quotient

The scalar curvature is the contraction of the Riemann tensor constructed
from the Levi--Civita connection.  A regular global metric records only the
smooth atlas descent of that computed scalar.  The resulting action is the
integral of `sqrt |det g| (R - 2 Λ) / (2 κ)`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Physical constants entering the gravitational bulk action. -/
structure EinsteinHilbertCouplings where
  gravitationalCoupling : Real
  gravitationalCoupling_ne_zero : gravitationalCoupling ≠ 0
  cosmologicalConstant : Real

/-- Local Einstein--Hilbert scalar, before multiplication by volume. -/
def localEinsteinHilbertLagrangian
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  (1 / (2 * couplings.gravitationalCoupling)) *
    (localScalarCurvature period hPeriod metric patch coordinate -
      2 * couplings.cosmologicalConstant)

theorem localEinsteinHilbertLagrangian_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localEinsteinHilbertLagrangian period hPeriod metric couplings patch) := by
  unfold localEinsteinHilbertLagrangian
  exact contDiff_const.mul
    ((localScalarCurvature_contDiff period hPeriod metric patch).sub
      contDiff_const)

/-- Functional domain for a global Einstein--Hilbert metric.  The global
scalar is constrained to equal the curvature computed from the metric in
every supplied holonomic chart. -/
structure RegularEinsteinHilbertMetric where
  metric : RegularGeneralLorentzMetric period hPeriod
  scalarCurvature : SmoothScalarField period hPeriod
  scalarCurvature_eq : ∀
      (patch : SmoothHolonomicFrameChart4 period hPeriod)
      (coordinate : Vector4),
    scalarCurvature (patch.coordinateMap coordinate) =
      localScalarCurvature period hPeriod metric.metric patch coordinate

/-- Smooth global Einstein--Hilbert density. -/
def regularEinsteinHilbertDensityField
    (couplings : EinsteinHilbertCouplings)
    (data : RegularEinsteinHilbertMetric period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    data.metric.volume point *
      ((1 / (2 * couplings.gravitationalCoupling)) *
        (data.scalarCurvature point - 2 * couplings.cosmologicalConstant))
  contMDiff_toFun := data.metric.volume.contMDiff_toFun.mul
    (contMDiff_const.mul
      (data.scalarCurvature.contMDiff_toFun.sub contMDiff_const))

theorem regularEinsteinHilbertDensityField_eq_local
    (couplings : EinsteinHilbertCouplings)
    (data : RegularEinsteinHilbertMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularEinsteinHilbertDensityField period hPeriod couplings data
        (patch.coordinateMap coordinate) =
      data.metric.volume (patch.coordinateMap coordinate) *
        localEinsteinHilbertLagrangian period hPeriod data.metric.metric
          couplings patch coordinate := by
  change
    data.metric.volume (patch.coordinateMap coordinate) *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          (data.scalarCurvature (patch.coordinateMap coordinate) -
            2 * couplings.cosmologicalConstant)) =
      _
  rw [data.scalarCurvature_eq patch coordinate]
  rfl

/-- Genuine integrated Einstein--Hilbert bulk action. -/
def intrinsicEinsteinHilbertAction
    (couplings : EinsteinHilbertCouplings)
    (data : RegularEinsteinHilbertMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point,
    regularEinsteinHilbertDensityField period hPeriod couplings data point
    ∂measure

theorem regularEinsteinHilbertDensityField_integrable
    (couplings : EinsteinHilbertCouplings)
    (data : RegularEinsteinHilbertMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    Integrable
      (regularEinsteinHilbertDensityField period hPeriod couplings data)
      measure :=
  (regularEinsteinHilbertDensityField period hPeriod couplings data)
    |>.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The action separates exactly into curvature and cosmological terms. -/
theorem intrinsicEinsteinHilbertAction_decomposition
    (couplings : EinsteinHilbertCouplings)
    (data : RegularEinsteinHilbertMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    intrinsicEinsteinHilbertAction period hPeriod couplings data measure =
      (1 / (2 * couplings.gravitationalCoupling)) *
          ∫ point,
            data.metric.volume point * data.scalarCurvature point ∂measure -
        (couplings.cosmologicalConstant /
            couplings.gravitationalCoupling) *
          ∫ point, data.metric.volume point ∂measure := by
  have hCurvature : Integrable
      (fun point => data.metric.volume point * data.scalarCurvature point)
      measure :=
    (data.metric.volume.contMDiff_toFun.mul
      data.scalarCurvature.contMDiff_toFun).continuous
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hVolume : Integrable data.metric.volume measure :=
    data.metric.volume.contMDiff_toFun.continuous
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  unfold intrinsicEinsteinHilbertAction
    regularEinsteinHilbertDensityField
  rw [show (fun point =>
      data.metric.volume point *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          (data.scalarCurvature point -
            2 * couplings.cosmologicalConstant))) =
      fun point =>
        (1 / (2 * couplings.gravitationalCoupling)) *
            (data.metric.volume point * data.scalarCurvature point) -
          (couplings.cosmologicalConstant /
              couplings.gravitationalCoupling) *
            data.metric.volume point by
    funext point
    field_simp [couplings.gravitationalCoupling_ne_zero]]
  rw [integral_sub
      (hCurvature.const_mul
        (1 / (2 * couplings.gravitationalCoupling)))
      (hVolume.const_mul
        (couplings.cosmologicalConstant /
          couplings.gravitationalCoupling)),
    integral_const_mul, integral_const_mul]

end

end P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
end JanusFormal
