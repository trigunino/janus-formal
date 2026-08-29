import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

/-!
# Frame-free intrinsic Einstein--Hilbert action

The global scalar curvature is integrated directly against a supplied
finite nonzero action measure.  This is the Einstein--Hilbert action when
that measure is the metric Lorentz volume.  No global tangent frame or
frame-dependent determinant representative occurs in this interface, and
the intrinsic quotient metric has a canonical volume specialization below.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusFrameFreeIntrinsicEinsteinHilbertAction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusFrameFreeIntrinsicScalarAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Frame-free Einstein--Hilbert scalar integrand.  The metric contributes
only its intrinsic global scalar curvature; the action measure is separate. -/
def frameFreeEinsteinHilbertDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    SmoothScalarField period hPeriod where
  toFun := fun point =>
    (1 / (2 * couplings.gravitationalCoupling)) *
      (globalSmoothScalarCurvature period hPeriod metric point -
        2 * couplings.cosmologicalConstant)
  contMDiff_toFun :=
    contMDiff_const.mul
      ((globalSmoothScalarCurvature period hPeriod metric).contMDiff_toFun.sub
        contMDiff_const)

/-- Every holonomic chart computes the frame-free density by the existing
local Einstein--Hilbert formula. -/
theorem frameFreeEinsteinHilbertDensity_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate :
      P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    frameFreeEinsteinHilbertDensity period hPeriod metric couplings
        (patch.coordinateMap coordinate) =
      localEinsteinHilbertLagrangian period hPeriod metric couplings patch
        coordinate := by
  change
    (1 / (2 * couplings.gravitationalCoupling)) *
        (globalSmoothScalarCurvature period hPeriod metric
            (patch.coordinateMap coordinate) -
          2 * couplings.cosmologicalConstant) =
      _
  rw [globalSmoothScalarCurvature_apply_local]
  rfl

theorem frameFreeEinsteinHilbertDensity_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (volume : FiniteNonzeroActionMeasure period hPeriod) :
    Integrable
      (frameFreeEinsteinHilbertDensity period hPeriod metric couplings)
      volume.measure := by
  letI := volume.finite
  exact
    (frameFreeEinsteinHilbertDensity period hPeriod metric couplings)
      |>.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Integrated frame-free scalar-curvature action.  It is Einstein--Hilbert
when the supplied action measure is the metric Lorentz volume. -/
def frameFreeEinsteinHilbertAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (volume : FiniteNonzeroActionMeasure period hPeriod) : Real :=
  ∫ point,
    frameFreeEinsteinHilbertDensity period hPeriod metric couplings point
      ∂volume.measure

/-- The explicit intrinsic quotient metric has a completely canonical
frame-free Einstein--Hilbert action. -/
def intrinsicCanonicalFrameFreeEinsteinHilbertAction
    (couplings : EinsteinHilbertCouplings) : Real :=
  frameFreeEinsteinHilbertAction period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) couplings
    (intrinsicCanonicalLorentzActionMeasure period hPeriod)

/-- Einstein--Hilbert action measured by the positive relative Lorentz volume
canonically constructed from the same smooth metric. -/
def generalLorentzFrameFreeEinsteinHilbertAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) : Real :=
  frameFreeEinsteinHilbertAction period hPeriod metric couplings
    (generalLorentzActionMeasure period hPeriod metric)

/-- Fixed-reference presentation of the metric-volume Einstein--Hilbert
action.  This is a spacetime identity, not a metric-space variation theorem. -/
theorem generalLorentzFrameFreeEinsteinHilbertAction_eq_reference
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    generalLorentzFrameFreeEinsteinHilbertAction period hPeriod metric
        couplings =
      ∫ point,
        globalMetricVolumeRatio period hPeriod metric point *
          frameFreeEinsteinHilbertDensity period hPeriod metric couplings point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  exact integral_generalLorentzVolumeMeasure_eq_reference period hPeriod metric
    (frameFreeEinsteinHilbertDensity period hPeriod metric couplings)

end

end P0EFTJanusMappingTorusFrameFreeIntrinsicEinsteinHilbertAction4D
end JanusFormal
