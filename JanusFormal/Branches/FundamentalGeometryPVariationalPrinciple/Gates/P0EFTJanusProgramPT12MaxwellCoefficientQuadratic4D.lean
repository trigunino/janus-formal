import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameC2LorenzFeature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeCoefficientRecenterDerivative4D
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2FixedVolumeMaxwellActionBridge4D

/-! # Maxwell action from completed gauge coefficients -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MaxwellCoefficientQuadratic4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2FixedVolumeMaxwellActionBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar :=
  C(EffectiveQuotient period hPeriod, Real)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev GaugeC2Core :=
  RegularGeneralMetricC2GaugeCoefficientCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

private abbrev C0Matrix :=
  Fin 4 → Fin 4 → C0Scalar period hPeriod

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
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open P0EFTJanusRegularFrameC2LorenzFeature4D
open P0EFTJanusGaugeCoefficientRecenterDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D

variable (metric : RegularGeneralLorentzMetric period hPeriod)

/-- The actual Cartan curvature entry is linear on the completed coefficient core. -/
def maxwellCurvatureEntryCLM (component : Fin 2) (first second : Fin 4) :
    GaugeC2Core period hPeriod →L[Real] C0Scalar period hPeriod :=
  (regularFrameC2FirstDerivativeCLM period hPeriod metric first).comp
    (gaugeCoefficientC2CoreComponentCLM period hPeriod second component) -
  (regularFrameC2FirstDerivativeCLM period hPeriod metric second).comp
    (gaugeCoefficientC2CoreComponentCLM period hPeriod first component) -
  ∑ upper : Fin 4,
    (ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
      (regularFrameStructureCoefficientContinuous period hPeriod metric first second upper)).comp
      ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
        (gaugeCoefficientC2CoreComponentCLM period hPeriod upper component))

theorem maxwellCurvatureEntryCLM_apply (component : Fin 2) (first second : Fin 4)
    (coefficients : GaugeC2Core period hPeriod) :
    maxwellCurvatureEntryCLM period hPeriod metric component first second coefficients =
      regularFrameGaugeCurvatureC0MatrixFromC2Coefficients period hPeriod metric coefficients
        component first second := by
  simp only [maxwellCurvatureEntryCLM, sub_apply, sum_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- A genuine quadratic map for the native completed Maxwell pairing. -/
def maxwellCoefficientQuadratic (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    QuadraticMap Real (GaugeC2Core period hPeriod) (C0Scalar period hPeriod) :=
  ∑ component : Fin 2, ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
    QuadraticMap.linMulLin
      (((ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
        (regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric variation a c *
          regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric variation b d)).comp
            (maxwellCurvatureEntryCLM period hPeriod metric component a b)).toLinearMap)
      (maxwellCurvatureEntryCLM period hPeriod metric component c d).toLinearMap

theorem maxwellCoefficientQuadratic_apply
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod) :
    maxwellCoefficientQuadratic period hPeriod metric variation coefficients =
      regularGeneralMetricC0GaugeCoefficientMaxwellPairing period hPeriod metric variation coefficients := by
  simp only [maxwellCoefficientQuadratic, QuadraticMap.sum_apply, QuadraticMap.linMulLin_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, maxwellCurvatureEntryCLM_apply]
  rfl

/-- Fixed-volume integration preserves the quadratic map. -/
def maxwellActionQuadratic (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    QuadraticForm Real (GaugeC2Core period hPeriod) :=
  (regularGeneralMetricC0IntegralCLM period hPeriod
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).toLinearMap.compQuadraticMap
    ((ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
      (smoothToCanonicalPhysicalContinuousScalar period hPeriod metric.volume)).toLinearMap.compQuadraticMap
      ((-(1 / 4 : Real)) • maxwellCoefficientQuadratic period hPeriod metric variation))

theorem maxwellActionQuadratic_apply
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod) :
    maxwellActionQuadratic period hPeriod metric variation coefficients =
      regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) variation coefficients := by
  change regularGeneralMetricC0IntegralCLM period hPeriod _
    (smoothToCanonicalPhysicalContinuousScalar period hPeriod metric.volume *
      ((-(1 / 4 : Real)) • maxwellCoefficientQuadratic period hPeriod metric variation coefficients)) = _
  rw [maxwellCoefficientQuadratic_apply]
  rfl

/-- The root transport is linear in its gauge packet, so the moving action is quadratic too. -/
def mobileMaxwellActionQuadratic (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    QuadraticForm Real (GaugeC2Core period hPeriod) :=
  (maxwellActionQuadratic period hPeriod metric variation).comp
    (gaugeCoefficientC2CoreFrameTransportRightCLM period hPeriod
      (c2IdentityRootBranch period hPeriod
        (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod metric variation))).toLinearMap

theorem mobileMaxwellActionQuadratic_apply
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod) :
    mobileMaxwellActionQuadratic period hPeriod metric variation coefficients =
      regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) variation coefficients := by
  unfold mobileMaxwellActionQuadratic
  rw [QuadraticMap.comp_apply, maxwellActionQuadratic_apply]
  rfl

end
end P0EFTJanusProgramPT12MaxwellCoefficientQuadratic4D
end JanusFormal
