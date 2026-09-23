import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MixedPartialHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellMixedMetricL24D
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FullMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellCoefficientQuadratic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12QuadraticParameterDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellStressCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InducedMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricResidual4D

/-! The native joint Maxwell Hessian, its mixed entries and their actual L2 representatives. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
open P0EFTJanusFixedVolumeMaxwellStressResidual4D
open P0EFTJanusMetricInducedSmoothGaugeVelocity4D
open P0EFTJanusGaugeCoefficientMaxwellIntrinsicFirstVariation4D
open P0EFTJanusMetricInducedMaxwellResidual4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

open scoped InnerProductSpace
open P0EFTJanusProgramPT12RegularTensorCovectorL24D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusStrongMaxwellMetricResidual4D

variable (metric : RegularGeneralLorentzMetric period hPeriod)
  (potential : SmoothAbelianGaugePotential period hPeriod)

open P0EFTJanusProgramPT12MaxwellStressCoefficients4D
open P0EFTJanusProgramPT12InducedMaxwellMetricL24D

open P0EFTJanusProgramPT12FullMaxwellMetricL24D
open P0EFTJanusProgramPT12MaxwellCoefficientQuadratic4D
open P0EFTJanusProgramPT12QuadraticParameterDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D

open P0EFTJanusProgramPT12MixedPartialHessian4D
open P0EFTJanusProgramPT12MaxwellMixedMetricL24D

/-- The original mobile-frame action on its completed joint chart. -/
def nativeMobileMaxwellAction
    (input : RegularGeneralMetricC2Core period hPeriod metric ×
      RegularGeneralMetricC2GaugeCoefficientCore period hPeriod) : Real :=
  regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction period hPeriod metric
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) input.1 input.2

theorem nativeMobileMaxwellAction_contDiffAt
    (coefficients : RegularGeneralMetricC2GaugeCoefficientCore period hPeriod) :
    ContDiffAt Real 2 (nativeMobileMaxwellAction period hPeriod metric) (0, coefficients) := by
  have hOpen : IsOpen (regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain period hPeriod metric) :=
    (regularGeneralMetricC2LorentzChartDomain_isOpen period hPeriod metric).prod isOpen_univ
  exact (regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
    period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).contDiffAt
    (hOpen.mem_nhds ⟨zero_mem_regularGeneralMetricC2LorentzChartDomain period hPeriod metric,
      Set.mem_univ coefficients⟩)

/-- Exact smooth potential injection into the completed gauge coordinates. -/
def maxwellSmoothGaugeC2 : SmoothAbelianGaugePotential period hPeriod →ₗ[Real]
    RegularGeneralMetricC2GaugeCoefficientCore period hPeriod :=
  (smoothGaugeCoefficientC2CoreLinearMap period hPeriod).comp
    (gaugePotentialFrameCoefficientsLinearMap period hPeriod metric)

/-- The true second Frechet derivative, with both metric and gauge slots. -/
def nativeMobileMaxwellHessian :=
  fderiv Real (fderiv Real (nativeMobileMaxwellAction period hPeriod metric))
    (0, maxwellSmoothGaugeC2 period hPeriod metric potential)

attribute [local irreducible] nativeMobileMaxwellAction maxwellSmoothGaugeC2

theorem nativeMobileMaxwellHessian_symmetric
    (first second : RegularGeneralMetricC2Core period hPeriod metric ×
      RegularGeneralMetricC2GaugeCoefficientCore period hPeriod) :
    nativeMobileMaxwellHessian period hPeriod metric potential first second =
      nativeMobileMaxwellHessian period hPeriod metric potential second first :=
  (nativeMobileMaxwellAction_contDiffAt period hPeriod metric
    (maxwellSmoothGaugeC2 period hPeriod metric potential)).isSymmSndFDerivAt (by norm_num) first second

theorem nativeMobileMaxwellHessian_mixed_hasDerivAt
    (direction : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    HasDerivAt (fun t : Real => fullMaxwellMetricVariation period hPeriod metric
      (potential + t • direction) tensor)
      (nativeMobileMaxwellHessian period hPeriod metric potential
        (0, maxwellSmoothGaugeC2 period hPeriod metric direction)
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor, 0)) 0 := by
  have hFirst (current : RegularGeneralMetricC2GaugeCoefficientCore period hPeriod) :=
    (nativeMobileMaxwellAction_contDiffAt period hPeriod metric current).differentiableAt (by norm_num)
  have hSecond := ((nativeMobileMaxwellAction_contDiffAt period hPeriod metric
    (maxwellSmoothGaugeC2 period hPeriod metric potential)).fderiv_right
      (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have h := metricPartial_hasDerivAt (nativeMobileMaxwellAction period hPeriod metric)
    (maxwellSmoothGaugeC2 period hPeriod metric potential)
    (maxwellSmoothGaugeC2 period hPeriod metric direction)
    (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) hFirst hSecond
  have hEq (t : Real) :
      fderiv Real (fun x => nativeMobileMaxwellAction period hPeriod metric
        (x, maxwellSmoothGaugeC2 period hPeriod metric potential +
          t • maxwellSmoothGaugeC2 period hPeriod metric direction)) 0
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      fullMaxwellMetricVariation period hPeriod metric (potential + t • direction) tensor := by
    rw [← map_smul, ← map_add]
    unfold nativeMobileMaxwellAction maxwellSmoothGaugeC2 fullMaxwellMetricVariation
    rfl
  simpa only [hEq, nativeMobileMaxwellHessian] using h

/-- The previously derived L2 vector is an entry of the native joint Hessian. -/
theorem nativeMobileMaxwellHessian_gauge_metric
    (direction : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    nativeMobileMaxwellHessian period hPeriod metric potential
      (0, maxwellSmoothGaugeC2 period hPeriod metric direction)
      (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor, 0) =
    inner Real (maxwellMixedMetricRiesz period hPeriod metric potential direction)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) :=
  (nativeMobileMaxwellHessian_mixed_hasDerivAt period hPeriod metric potential direction tensor).unique
    (fullMaxwellMetricVariation_hasDerivAt_potential period hPeriod metric potential direction tensor)

theorem nativeMobileMaxwellHessian_metric_gauge
    (direction : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    nativeMobileMaxwellHessian period hPeriod metric potential
      (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor, 0)
      (0, maxwellSmoothGaugeC2 period hPeriod metric direction) =
    inner Real (maxwellMixedMetricRiesz period hPeriod metric potential direction)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) := by
  rw [nativeMobileMaxwellHessian_symmetric, nativeMobileMaxwellHessian_gauge_metric]

theorem nativeMobileMaxwellHessian_metric_gauge_bound
    (direction : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ‖nativeMobileMaxwellHessian period hPeriod metric potential
      (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor, 0)
      (0, maxwellSmoothGaugeC2 period hPeriod metric direction)‖ ≤
    ‖maxwellMixedMetricRiesz period hPeriod metric potential direction‖ *
      ‖globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor‖ := by
  rw [nativeMobileMaxwellHessian_metric_gauge]
  exact norm_inner_le_norm _ _

end
end P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D
end JanusFormal
