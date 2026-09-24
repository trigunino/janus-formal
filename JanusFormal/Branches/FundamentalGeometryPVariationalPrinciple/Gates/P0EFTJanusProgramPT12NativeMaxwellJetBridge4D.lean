import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellMetricHessianTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellJetSymbol4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeMaxwellJetBridge4D

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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

open P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D
open P0EFTJanusProgramPT12MobileMetricChartHessian4D
open P0EFTJanusProgramPT12NonlinearHessianPullback4D
open P0EFTJanusProgramPT12VectorHessianPullback4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D

open P0EFTJanusProgramPT12MaxwellJetSymbol4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D

/-- The original mobile density, before the continuous integral map. -/
def nativeMobileMaxwellDensity (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    C(EffectiveQuotient period hPeriod, Real) :=
  regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellDensity period hPeriod metric variation
    (regularGeneralMetricC2MobileGaugeCoefficientTransport period hPeriod metric variation
      (maxwellSmoothGaugeC2 period hPeriod metric potential))

/-- Both slots are read from the native completed chart, not independent substitutes. -/
def nativeMobileMaxwellJet (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) : MaxwellJet :=
  (fun row column => regularGeneralMetricC0InverseMetricCoefficient
    period hPeriod metric variation row column point,
   fun component row column => regularFrameGaugeCurvatureC0FromC2Coefficients period hPeriod metric
    (regularGeneralMetricC2MobileGaugeCoefficientTransport period hPeriod metric variation
      (maxwellSmoothGaugeC2 period hPeriod metric potential)) component row column point)

theorem nativeMobileMaxwellDensity_eq_symbol
    (variation : RegularGeneralMetricC2Core period hPeriod metric) (point : EffectiveQuotient period hPeriod) :
    nativeMobileMaxwellDensity period hPeriod metric potential variation point =
      maxwellSymbol (metric.volume point, nativeMobileMaxwellJet period hPeriod metric potential variation point) := by
  simp only [nativeMobileMaxwellDensity, regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellDensity,
    regularGeneralMetricC0GaugeCoefficientMaxwellPairing, c0MaxwellMatrixContraction,
    regularFrameGaugeCurvatureC0MatrixFromC2Coefficients, ContinuousMap.mul_apply,
    ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul, maxwellSymbol, nativeMobileMaxwellJet]
  rfl

private theorem fixedDensity_contDiffAt
    (coefficients : RegularGeneralMetricC2GaugeCoefficientCore period hPeriod) :
    ContDiffAt Real 2
      (fun input : RegularGeneralMetricC2Core period hPeriod metric ×
          RegularGeneralMetricC2GaugeCoefficientCore period hPeriod =>
        regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellDensity
          period hPeriod metric input.1 input.2) (0, coefficients) := by
  have hOpen : IsOpen (regularGeneralMetricC2GaugeCoefficientMaxwellDomain period hPeriod metric) :=
    (regularGeneralMetricC2Domain_isOpen period hPeriod metric).prod isOpen_univ
  have hPairing : ContDiffAt Real 2
      (fun input : RegularGeneralMetricC2Core period hPeriod metric ×
          RegularGeneralMetricC2GaugeCoefficientCore period hPeriod =>
        regularGeneralMetricC0GaugeCoefficientMaxwellPairing period hPeriod metric input.1 input.2)
      (0, coefficients) := (regularGeneralMetricC0GaugeCoefficientMaxwellPairing_contDiffOn_two
    period hPeriod metric).contDiffAt
      (hOpen.mem_nhds ⟨zero_mem_regularGeneralMetricC2Domain period hPeriod metric, Set.mem_univ coefficients⟩)
  have hDensity : ContDiffAt Real 2
      (fun input : RegularGeneralMetricC2Core period hPeriod metric ×
          RegularGeneralMetricC2GaugeCoefficientCore period hPeriod =>
        regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellDensity
          period hPeriod metric input.1 input.2) (0, coefficients) :=
    contDiffAt_const.mul (hPairing.const_smul _)
  exact hDensity

attribute [local irreducible] nativeMobileMaxwellDensity mobileMetricChart
  regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellDensity maxwellSmoothGaugeC2

theorem nativeMobileMaxwellDensity_contDiffAt_zero :
    ContDiffAt Real 2 (nativeMobileMaxwellDensity period hPeriod metric potential) 0 := by
  let coefficients := maxwellSmoothGaugeC2 period hPeriod metric potential
  have hDensity := fixedDensity_contDiffAt period hPeriod metric coefficients
  have hAt : ContDiffAt Real 2
      (fun input : RegularGeneralMetricC2Core period hPeriod metric ×
          RegularGeneralMetricC2GaugeCoefficientCore period hPeriod =>
        regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellDensity
          period hPeriod metric input.1 input.2)
      (mobileMetricChart period hPeriod metric coefficients 0) := by
    simpa only [mobileMetricChart_zero] using hDensity
  have h := hAt.comp 0 (mobileMetricChart_contDiffAt_zero period hPeriod metric coefficients)
  apply h.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro variation
  unfold nativeMobileMaxwellDensity mobileMetricChart
  rfl

theorem nativeMobileMaxwellJet_contDiffAt_zero (point : EffectiveQuotient period hPeriod) :
    ContDiffAt Real 2 (fun variation => nativeMobileMaxwellJet period hPeriod metric potential variation point) 0 := by
  let evaluation : C(EffectiveQuotient period hPeriod, Real) →L[Real] Real := ContinuousMap.evalCLM Real point
  have hInverse (row column : Fin 4) : ContDiffAt Real 2
      (fun variation => regularGeneralMetricC0InverseMetricCoefficient
        period hPeriod metric variation row column point) 0 :=
    evaluation.contDiff.contDiffAt.comp 0
      (((regularGeneralMetricC0InverseMetricCoefficient_contDiffOn period hPeriod metric row column).contDiffAt
        ((regularGeneralMetricC2Domain_isOpen period hPeriod metric).mem_nhds
          (zero_mem_regularGeneralMetricC2Domain period hPeriod metric))).of_le (by decide))
  have hGauge := (mobileMetricChart_contDiffAt_zero period hPeriod metric
    (maxwellSmoothGaugeC2 period hPeriod metric potential)).snd
  unfold mobileMetricChart at hGauge
  have hCurvature (component : Fin 2) (row column : Fin 4) :=
    evaluation.contDiff.contDiffAt.comp 0
      ((regularFrameGaugeCurvatureC0FromC2Coefficients_contDiff period hPeriod metric component row column).contDiffAt.of_le (show (2 : ℕ∞ω) ≤ ∞ by decide) |>.comp 0 hGauge)
  exact (contDiffAt_pi.mpr fun row => contDiffAt_pi.mpr fun column => hInverse row column).prodMk
    (contDiffAt_pi.mpr fun component => contDiffAt_pi.mpr fun row => contDiffAt_pi.mpr
      fun column => hCurvature component row column)

end
end P0EFTJanusProgramPT12NativeMaxwellJetBridge4D
end JanusFormal
