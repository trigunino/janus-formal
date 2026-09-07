import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMobileMaxwellActionRecenter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D

/-! # Completed root identity for the genuine gauge coefficient transition

The two root transports of the transitioned packet equal the direct root
transport of the original packet. The transition packet remains inside this
identity: differentiating it must retain its metric-induced velocity.
-/

namespace JanusFormal
namespace P0EFTJanusGaugeCoefficientRecenterRootTransport4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusRegularFrameGaugeCoefficientTransition4D
open P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C2Matrix := C2FiniteMatrix period hPeriod 4
private abbrev GaugeC2Core := RegularGeneralMetricC2GaugeCoefficientCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Root transport of arbitrary moving-frame coefficients reads the reconstructed potential
in the fixed base frame. -/
theorem gaugeCoefficientC2CoreFrameTransport_reconstructed
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod metric variation ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    gaugeCoefficientC2CoreFrameTransport period hPeriod
        (c2IdentityRootBranch period hPeriod
          (regularGeneralMetricC2VariationMatrix period hPeriod metric variation))
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) =
      smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric
          (regularFrameGaugePotentialFromCoefficients period hPeriod
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric variation hVariation)
            coefficients)) := by
  simpa only [gaugePotentialFrameCoefficients_reconstructed] using
    gaugeCoefficientC2CoreFrameTransport_lorentzChart period hPeriod metric variation hVariation
      (regularFrameGaugePotentialFromCoefficients period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric variation hVariation)
        coefficients)

/-- Exact completed identity for the metric-dependent transition in the recentered Maxwell action. -/
theorem gaugeCoefficientRecenter_rootTransport
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift increment : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hTotal : regularGeneralMetricSmoothC2Variation period hPeriod metric (shift + increment) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hIncrement : regularGeneralMetricSmoothC2Variation period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift) increment ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift))
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
    let originalFinal := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
      metric (shift + increment) hTotal
    let recenteredFinal := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
      shifted increment hIncrement
    gaugeCoefficientC2CoreFrameTransport period hPeriod
      (c2IdentityRootBranch period hPeriod
        (regularGeneralMetricC2VariationMatrix period hPeriod metric shift))
      (gaugeCoefficientC2CoreFrameTransport period hPeriod
        (c2IdentityRootBranch period hPeriod
          (regularGeneralMetricC2VariationMatrix period hPeriod shifted increment))
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (regularFrameGaugeCoefficientTransition period hPeriod originalFinal recenteredFinal coefficients))) =
    gaugeCoefficientC2CoreFrameTransport period hPeriod
      (c2IdentityRootBranch period hPeriod
        (regularGeneralMetricC2VariationMatrix period hPeriod metric (shift + increment)))
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) := by
  dsimp only
  rw [gaugeCoefficientC2CoreFrameTransport_reconstructed period hPeriod _ increment hIncrement,
    regularFrameGaugeCoefficientTransition_preserves_potential,
    gaugeCoefficientC2CoreFrameTransport_lorentzChart period hPeriod metric shift hShift,
    gaugeCoefficientC2CoreFrameTransport_reconstructed period hPeriod metric (shift + increment) hTotal]

/-- The root-induced derivative at an arbitrary admissible matrix point uses the actual
Sylvester derivative, with no identity-centre simplification. -/
theorem c2IdentityGaugeCoefficientTransport_hasFDerivAt
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈ c2IdentityRootPerturbationDomain period hPeriod)
    (coefficients : GaugeC2Core period hPeriod) :
    HasFDerivAt
      (fun current => gaugeCoefficientC2CoreFrameTransport period hPeriod
        (c2IdentityRootBranch period hPeriod current) coefficients)
      ((gaugeCoefficientC2CoreFrameTransportLeftCLM period hPeriod coefficients).comp
        (c2IdentityRootDerivative period hPeriod variation hVariation)) variation := by
  have hDerivative :=
    (gaugeCoefficientC2CoreFrameTransportLeftCLM period hPeriod coefficients).hasFDerivAt.comp
      variation (c2IdentityRootBranch_hasFDerivAt period hPeriod variation hVariation)
  simpa only [Function.comp_def, gaugeCoefficientC2CoreFrameTransportLeftCLM_apply] using hDerivative

theorem c2IdentityGaugeCoefficientTransport_fderiv_apply
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈ c2IdentityRootPerturbationDomain period hPeriod)
    (coefficients : GaugeC2Core period hPeriod)
    (direction : C2Matrix period hPeriod) :
    fderiv Real
      (fun current => gaugeCoefficientC2CoreFrameTransport period hPeriod
        (c2IdentityRootBranch period hPeriod current) coefficients) variation direction =
      gaugeCoefficientC2CoreFrameTransport period hPeriod
        (c2IdentityRootDerivative period hPeriod variation hVariation direction) coefficients := by
  simpa only [ContinuousLinearMap.comp_apply,
    gaugeCoefficientC2CoreFrameTransportLeftCLM_apply] using
    congrArg (fun derivative => derivative direction)
      (c2IdentityGaugeCoefficientTransport_hasFDerivAt period hPeriod variation hVariation coefficients).fderiv

end
end P0EFTJanusGaugeCoefficientRecenterRootTransport4D
end JanusFormal
