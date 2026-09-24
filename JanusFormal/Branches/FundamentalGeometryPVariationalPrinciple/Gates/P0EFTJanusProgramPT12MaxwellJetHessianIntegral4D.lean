import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NativeMaxwellJetBridge4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12MaxwellJetHessianIntegral4D

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

open P0EFTJanusProgramPT12NativeMaxwellJetBridge4D

/-- The finite-symbol Hessian retains the full inverse and gauge-transport acceleration. -/
def nativeMobileMaxwellJetHessianDensity
    (first second : RegularGeneralMetricC2Core period hPeriod metric) (point : EffectiveQuotient period hPeriod) : Real :=
  let jet := fun variation => nativeMobileMaxwellJet period hPeriod metric potential variation point
  maxwellSymbolHessian (metric.volume point, jet 0)
    (fderiv Real jet 0 first) (fderiv Real jet 0 second) +
  maxwellSymbolGradient (metric.volume point, jet 0)
    (fderiv Real (fderiv Real jet) 0 first second)

theorem nativeMobileMaxwellDensity_hessian_eq_jet
    (first second : RegularGeneralMetricC2Core period hPeriod metric) (point : EffectiveQuotient period hPeriod) :
    fderiv Real (fderiv Real (fun variation =>
      nativeMobileMaxwellDensity period hPeriod metric potential variation point)) 0 first second =
      nativeMobileMaxwellJetHessianDensity period hPeriod metric potential first second point := by
  let jet := fun variation => nativeMobileMaxwellJet period hPeriod metric potential variation point
  let symbol := fun current => maxwellSymbol (metric.volume point, current)
  have hEq : (fun variation => nativeMobileMaxwellDensity period hPeriod metric potential variation point) =
      symbol ∘ jet := funext fun variation => nativeMobileMaxwellDensity_eq_symbol period hPeriod metric potential variation point
  have h := congrArg (fun action : RegularGeneralMetricC2Core period hPeriod metric → Real =>
    fderiv Real (fderiv Real action) 0 first second) hEq
  exact h.trans (nonlinearHessian symbol jet 0 first second
    ((maxwellSymbol_jet_contDiff (metric.volume point)).contDiffAt.of_le (by decide))
    (nativeMobileMaxwellJet_contDiffAt_zero period hPeriod metric potential point))

attribute [local irreducible] nativeMobileMaxwellAction nativeMobileMaxwellHessian nativeMobileMaxwellDensity
  maxwellSmoothGaugeC2 nativeMobileMaxwellJetHessianDensity

/-- The actual mobile metric-metric Hessian is the integral of this finite-jet formula. -/
theorem nativeMobileMaxwellHessian_eq_jetIntegral
    (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    nativeMobileMaxwellHessian period hPeriod metric potential (first, 0) (second, 0) =
      ∫ point, nativeMobileMaxwellJetHessianDensity period hPeriod metric potential first second point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  let coefficients := maxwellSmoothGaugeC2 period hPeriod metric potential
  let density := nativeMobileMaxwellDensity period hPeriod metric potential
  let integral := regularGeneralMetricC0IntegralCLM period hPeriod (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  let projection : RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      RegularGeneralMetricC2Core period hPeriod metric ×
        RegularGeneralMetricC2GaugeCoefficientCore period hPeriod :=
    (ContinuousLinearMap.id Real _).prod 0
  have hAffine := affineHessian (nativeMobileMaxwellAction period hPeriod metric)
    (0, coefficients) projection (nativeMobileMaxwellAction_contDiffAt period hPeriod metric coefficients)
    first second
  have hEq : (fun variation => nativeMobileMaxwellAction period hPeriod metric
      ((0, coefficients) + projection variation)) = integral ∘ density := by
    funext variation
    simp only [projection, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      zero_apply, Prod.mk_add_mk, zero_add, add_zero]
    unfold integral density nativeMobileMaxwellAction nativeMobileMaxwellDensity
    rfl
  have hEqDerivative := congrArg (fun action : RegularGeneralMetricC2Core period hPeriod metric → Real =>
    fderiv Real (fderiv Real action) 0 first second) hEq
  have hRestriction : nativeMobileMaxwellHessian period hPeriod metric potential (first, 0) (second, 0) =
      fderiv Real (fderiv Real (integral ∘ density)) 0 first second := by
    unfold nativeMobileMaxwellHessian
    exact hAffine.symm.trans hEqDerivative
  have hDensity := nativeMobileMaxwellDensity_contDiffAt_zero period hPeriod metric potential
  have hIntegral := hRestriction.trans (linearPostHessian integral density 0 first second hDensity)
  refine hIntegral.trans ?_
  change integral _ = _
  rw [regularGeneralMetricC0IntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with point
  let evaluation : C(EffectiveQuotient period hPeriod, Real) →L[Real] Real := ContinuousMap.evalCLM Real point
  exact (linearPostHessian evaluation density 0 first second hDensity).symm.trans
    (nativeMobileMaxwellDensity_hessian_eq_jet period hPeriod metric potential first second point)

end
end P0EFTJanusProgramPT12MaxwellJetHessianIntegral4D
end JanusFormal
