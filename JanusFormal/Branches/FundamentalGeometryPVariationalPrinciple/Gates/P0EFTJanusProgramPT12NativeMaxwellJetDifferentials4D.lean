import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MobileCurvatureDifferentials4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellJetDifferentials4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InverseMetricHessianPointwise4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeMaxwellJetDifferentials4D

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

open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusRegularFrameC2LorenzFeature4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D

open P0EFTJanusProgramPT12NativeMaxwellJetBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
open P0EFTJanusProgramPT12GaugeCurvatureReadout4D
open P0EFTJanusProgramPT12MobileCurvatureDifferentials4D
open P0EFTJanusProgramPT12MaxwellJetDifferentials4D
open P0EFTJanusProgramPT12CurvatureJetSymbol4D
open P0EFTJanusProgramPT12InverseMetricHessianPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotentialDerivative4D

variable (point : EffectiveQuotient period hPeriod)

def nativeMaxwellJetVelocity (direction : RegularGeneralMetricC2Core period hPeriod metric) : MaxwellJet :=
  (fun row column => -((regularGeneralMetricC2RelativeMatrixAt period hPeriod metric direction point) *
      regularFrameMetricInverseMatrixMap period hPeriod metric point) row column,
   (1 / 2 : Real) • gaugeCurvatureReadout period hPeriod metric point
     (gaugeCoefficientC2CoreFrameTransport period hPeriod direction.1
       (maxwellSmoothGaugeC2 period hPeriod metric potential)))

def nativeMaxwellJetAcceleration (first second : RegularGeneralMetricC2Core period hPeriod metric) : MaxwellJet :=
  let firstAt := regularGeneralMetricC2RelativeMatrixAt period hPeriod metric first point
  let secondAt := regularGeneralMetricC2RelativeMatrixAt period hPeriod metric second point
  let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
  (fun row column => ((secondAt * firstAt + firstAt * secondAt) *
      regularFrameMetricInverseMatrixMap period hPeriod metric point) row column,
   (-(1 / 8 : Real)) • gaugeCurvatureReadout period hPeriod metric point
     (gaugeCoefficientC2CoreFrameTransport period hPeriod
       (product first.1 second.1 + product second.1 first.1)
       (maxwellSmoothGaugeC2 period hPeriod metric potential)))

private theorem inverseCoefficient_velocity (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (row column : Fin 4) :
    fderiv Real (fun variation => regularGeneralMetricC0InverseMetricCoefficient
      period hPeriod metric variation row column point) 0 direction =
      -((regularGeneralMetricC2RelativeMatrixAt period hPeriod metric direction point) *
        regularFrameMetricInverseMatrixMap period hPeriod metric point) row column := by
  let evaluation : C(EffectiveQuotient period hPeriod, Real) →L[Real] Real := ContinuousMap.evalCLM Real point
  have h := evaluation.hasFDerivAt.comp 0
    (regularGeneralMetricC0InverseMetricCoefficient_hasFDerivAt_zero period hPeriod metric row column)
  have hEq := congrArg (fun derivative => derivative direction) h.fderiv
  exact hEq.trans (congrArg (fun matrix : Matrix (Fin 4) (Fin 4) Real => matrix row column)
    (regularGeneralMetricC0InverseMetricVelocityAt_eq_relative period hPeriod metric direction point))

private theorem curvatureSlot_eq :
    (ContinuousLinearMap.snd Real MetricMatrix MaxwellCurvature) ∘
        (fun variation => nativeMobileMaxwellJet period hPeriod metric potential variation point) =
      mobileCurvature period hPeriod metric (maxwellSmoothGaugeC2 period hPeriod metric potential) point := by
  funext variation component row column
  exact (gaugeCurvatureReadout_apply period hPeriod metric point _ component row column).symm

/-- Full first derivative: inverse velocity and root-induced gauge curvature velocity. -/
theorem nativeMobileMaxwellJet_fderiv_zero
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    fderiv Real (fun variation => nativeMobileMaxwellJet period hPeriod metric potential variation point) 0 direction =
      nativeMaxwellJetVelocity period hPeriod metric potential point direction := by
  let field := fun variation => nativeMobileMaxwellJet period hPeriod metric potential variation point
  have hC1 := (nativeMobileMaxwellJet_contDiffAt_zero period hPeriod metric potential point).differentiableAt (by norm_num)
  apply Prod.ext
  · funext row column
    have h := (inverseReadout row column).hasFDerivAt.comp 0 hC1.hasFDerivAt
    have hEq := congrArg (fun derivative => derivative direction) h.fderiv
    exact hEq.symm.trans (inverseCoefficient_velocity period hPeriod metric point direction row column)
  · let readout := ContinuousLinearMap.snd Real MetricMatrix MaxwellCurvature
    have h := readout.hasFDerivAt.comp 0 hC1.hasFDerivAt
    have hEq := congrArg (fun derivative => derivative direction) h.fderiv
    have hSlot := congrArg (fun current : RegularGeneralMetricC2Core period hPeriod metric → MaxwellCurvature =>
      fderiv Real current 0 direction) (curvatureSlot_eq period hPeriod metric potential point)
    exact hEq.symm.trans (hSlot.trans (mobileCurvature_fderiv_zero period hPeriod metric
      (maxwellSmoothGaugeC2 period hPeriod metric potential) point direction))

/-- Full acceleration: true inverse acceleration and both noncommuting root products. -/
theorem nativeMobileMaxwellJet_hessian_zero
    (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    fderiv Real (fderiv Real (fun variation => nativeMobileMaxwellJet period hPeriod metric potential variation point))
      0 first second = nativeMaxwellJetAcceleration period hPeriod metric potential point first second := by
  let field := fun variation => nativeMobileMaxwellJet period hPeriod metric potential variation point
  have hC2 := nativeMobileMaxwellJet_contDiffAt_zero period hPeriod metric potential point
  apply Prod.ext
  · funext row column
    exact (linearPostHessian (inverseReadout row column) field 0 first second hC2).symm.trans
      (nativeInverseCoefficient_hessian_pointwise period hPeriod metric first second point row column)
  · let readout := ContinuousLinearMap.snd Real MetricMatrix MaxwellCurvature
    have h := linearPostHessian readout field 0 first second hC2
    have hSlot := congrArg (fun current : RegularGeneralMetricC2Core period hPeriod metric → MaxwellCurvature =>
      fderiv Real (fderiv Real current) 0 first second) (curvatureSlot_eq period hPeriod metric potential point)
    exact h.symm.trans (hSlot.trans (mobileCurvature_hessian_zero period hPeriod metric
      (maxwellSmoothGaugeC2 period hPeriod metric potential) point first second))

end
end P0EFTJanusProgramPT12NativeMaxwellJetDifferentials4D
end JanusFormal
