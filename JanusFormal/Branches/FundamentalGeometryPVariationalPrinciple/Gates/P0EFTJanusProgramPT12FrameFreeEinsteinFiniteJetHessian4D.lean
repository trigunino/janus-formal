import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeNativeEinsteinFeatureVariation4D

/-! The genuine pointwise Einstein Hessian factors through finite variation jets. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeEinsteinFiniteJetHessian4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameC2ScalarCurvature4D
open P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : MeasureTheory.IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

open P0EFTJanusProgramPT12ProjectedCurvatureJetSymbol4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2DeDonderFirstJet4D
open P0EFTJanusFiniteFrameC2ProjectedRicciCompletion4D
open P0EFTJanusFiniteFrameCovectorC2Projection4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
variable (frame : SmoothD8Frame period hPeriod) (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Model" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "N" => Fin frame.count
local notation "Jet" => CurvatureJet frame.count

open P0EFTJanusProgramPT12FrameFreeNativeCurvatureJet4D
open P0EFTJanusProgramPT12NonlinearHessianPullback4D
local instance : NormedAddCommGroup Model := inferInstance
local instance : NormedSpace Real Model := Submodule.normedSpace _

open scoped Matrix.Norms.Elementwise
open P0EFTJanusProgramPT12FrameFreeNativeEinsteinFeatureVariation4D
open P0EFTJanusProgramPT12FrameFreeNativeMetricJetVariation4D
open P0EFTJanusProgramPT12FiniteFrameMatrixFirstJet4D
open P0EFTJanusProgramPT12FrameFreeNativeVolumeJet4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D

abbrev FiniteEinsteinVariation (n : Nat) :=
  (MetricMatrix n × MetricFirstJet n × MetricSecondJet n) × FiniteMatrixFirstJet n

def finiteEinsteinFeatureVelocity {n : Nat} (baseVolume : Real) (baseInverse : FiniteMatrixFirstJet n)
    (variation : FiniteEinsteinVariation n) : GroupedEinsteinJet n :=
  (fderiv Real (finiteVolumeSymbol (dimension := n) baseVolume) (1 : Matrix (Fin n) (Fin n) Real) variation.2.1,
    variation.1, -finiteMatrixFirstJetProduct variation.2 baseInverse)

def finiteEinsteinFeatureAcceleration {n : Nat} (baseVolume : Real) (baseInverse : FiniteMatrixFirstJet n)
    (first second : FiniteEinsteinVariation n) : GroupedEinsteinJet n :=
  (fderiv Real (fderiv Real (finiteVolumeSymbol (dimension := n) baseVolume))
      (1 : Matrix (Fin n) (Fin n) Real) first.2.1 second.2.1,
    0, finiteMatrixFirstJetProduct
      (finiteMatrixFirstJetProduct second.2 first.2 + finiteMatrixFirstJetProduct first.2 second.2) baseInverse)

def groupedEinsteinDensity {n : Nat} (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (projection : MetricMatrix n) (gravitationalCoupling cosmologicalConstant : Real) : GroupedEinsteinJet n → Real :=
  projectedJetEinsteinDensity bracket bracketDerivative projection gravitationalCoupling cosmologicalConstant ∘ ungroupEinsteinFeatures

theorem groupedEinsteinDensity_contDiff {n : Nat} (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (projection : MetricMatrix n) (gravitationalCoupling cosmologicalConstant : Real) :
    ContDiff Real ∞ (groupedEinsteinDensity bracket bracketDerivative projection gravitationalCoupling cosmologicalConstant) :=
  (projectedJetEinsteinDensity_contDiff _ _ _ _ _).comp (ungroupEinsteinFeatures (n := n)).contDiff

def finiteEinsteinJetHessian {n : Nat} (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (projection : MetricMatrix n) (gravitationalCoupling cosmologicalConstant : Real)
    (base : GroupedEinsteinJet n) (baseVolume : Real) (baseInverse : FiniteMatrixFirstJet n)
    (first second : FiniteEinsteinVariation n) : Real :=
  let symbol := groupedEinsteinDensity bracket bracketDerivative projection gravitationalCoupling cosmologicalConstant
  fderiv Real (fderiv Real symbol) base
      (finiteEinsteinFeatureVelocity baseVolume baseInverse first) (finiteEinsteinFeatureVelocity baseVolume baseInverse second) +
    fderiv Real symbol base (finiteEinsteinFeatureAcceleration baseVolume baseInverse first second)

def frameFreeEinsteinVariationReadout (point : EffectiveQuotient period hPeriod) : Model →L[Real] FiniteEinsteinVariation frame.count :=
  (frameFreeMetricRawJetReadout period hPeriod frame baseMetric point).prod
    ((finiteFrameMatrixFirstJetReadout period hPeriod frame baseMetric point).comp
      (generalMetricRelativeC2CoreToMatrix period hPeriod frame baseMetric))

variable (point : EffectiveQuotient period hPeriod)
local notation "grouped" => fun variation => frameFreeNativeGroupedEinsteinFeatures period hPeriod frame baseMetric variation point
local notation "variationJet" => frameFreeEinsteinVariationReadout period hPeriod frame baseMetric point
local notation "baseVolume" => globalSmoothMetricVolumeRatio period hPeriod baseMetric point
local notation "baseInverseJet" => finiteFrameMatrixFirstJetReadout period hPeriod frame baseMetric point
  (smoothFiniteMatrixToC2 period hPeriod frame.count (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric))

theorem frameFreeEinsteinFeatureVelocity_eq_finite (direction : Model) :
    frameFreeEinsteinFeatureVelocity period hPeriod frame baseMetric point direction =
      finiteEinsteinFeatureVelocity baseVolume baseInverseJet (variationJet direction) := rfl

theorem frameFreeEinsteinFeatureAcceleration_eq_finite (first second : Model) :
    frameFreeEinsteinFeatureAcceleration period hPeriod frame baseMetric point first second =
      finiteEinsteinFeatureAcceleration baseVolume baseInverseJet (variationJet first) (variationJet second) := rfl

variable (couplings : EinsteinHilbertCouplings)
local notation "symbol" => groupedEinsteinDensity
  (frameFreeNativeStructureJet period hPeriod frame baseMetric point)
  (frameFreeNativeStructureDerivativeJet period hPeriod frame baseMetric point)
  (frameFreeNativeTraceProjection period hPeriod frame baseMetric point)
  couplings.gravitationalCoupling couplings.cosmologicalConstant

theorem frameFreeNativeEinsteinDensity_eq_grouped (variation : Model) :
    finiteFrameC2EinsteinHilbertDensity period hPeriod frame baseMetric couplings variation point =
      symbol (grouped variation) :=
  frameFreeNativeEinsteinDensity_eq_jet period hPeriod frame baseMetric couplings variation point

private theorem nativeDensity_grouped_hessian (first second : Model) :
    fderiv Real (fderiv Real (fun variation =>
      finiteFrameC2EinsteinHilbertDensity period hPeriod frame baseMetric couplings variation point)) 0 first second =
      fderiv Real (fderiv Real symbol) (grouped 0)
        (fderiv Real grouped 0 first) (fderiv Real grouped 0 second) +
      fderiv Real symbol (grouped 0) (fderiv Real (fderiv Real grouped) 0 first second) := by
  have hAction : (fun variation => finiteFrameC2EinsteinHilbertDensity period hPeriod frame baseMetric couplings variation point) =
      symbol ∘ grouped := funext (frameFreeNativeEinsteinDensity_eq_grouped period hPeriod frame baseMetric point couplings)
  refine (congrArg (fun action : Model → Real => fderiv Real (fderiv Real action) 0 first second) hAction).trans ?_
  exact nonlinearHessian symbol grouped 0 first second
    ((groupedEinsteinDensity_contDiff _ _ _ _ _).contDiffAt.of_le (by decide))
    (frameFreeNativeGroupedEinsteinFeatures_contDiffAt period hPeriod frame baseMetric point)

private theorem groupedFiniteVelocity (direction : Model) :
    fderiv Real grouped 0 direction = finiteEinsteinFeatureVelocity baseVolume baseInverseJet (variationJet direction) :=
  (frameFreeNativeGroupedEinsteinFeatures_fderiv period hPeriod frame baseMetric point direction).trans
    (frameFreeEinsteinFeatureVelocity_eq_finite period hPeriod frame baseMetric point direction)

private theorem groupedFiniteAcceleration (first second : Model) :
    fderiv Real (fderiv Real grouped) 0 first second =
      finiteEinsteinFeatureAcceleration baseVolume baseInverseJet (variationJet first) (variationJet second) :=
  (frameFreeNativeGroupedEinsteinFeatures_hessian period hPeriod frame baseMetric point first second).trans
    (frameFreeEinsteinFeatureAcceleration_eq_finite period hPeriod frame baseMetric point first second)

theorem frameFreeNativeEinsteinDensity_hessian_eq_finite (first second : Model) :
    fderiv Real (fderiv Real (fun variation =>
      finiteFrameC2EinsteinHilbertDensity period hPeriod frame baseMetric couplings variation point)) 0 first second =
      finiteEinsteinJetHessian
        (frameFreeNativeStructureJet period hPeriod frame baseMetric point)
        (frameFreeNativeStructureDerivativeJet period hPeriod frame baseMetric point)
        (frameFreeNativeTraceProjection period hPeriod frame baseMetric point)
        couplings.gravitationalCoupling couplings.cosmologicalConstant
        (grouped 0) baseVolume baseInverseJet (variationJet first) (variationJet second) := by
  refine (nativeDensity_grouped_hessian period hPeriod frame baseMetric point couplings first second).trans ?_
  exact congrArg₂ (fun a b : Real => a + b)
    (congrArg₂ (fun a b : GroupedEinsteinJet frame.count => fderiv Real (fderiv Real symbol) (grouped 0) a b)
      (groupedFiniteVelocity period hPeriod frame baseMetric point first)
      (groupedFiniteVelocity period hPeriod frame baseMetric point second))
    (congrArg (fderiv Real symbol (grouped 0))
      (groupedFiniteAcceleration period hPeriod frame baseMetric point first second))

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeEinsteinFiniteJetHessian4D
