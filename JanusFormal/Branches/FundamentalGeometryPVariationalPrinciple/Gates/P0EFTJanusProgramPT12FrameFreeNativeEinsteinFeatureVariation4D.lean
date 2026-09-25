import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeNativeInverseSpatialJet4D

/-! Assembly of all native Einstein feature velocities and accelerations. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeEinsteinFeatureVariation4D
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

private theorem postFirst {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (linear : F →L[Real] G) (field : E → F) (point : E)
    (h : DifferentiableAt Real field point) :
    fderiv Real (linear ∘ field) point = linear.comp (fderiv Real field point) :=
  (linear.hasFDerivAt.comp point h.hasFDerivAt).fderiv

private theorem prodFirst {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (f : E → F) (g : E → G) (point direction : E)
    (h : DifferentiableAt Real (fun x => (f x, g x)) point) :
    fderiv Real (fun x => (f x, g x)) point direction =
      (fderiv Real f point direction, fderiv Real g point direction) := by
  apply Prod.ext
  · exact (congrArg (fun op : E →L[Real] F => op direction)
      (postFirst (ContinuousLinearMap.fst Real F G) _ point h)).symm
  · exact (congrArg (fun op : E →L[Real] G => op direction)
      (postFirst (ContinuousLinearMap.snd Real F G) _ point h)).symm

private theorem prodHessian {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (f : E → F) (g : E → G) (point first second : E)
    (h : ContDiffAt Real 2 (fun x => (f x, g x)) point) :
    fderiv Real (fderiv Real (fun x => (f x, g x))) point first second =
      (fderiv Real (fderiv Real f) point first second, fderiv Real (fderiv Real g) point first second) := by
  exact Prod.ext
    (P0EFTJanusProgramPT12VectorHessianPullback4D.linearPostHessian
      (ContinuousLinearMap.fst Real F G) _ point first second h).symm
    (P0EFTJanusProgramPT12VectorHessianPullback4D.linearPostHessian
      (ContinuousLinearMap.snd Real F G) _ point first second h).symm

private theorem affineFirst {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (field : F → G) (base : F) (readout : E →L[Real] F)
    (h : DifferentiableAt Real field base) (direction : E) :
    fderiv Real (fun x => field (base + readout x)) 0 direction =
      fderiv Real field base (readout direction) := by
  have hOuter : HasFDerivAt field (fderiv Real field base) (base + readout 0) := by
    simpa only [map_zero, add_zero] using h.hasFDerivAt
  exact congrArg (fun op : E →L[Real] G => op direction)
    (hOuter.comp 0 (readout.hasFDerivAt.const_add base)).fderiv

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
open P0EFTJanusProgramPT12FrameFreeNativeEinsteinJetHessian4D
open P0EFTJanusProgramPT12FrameFreeNativeMetricJetVariation4D
open P0EFTJanusProgramPT12FrameFreeNativeInverseSpatialJet4D
open P0EFTJanusProgramPT12FiniteFrameMatrixFirstJet4D
open P0EFTJanusProgramPT12FrameFreeNativeVolumeJet4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D

abbrev GroupedEinsteinJet (n : Nat) :=
  Real × (MetricMatrix n × MetricFirstJet n × MetricSecondJet n) × FiniteMatrixFirstJet n

def groupEinsteinFeatures {n : Nat} : (Real × CurvatureJet n) →L[Real] GroupedEinsteinJet n :=
  LinearMap.toContinuousLinearMap {
    toFun := fun f => (f.1, (f.2.1, f.2.2.2.1, f.2.2.2.2.1), (f.2.2.1, f.2.2.2.2.2))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def ungroupEinsteinFeatures {n : Nat} : GroupedEinsteinJet n →L[Real] (Real × CurvatureJet n) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun g => (g.1, g.2.1.1, g.2.2.1, g.2.1.2.1, g.2.1.2.2, g.2.2.2)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def frameFreeNativeGroupedEinsteinFeatures (variation : Model) (point : EffectiveQuotient period hPeriod) : GroupedEinsteinJet frame.count :=
  (finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric variation point,
    frameFreeNativeMetricRawJet period hPeriod frame baseMetric variation point,
    frameFreeNativeInverseFirstJet period hPeriod frame baseMetric variation point)

variable (point : EffectiveQuotient period hPeriod)
local notation "grouped" => fun variation => frameFreeNativeGroupedEinsteinFeatures period hPeriod frame baseMetric variation point
local notation "volume" => fun variation => finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric variation point
local notation "volumeSymbol" => finiteVolumeSymbol (dimension := frame.count) (globalSmoothMetricVolumeRatio period hPeriod baseMetric point)
local notation "relativeValue" => frameFreeRelativeMatrixAt period hPeriod frame baseMetric point
local notation "jetReadout" => finiteFrameMatrixFirstJetReadout period hPeriod frame baseMetric point
local notation "jetProduct" => finiteMatrixFirstJetProduct (dimension := frame.count)
local notation "baseInverse" => smoothFiniteMatrixToC2 period hPeriod frame.count
  (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric)

theorem frameFreeNativeGroupedEinsteinFeatures_contDiffAt : ContDiffAt Real 2 grouped 0 :=
  (groupEinsteinFeatures (n := frame.count)).contDiff.contDiffAt.comp 0
    (frameFreeNativeEinsteinFeatures_contDiffAt_zero period hPeriod frame baseMetric point)

theorem frameFreeNativeVolume_fderiv (direction : Model) :
    fderiv Real volume 0 direction = fderiv Real volumeSymbol 1 (relativeValue direction) := by
  rw [(frameFreeNativeVolume_eventually_eq_symbol period hPeriod frame baseMetric point).fderiv_eq]
  exact affineFirst volumeSymbol 1 relativeValue
    ((finiteVolumeSymbol_contDiffAt_one _).differentiableAt (by simp)) direction

def frameFreeEinsteinFeatureVelocity (direction : Model) : GroupedEinsteinJet frame.count :=
  (fderiv Real volumeSymbol 1 (relativeValue direction),
    frameFreeMetricRawJetReadout period hPeriod frame baseMetric point direction,
    -(jetProduct (jetReadout direction.1) (jetReadout baseInverse)))

def frameFreeEinsteinFeatureAcceleration (first second : Model) : GroupedEinsteinJet frame.count :=
  (fderiv Real (fderiv Real volumeSymbol) 1 (relativeValue first) (relativeValue second),
    0, jetProduct (jetProduct (jetReadout second.1) (jetReadout first.1) +
      jetProduct (jetReadout first.1) (jetReadout second.1)) (jetReadout baseInverse))

theorem frameFreeNativeGroupedEinsteinFeatures_fderiv (direction : Model) :
    fderiv Real grouped 0 direction = frameFreeEinsteinFeatureVelocity period hPeriod frame baseMetric point direction := by
  have h := (frameFreeNativeGroupedEinsteinFeatures_contDiffAt period hPeriod frame baseMetric point).differentiableAt (by norm_num)
  change fderiv Real (fun variation => (volume variation,
    frameFreeNativeMetricRawJet period hPeriod frame baseMetric variation point,
    frameFreeNativeInverseFirstJet period hPeriod frame baseMetric variation point)) 0 direction = _
  rw [prodFirst _ _ 0 direction h, prodFirst _ _ 0 direction h.snd,
    frameFreeNativeVolume_fderiv, frameFreeNativeMetricRawJet_fderiv, frameFreeNativeInverseFirstJet_fderiv]
  rfl

private theorem metricInversePair_hessian (first second : Model) :
    fderiv Real (fderiv Real (fun variation =>
      (frameFreeNativeMetricRawJet period hPeriod frame baseMetric variation point,
        frameFreeNativeInverseFirstJet period hPeriod frame baseMetric variation point))) 0 first second =
      (frameFreeEinsteinFeatureAcceleration period hPeriod frame baseMetric point first second).2 := by
  have h := (frameFreeNativeGroupedEinsteinFeatures_contDiffAt period hPeriod frame baseMetric point).snd
  refine (prodHessian _ _ 0 first second h).trans ?_
  apply Prod.ext
  · exact congrArg (fun op => op first second)
      (frameFreeNativeMetricRawJet_hessian_zero period hPeriod frame baseMetric point 0)
  · exact frameFreeNativeInverseFirstJet_hessian period hPeriod frame baseMetric point first second

theorem frameFreeNativeGroupedEinsteinFeatures_hessian (first second : Model) :
    fderiv Real (fderiv Real grouped) 0 first second =
      frameFreeEinsteinFeatureAcceleration period hPeriod frame baseMetric point first second := by
  have h := frameFreeNativeGroupedEinsteinFeatures_contDiffAt period hPeriod frame baseMetric point
  refine (prodHessian volume _ 0 first second h).trans ?_
  apply Prod.ext
  · exact frameFreeNativeVolume_hessian period hPeriod frame baseMetric point first second
  · exact metricInversePair_hessian period hPeriod frame baseMetric point first second

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeEinsteinFeatureVariation4D
