import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12L2VolumeMultiplier4D

/-! Bounded Maxwell pairing on the genuine curvature/Lorenz graph, with exact
agreement with the native C² Maxwell bilinear form on smooth potentials. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphPairing4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusProgramPT12L2VolumeMultiplier4D

private def weightedL2Pairing {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (weight : C(X, Real)) :
    Lp Real 2 μ →L[Real] Lp Real 2 μ →L[Real] Real :=
  (innerSL Real).bilinearComp
    (l2VolumeMultiplier μ (ContinuousMap.linearIsometryBoundedOfCompact X Real Real weight))
    (ContinuousLinearMap.id Real _)

private theorem weightedL2Pairing_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (weight first second : C(X, Real)) :
    weightedL2Pairing μ weight (ContinuousMap.toLp 2 μ Real first)
      (ContinuousMap.toLp 2 μ Real second) = ∫ point, (weight * (first * second)) point ∂μ := by
  change inner Real (l2VolumeMultiplier μ _ (ContinuousMap.toLp 2 μ Real first))
    (ContinuousMap.toLp 2 μ Real second) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2VolumeMultiplier_ae μ
      (ContinuousMap.linearIsometryBoundedOfCompact X Real Real weight)
      (ContinuousMap.toLp 2 μ Real first),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := Real) μ first,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := Real) μ second] with point hWeight hFirst hSecond
  simp only [hWeight, hFirst, hSecond, RCLike.inner_apply, conj_trivial,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply, ContinuousMap.mul_apply]
  ring

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D P0EFTJanusFiniteFrameC2MaxwellCurvature4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12FrameFreeMaxwellBilinear4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "base" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "μ" => intrinsicCanonicalLorentzVolumeMeasure period hPeriod
local notation "Smooth" => GlobalPairedAbelianPotentialSmooth period hPeriod
local notation "Gauge" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
local notation "Graph" => IntrinsicAbelianMaxwellLorenzGraph period hPeriod
local notation "C0" => C(Q period hPeriod, Real)
local instance : NormedAddCommGroup Gauge := inferInstance
local instance : NormedSpace Real Gauge := inferInstance
local instance : NormedSpace Real (GlobalPairedAbelianLorenzGraphHilbert period hPeriod (fun _ => base)) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianLorenzGraphHilbert period hPeriod (fun _ => base))).toNormedSpace
local instance : NormedSpace Real (IntrinsicAbelianCurvatureL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real (IntrinsicAbelianCurvatureL2 period hPeriod)).toNormedSpace
local instance : NormedSpace Real (IntrinsicAbelianMaxwellLorenzAmbient period hPeriod) := inferInstance
local instance graphNormedGroup : NormedAddCommGroup Graph := inferInstance
local instance : SeminormedAddCommGroup Graph := (graphNormedGroup period hPeriod).toSeminormedAddCommGroup
local instance graphNormedSpace : NormedSpace Real Graph :=
  Submodule.normedSpace (intrinsicAbelianMaxwellLorenzSubmodule period hPeriod)
local instance : Module Real Graph := (graphNormedSpace period hPeriod).toModule
local instance : NormedAddCommGroup (Graph →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Graph →L[Real] Real) := ContinuousLinearMap.toNormedSpace

private def curvatureFeature (index : IntrinsicAbelianCurvatureIndex period hPeriod) :
    Graph →L[Real] CanonicalPhysicalBulkL2 period hPeriod :=
  (PiLp.proj 2 (fun _ : IntrinsicAbelianCurvatureIndex period hPeriod =>
    CanonicalPhysicalBulkL2 period hPeriod) index).comp
      (intrinsicAbelianMaxwellLorenzCurvature period hPeriod)

private theorem curvatureFeature_smooth (potential : Smooth)
    (index : IntrinsicAbelianCurvatureIndex period hPeriod) :
    curvatureFeature period hPeriod index (intrinsicAbelianMaxwellLorenzSmooth period hPeriod potential) =
      ContinuousMap.toLp 2 μ Real
        (frameFreeMaxwellCurvatureCLM period hPeriod frame base index.2.1 index.2.2.1 index.2.2.2
          (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame (potential index.1))) := by
  change intrinsicAbelianCurvatureL2 period hPeriod potential index = _
  rw [intrinsicAbelianCurvatureL2_component, frameFreeMaxwellCurvatureCLM_apply]

private def nativeWeight (first second raisedFirst raisedSecond : Fin (finiteSmoothTangentFrame period hPeriod).count) : C0 :=
  finiteFrameCanonicalVolumeC0 period hPeriod frame base 0 *
    ((-(1 / 4 : Real)) •
      (finiteFrameInverseMetricC0Coefficient period hPeriod frame base first raisedFirst 0 *
        finiteFrameInverseMetricC0Coefficient period hPeriod frame base second raisedSecond 0))

def intrinsicAbelianMaxwellGraphSectorPairing (sector : Sector) : Graph →L[Real] Graph →L[Real] Real :=
  ∑ component : Fin 2, ∑ first : Fin (finiteSmoothTangentFrame period hPeriod).count,
    ∑ second : Fin (finiteSmoothTangentFrame period hPeriod).count,
    ∑ raisedFirst : Fin (finiteSmoothTangentFrame period hPeriod).count,
    ∑ raisedSecond : Fin (finiteSmoothTangentFrame period hPeriod).count,
      (weightedL2Pairing μ (nativeWeight period hPeriod first second raisedFirst raisedSecond)).bilinearComp
        (curvatureFeature period hPeriod (sector, component, first, second))
        (curvatureFeature period hPeriod (sector, component, raisedFirst, raisedSecond))

private theorem nativePairing_eq_sum (first second : Gauge) :
    frameFreeMaxwellBilinear period hPeriod frame base 0 first second =
      ∑ component : Fin 2, ∑ i : Fin (finiteSmoothTangentFrame period hPeriod).count,
        ∑ j : Fin (finiteSmoothTangentFrame period hPeriod).count,
        ∑ k : Fin (finiteSmoothTangentFrame period hPeriod).count,
        ∑ l : Fin (finiteSmoothTangentFrame period hPeriod).count,
          ∫ point, (nativeWeight period hPeriod i j k l *
            (frameFreeMaxwellCurvatureCLM period hPeriod frame base component i j first *
              frameFreeMaxwellCurvatureCLM period hPeriod frame base component k l second)) point ∂μ := by
  have hContraction : frameFreeMaxwellContractionBilinear period hPeriod frame base 0 first second =
      ∑ component : Fin 2, ∑ i : Fin (finiteSmoothTangentFrame period hPeriod).count,
        ∑ j : Fin (finiteSmoothTangentFrame period hPeriod).count,
        ∑ k : Fin (finiteSmoothTangentFrame period hPeriod).count,
        ∑ l : Fin (finiteSmoothTangentFrame period hPeriod).count,
          (finiteFrameInverseMetricC0Coefficient period hPeriod frame base i k 0 *
            finiteFrameInverseMetricC0Coefficient period hPeriod frame base j l 0) *
            (frameFreeMaxwellCurvatureCLM period hPeriod frame base component i j first *
              frameFreeMaxwellCurvatureCLM period hPeriod frame base component k l second) := by
    simp only [frameFreeMaxwellContractionBilinear, sum_apply]
    rfl
  change finiteFrameBRSTCanonicalIntegralCLM period hPeriod
    (finiteFrameCanonicalVolumeC0 period hPeriod frame base 0 *
      ((-(1 / 4 : Real)) • frameFreeMaxwellContractionBilinear period hPeriod frame base 0 first second)) = _
  rw [hContraction]
  simp only [Finset.smul_sum, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro component _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [finiteFrameBRSTCanonicalIntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with point
  simp only [nativeWeight, ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem intrinsicAbelianMaxwellGraphSectorPairing_smooth (sector : Sector) (first second : Smooth) :
    intrinsicAbelianMaxwellGraphSectorPairing period hPeriod sector
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first)
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second) =
    frameFreeMaxwellBilinear period hPeriod frame base 0
      (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame (first sector))
      (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame (second sector)) := by
  rw [nativePairing_eq_sum]
  simp only [intrinsicAbelianMaxwellGraphSectorPairing, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, curvatureFeature_smooth, weightedL2Pairing_continuous]

def intrinsicAbelianMaxwellGraphPairing (scale : Sector → Real) : Graph →L[Real] Graph →L[Real] Real :=
  ∑ sector, scale sector • intrinsicAbelianMaxwellGraphSectorPairing period hPeriod sector

theorem intrinsicAbelianMaxwellGraphPairing_smooth (scale : Sector → Real) (first second : Smooth) :
    intrinsicAbelianMaxwellGraphPairing period hPeriod scale
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first)
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second) =
      ∑ sector, scale sector * frameFreeMaxwellBilinear period hPeriod frame base 0
        (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame (first sector))
        (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame (second sector)) := by
  simp only [intrinsicAbelianMaxwellGraphPairing, sum_apply, smul_apply,
    smul_eq_mul, intrinsicAbelianMaxwellGraphSectorPairing_smooth]

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphPairing4D
