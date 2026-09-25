import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianLorenzAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D

/-! Faithful physical L² carrier of the native paired Maxwell and BRST fields. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullL2Core4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusFiniteFrameLorenzCovariantTrace4D P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameC2MaxwellCurvature4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12FrameFreeMaxwellBilinear4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
open P0EFTJanusProgramPT12IntrinsicAbelianPotentialL2Core4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D
open P0EFTJanusProgramPT12FrameFreeMaxwellCurvaturePairing4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "base" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "Smooth" => GlobalPairedAbelianPotentialSmooth period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "Potential" => IntrinsicAbelianPotentialL2Core period hPeriod
local notation "Curvature" => IntrinsicAbelianCurvatureL2 period hPeriod
local instance potentialGroup : NormedAddCommGroup Potential := inferInstance
local instance : SeminormedAddCommGroup Potential := (potentialGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Potential := inferInstance
local instance curvatureGroup : NormedAddCommGroup Curvature := inferInstance
local instance : SeminormedAddCommGroup Curvature := (curvatureGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Curvature := inferInstance

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureL2Graph4D

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureClosed4D
local notation "H" => CanonicalPhysicalBulkL2 period hPeriod
local notation "Index" => IntrinsicAbelianCurvatureIndex period hPeriod
local instance : InnerProductSpace Real Potential :=
  Submodule.innerProductSpace (𝕜 := Real) (intrinsicAbelianPotentialL2Submodule period hPeriod)
local instance : InnerProductSpace Real Curvature := inferInstance
local instance : CompleteSpace Curvature := inferInstance

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureAdjointColumns4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusProgramPT12IntrinsicAbelianLorenzSmoothAdjoint4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
local notation "GaugeSmooth" => GlobalPairedGaugeLieSmooth period hPeriod
local notation "GaugeL2" => GlobalPairedGaugeLieL2 period hPeriod
local instance : NormedSpace Real GaugeL2 := inferInstance

open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D
local notation "State" => GlobalPairedAbelianBRSTState period hPeriod
local instance gaugeGroup : NormedAddCommGroup GaugeL2 := inferInstance
local instance : SeminormedAddCommGroup GaugeL2 := (gaugeGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real GaugeL2 := inferInstance

abbrev IntrinsicAbelianNonminimalL2 := WithLp 2 (Potential × GaugeL2)
abbrev IntrinsicAbelianGhostL2 := WithLp 2 (GaugeL2 × GaugeL2)
abbrev IntrinsicAbelianFullL2 := WithLp 2
  (IntrinsicAbelianNonminimalL2 period hPeriod × IntrinsicAbelianGhostL2 period hPeriod)
local notation "Full" => IntrinsicAbelianFullL2 period hPeriod
local instance fullGroup : NormedAddCommGroup Full := inferInstance
local instance : SeminormedAddCommGroup Full := (fullGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Full := inferInstance
local instance : InnerProductSpace Real Full := inferInstance

instance intrinsicAbelianFullL2_complete : CompleteSpace Full := inferInstance

/-- All four original slots are retained; no derivative is included in the potential norm. -/
def intrinsicAbelianFullL2Smooth : State →ₗ[Real] Full where
  toFun state := WithLp.toLp 2
    (WithLp.toLp 2 (intrinsicAbelianPotentialL2Smooth period hPeriod state.potential,
      globalPairedGaugeLieL2LinearMap period hPeriod (fun sector => (state.nonminimal sector).nakanishiLautrup.field)),
     WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector => (state.nonminimal sector).antighost.field),
      globalPairedGaugeLieL2LinearMap period hPeriod (fun sector => (state.nonminimal sector).ghost.field)))
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      exact Prod.ext ((intrinsicAbelianPotentialL2Smooth period hPeriod).map_add _ _)
        ((globalPairedGaugeLieL2LinearMap period hPeriod).map_add _ _)
    · apply WithLp.ofLp_injective 2
      exact Prod.ext ((globalPairedGaugeLieL2LinearMap period hPeriod).map_add _ _)
        ((globalPairedGaugeLieL2LinearMap period hPeriod).map_add _ _)
  map_smul' scalar state := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      exact Prod.ext ((intrinsicAbelianPotentialL2Smooth period hPeriod).map_smul scalar _)
        ((globalPairedGaugeLieL2LinearMap period hPeriod).map_smul scalar _)
    · apply WithLp.ofLp_injective 2
      exact Prod.ext ((globalPairedGaugeLieL2LinearMap period hPeriod).map_smul scalar _)
        ((globalPairedGaugeLieL2LinearMap period hPeriod).map_smul scalar _)

theorem intrinsicAbelianFullL2Smooth_injective : Function.Injective (intrinsicAbelianFullL2Smooth period hPeriod) := by
  intro first second h
  have hP := intrinsicAbelianPotentialL2Smooth_injective period hPeriod
    (congrArg (fun x : Full => x.fst.fst) h)
  have hB := globalPairedGaugeLieL2LinearMap_injective period hPeriod (congrArg (fun x : Full => x.fst.snd) h)
  have hA := globalPairedGaugeLieL2LinearMap_injective period hPeriod (congrArg (fun x : Full => x.snd.fst) h)
  have hC := globalPairedGaugeLieL2LinearMap_injective period hPeriod (congrArg (fun x : Full => x.snd.snd) h)
  apply GlobalPairedAbelianBRSTState.ext hP
  funext sector
  exact GlobalAbelianNonminimalFields.ext
    (GlobalAbelianGhostField.ext (congrFun hC sector))
    (GlobalAbelianAntighostField.ext (congrFun hA sector))
    (GlobalAbelianNakanishiLautrupField.ext (congrFun hB sector))

private theorem dense_withLp_pair {X Y P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [NormedAddCommGroup Q] [NormedSpace Real Q]
    {f : X → P} {g : Y → Q} (hf : DenseRange f) (hg : DenseRange g) :
    DenseRange (fun pair : X × Y => WithLp.toLp 2 (f pair.1, g pair.2)) :=
  (WithLp.prodContinuousLinearEquiv 2 Real P Q).symm.surjective.denseRange.comp
    (hf.prodMap hg) (WithLp.prodContinuousLinearEquiv 2 Real P Q).symm.continuous

theorem intrinsicAbelianFullL2Smooth_denseRange : DenseRange (intrinsicAbelianFullL2Smooth period hPeriod) := by
  have h := dense_withLp_pair
    (dense_withLp_pair (intrinsicAbelianPotentialL2Smooth_denseRange period hPeriod)
      (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod))
    (dense_withLp_pair (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod)
      (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod))
  refine Dense.mono ?_ h
  rintro _ ⟨fields, rfl⟩
  exact ⟨⟨fields.1.1, fun sector => ⟨⟨fields.2.2 sector⟩, ⟨fields.2.1 sector⟩, ⟨fields.1.2 sector⟩⟩⟩, rfl⟩

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullL2Core4D
