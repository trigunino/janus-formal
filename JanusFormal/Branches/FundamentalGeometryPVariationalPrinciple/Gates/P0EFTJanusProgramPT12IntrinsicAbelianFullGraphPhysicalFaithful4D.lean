import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongGraphBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullGraphFaithful4D

/-! Faithful physical readout of the completed native Maxwell-BRST graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullGraphPhysicalFaithful4D
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

open P0EFTJanusProgramPT12IntrinsicAbelianFullL2Core4D
open P0EFTJanusProgramPT12IntrinsicAbelianLorenzAdjoint4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongSmooth4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullGraph4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullGraphRiesz4D
open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12FrameFreeFPCanonicalPairing4D
open P0EFTJanusProgramPGlobalCovariantAction4D
local notation "Full" => IntrinsicAbelianFullL2 period hPeriod
local instance fullGroup : NormedAddCommGroup Full := inferInstance
local instance : SeminormedAddCommGroup Full := (fullGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Full := inferInstance
local instance : InnerProductSpace Real Full := inferInstance
local notation "Maxwell" => IntrinsicAbelianMaxwellLorenzGraph period hPeriod
local instance maxwellGroup : NormedAddCommGroup Maxwell := inferInstance
local instance : SeminormedAddCommGroup Maxwell := (maxwellGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real Maxwell := graphInnerProductSpace period hPeriod
local instance : NormedSpace Real Maxwell := inferInstance
local notation "FullGraph" => IntrinsicAbelianFullGraph period hPeriod
local instance graphGroup : NormedAddCommGroup FullGraph := inferInstance
local instance : SeminormedAddCommGroup FullGraph := (graphGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real FullGraph := intrinsicAbelianFullGraphInnerProductSpace period hPeriod
local instance : CompleteSpace FullGraph := intrinsicAbelianFullGraph_complete period hPeriod
local instance : NormedSpace Real FullGraph := (intrinsicAbelianFullGraphInnerProductSpace period hPeriod).toNormedSpace

open P0EFTJanusProgramPT12IntrinsicAbelianFullStrongSmooth4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullStrongClosed4D
open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureGraphBridge4D
local notation "BRST" => GlobalPairedAbelianOffShellGraphHilbert period hPeriod (fun _ => base)
local instance brstGroup : NormedAddCommGroup BRST := inferInstance
local instance : SeminormedAddCommGroup BRST := (brstGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real BRST := inferInstance

open P0EFTJanusProgramPT12IntrinsicAbelianFullStrongGraphBridge4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullGraphFaithful4D

/-- Lorenz remains the weak derivative of the physical potential after completion. -/
theorem intrinsicAbelianFullGraph_weak_lorenz (point : FullGraph) (test : GaugeSmooth) :
    inner Real (globalPairedAbelianOffShellLorenzProjection period hPeriod (fun _ => base)
      (intrinsicAbelianFullBRST period hPeriod point)) (globalPairedGaugeLieL2LinearMap period hPeriod test) =
    inner Real (intrinsicAbelianFullGraphToL2 period hPeriod point).fst.fst
      (intrinsicAbelianLorenzAdjointSmooth period hPeriod test) := by
  have hAll : (fun point : FullGraph => inner Real
      (globalPairedAbelianOffShellLorenzProjection period hPeriod (fun _ => base)
        (intrinsicAbelianFullBRST period hPeriod point)) (globalPairedGaugeLieL2LinearMap period hPeriod test)) =
      (fun point : FullGraph => inner Real (intrinsicAbelianFullGraphToL2 period hPeriod point).fst.fst
        (intrinsicAbelianLorenzAdjointSmooth period hPeriod test)) := by
    apply (intrinsicAbelianFullSmooth_denseRange period hPeriod).equalizer
    · fun_prop
    · fun_prop
    · funext state
      exact intrinsicAbelianLorenzAdjointSmooth_pairing period hPeriod state.potential test
  exact congrFun hAll point

/-- The completed FP feature is determined by the physical ghost through its native adjoint. -/
theorem intrinsicAbelianFullGraph_weak_fp (point : FullGraph) (test : GaugeSmooth) :
    inner Real (globalPairedAbelianOffShellFPProjection period hPeriod (fun _ => base)
      (intrinsicAbelianFullBRST period hPeriod point)) (globalPairedGaugeLieL2LinearMap period hPeriod test) =
    inner Real (intrinsicAbelianFullGraphToL2 period hPeriod point).snd.snd
      (pairedFPCanonicalAdjointL2 period hPeriod (fun _ => base) test) := by
  have hAll : (fun point : FullGraph => inner Real
      (globalPairedAbelianOffShellFPProjection period hPeriod (fun _ => base)
        (intrinsicAbelianFullBRST period hPeriod point)) (globalPairedGaugeLieL2LinearMap period hPeriod test)) =
      (fun point : FullGraph => inner Real (intrinsicAbelianFullGraphToL2 period hPeriod point).snd.snd
        (pairedFPCanonicalAdjointL2 period hPeriod (fun _ => base) test)) := by
    apply (intrinsicAbelianFullSmooth_denseRange period hPeriod).equalizer
    · fun_prop
    · fun_prop
    · funext state
      exact frameFreePairedFPCanonicalAdjoint_pairing period hPeriod (fun _ => base)
        (fun sector => (state.nonminimal sector).ghost.field) test
  exact congrFun hAll point

private theorem gauge_ext {first second : GaugeL2}
    (h : ∀ test : GaugeSmooth, inner Real first (globalPairedGaugeLieL2LinearMap period hPeriod test) =
      inner Real second (globalPairedGaugeLieL2LinearMap period hPeriod test)) : first = second := by
  have hAll : (fun test : GaugeL2 => inner Real first test) = (fun test : GaugeL2 => inner Real second test) := by
    apply (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod).equalizer
    · fun_prop
    · fun_prop
    · funext test
      exact h test
  exact ext_inner_right Real (congrFun hAll)

/-- No vertical Lorenz, curvature, or FP mode survives the physical L² readout. -/
theorem intrinsicAbelianFullGraphToL2_injective : Function.Injective (intrinsicAbelianFullGraphToL2 period hPeriod) := by
  intro first second h
  have hLorenz : globalPairedAbelianOffShellLorenzProjection period hPeriod (fun _ => base)
      (intrinsicAbelianFullBRST period hPeriod first) =
      globalPairedAbelianOffShellLorenzProjection period hPeriod (fun _ => base)
        (intrinsicAbelianFullBRST period hPeriod second) := by
    apply gauge_ext period hPeriod
    intro test
    exact (intrinsicAbelianFullGraph_weak_lorenz period hPeriod first test).trans
      ((congrArg (fun value : Full => inner Real value.fst.fst
        (intrinsicAbelianLorenzAdjointSmooth period hPeriod test)) h).trans
        (intrinsicAbelianFullGraph_weak_lorenz period hPeriod second test).symm)
  have hFP : globalPairedAbelianOffShellFPProjection period hPeriod (fun _ => base)
      (intrinsicAbelianFullBRST period hPeriod first) =
      globalPairedAbelianOffShellFPProjection period hPeriod (fun _ => base)
        (intrinsicAbelianFullBRST period hPeriod second) := by
    apply gauge_ext period hPeriod
    intro test
    exact (intrinsicAbelianFullGraph_weak_fp period hPeriod first test).trans
      ((congrArg (fun value : Full => inner Real value.snd.snd
        (pairedFPCanonicalAdjointL2 period hPeriod (fun _ => base) test)) h).trans
        (intrinsicAbelianFullGraph_weak_fp period hPeriod second test).symm)
  have hPotential := congrArg (fun value : Full => value.fst.fst.val) h
  have hB := congrArg (fun value : Full => value.fst.snd) h
  have hAnti := congrArg (fun value : Full => value.snd.fst) h
  have hGhost := congrArg (fun value : Full => value.snd.snd) h
  apply intrinsicAbelianFullBRST_injective period hPeriod
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · have hFirst := congrArg (fun value : GlobalPairedAbelianLorenzGraphAmbient period hPeriod => value.fst)
        (intrinsicAbelianFullLorenz_agreement period hPeriod first)
      have hSecond := congrArg (fun value : GlobalPairedAbelianLorenzGraphAmbient period hPeriod => value.fst)
        (intrinsicAbelianFullLorenz_agreement period hPeriod second)
      exact hFirst.symm.trans (hPotential.trans hSecond)
    · exact hLorenz
  · apply WithLp.ofLp_injective 2
    refine Prod.ext ?_ ?_
    · exact hB
    · apply WithLp.ofLp_injective 2
      refine Prod.ext ?_ ?_
      · exact hAnti
      · apply WithLp.ofLp_injective 2
        refine Prod.ext ?_ ?_
        · exact hGhost
        · exact hFP

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullGraphPhysicalFaithful4D
