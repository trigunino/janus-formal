import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureGraphBridge4D

/-! Transport between the native graph Hessian and the physical L² strong Jacobi. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongGraphBridge4D
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

private def lpPairCLM {S E F : Type*}
    [NormedAddCommGroup S] [NormedSpace Real S]
    [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F] [NormedSpace Real F]
    (first : S →L[Real] E) (second : S →L[Real] F) : S →L[Real] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 Real E F).symm.toContinuousLinearMap.comp (first.prod second)

private def ghostProjection : BRST →L[Real] GaugeL2 :=
  (WithLp.fstL 2 Real GaugeL2 GaugeL2).comp
    (globalPairedAbelianOffShellTail3Projection period hPeriod (fun _ => base))

/-- Canonical physical field readout of the complete native Maxwell–BRST graph. -/
def intrinsicAbelianFullGraphToL2 : FullGraph →L[Real] Full :=
  lpPairCLM
    (lpPairCLM
      ((intrinsicAbelianMaxwellToPotentialL2 period hPeriod).comp (intrinsicAbelianFullMaxwell period hPeriod))
      ((globalPairedAbelianOffShellBProjection period hPeriod (fun _ => base)).comp (intrinsicAbelianFullBRST period hPeriod)))
    (lpPairCLM
      ((globalPairedAbelianOffShellAntighostProjection period hPeriod (fun _ => base)).comp (intrinsicAbelianFullBRST period hPeriod))
      ((ghostProjection period hPeriod).comp (intrinsicAbelianFullBRST period hPeriod)))

theorem intrinsicAbelianFullGraphToL2_smooth (state : State) :
    intrinsicAbelianFullGraphToL2 period hPeriod (intrinsicAbelianFullSmooth period hPeriod state) =
      intrinsicAbelianFullL2Smooth period hPeriod state := rfl

theorem intrinsicAbelianFullGraphToL2_denseRange : DenseRange (intrinsicAbelianFullGraphToL2 period hPeriod) :=
  (intrinsicAbelianFullL2Smooth_denseRange period hPeriod).mono (by
    rintro _ ⟨state, rfl⟩
    exact ⟨intrinsicAbelianFullSmooth period hPeriod state, intrinsicAbelianFullGraphToL2_smooth period hPeriod state⟩)

variable (couplings : GlobalCandidateAActionCouplings)
attribute [local irreducible] intrinsicAbelianFullStrongSmooth intrinsicAbelianFullL2Smooth

/-- The same-action pairing holds against every completed graph test. -/
theorem intrinsicAbelianFullStrongSmooth_graph_pairing (state : State) (test : FullGraph) :
    inner Real (intrinsicAbelianFullStrongSmooth period hPeriod couplings state)
      (intrinsicAbelianFullGraphToL2 period hPeriod test) =
      intrinsicAbelianFullGraphHessian period hPeriod couplings
        (intrinsicAbelianFullSmooth period hPeriod state) test := by
  have hAll : (fun test : FullGraph => inner Real (intrinsicAbelianFullStrongSmooth period hPeriod couplings state)
      (intrinsicAbelianFullGraphToL2 period hPeriod test)) =
      (fun test : FullGraph => intrinsicAbelianFullGraphHessian period hPeriod couplings
        (intrinsicAbelianFullSmooth period hPeriod state) test) := by
    apply (intrinsicAbelianFullSmooth_denseRange period hPeriod).equalizer
    · fun_prop
    · exact (intrinsicAbelianFullGraphHessian period hPeriod couplings
        (intrinsicAbelianFullSmooth period hPeriod state)).continuous
    · funext field
      exact (congrArg (inner Real (intrinsicAbelianFullStrongSmooth period hPeriod couplings state))
        (intrinsicAbelianFullGraphToL2_smooth period hPeriod field)).trans
          (intrinsicAbelianFullStrongSmooth_eq_graphHessian period hPeriod couplings state field)
  exact congrFun hAll test

/-- The native graph Riesz is the adjoint transport of the physical strong column. -/
theorem intrinsicAbelianFullStrongSmooth_adjoint_transport (state : State) :
    (intrinsicAbelianFullGraphToL2 period hPeriod).adjoint
      (intrinsicAbelianFullStrongSmooth period hPeriod couplings state) =
      intrinsicAbelianFullGraphRiesz period hPeriod couplings (intrinsicAbelianFullSmooth period hPeriod state) := by
  apply ext_inner_right Real
  intro test
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (intrinsicAbelianFullStrongSmooth_graph_pairing period hPeriod couplings state test).trans
    (InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _).symm

theorem intrinsicAbelianFullStrongMinimal_graph_pairing (state : State) (test : FullGraph) :
    inner Real (intrinsicAbelianFullStrongMinimal period hPeriod couplings
      ⟨intrinsicAbelianFullL2Smooth period hPeriod state,
        intrinsicAbelianFullStrongMinimal_smooth_mem period hPeriod couplings state⟩)
      (intrinsicAbelianFullGraphToL2 period hPeriod test) =
      intrinsicAbelianFullGraphHessian period hPeriod couplings
        (intrinsicAbelianFullSmooth period hPeriod state) test :=
  (congrArg (fun value : Full => inner Real value (intrinsicAbelianFullGraphToL2 period hPeriod test))
    (intrinsicAbelianFullStrongMinimal_smooth_apply period hPeriod couplings state)).trans
      (intrinsicAbelianFullStrongSmooth_graph_pairing period hPeriod couplings state test)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongGraphBridge4D
