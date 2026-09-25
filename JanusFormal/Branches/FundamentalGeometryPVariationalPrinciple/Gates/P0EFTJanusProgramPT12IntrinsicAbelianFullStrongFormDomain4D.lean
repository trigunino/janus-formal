import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongMaximal4D

/-! Exact physical representability criterion for the completed native Hessian. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongFormDomain4D
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

open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D

open P0EFTJanusProgramPT12IntrinsicAbelianFullStrongMaximal4D

variable (couplings : GlobalCandidateAActionCouplings)
local notation "inc" => intrinsicAbelianFullL2Smooth period hPeriod
local notation "action" => intrinsicAbelianFullStrongSmooth period hPeriod couplings
local notation "readout" => intrinsicAbelianFullGraphToL2 period hPeriod
local notation "riesz" => intrinsicAbelianFullGraphRiesz period hPeriod couplings
local notation "smooth" => intrinsicAbelianFullSmooth period hPeriod
local notation "maximal" => intrinsicAbelianFullStrongMaximal period hPeriod couplings

private theorem smooth_test_riesz (point : FullGraph) (test : State) :
    inner Real (action test) (readout point) = inner Real (riesz point) (smooth test) :=
  (intrinsicAbelianFullStrongSmooth_graph_pairing period hPeriod couplings test point).trans
    ((intrinsicAbelianFullGraphHessian_comm period hPeriod couplings (smooth test) point).trans
      (InnerProductSpace.continuousLinearMapOfBilin_apply _ point (smooth test)).symm)

private theorem readout_adjoint_smooth (value : Full) (test : State) :
    inner Real ((readout).adjoint value) (smooth test) = inner Real (inc test) value :=
  (ContinuousLinearMap.adjoint_inner_left readout (smooth test) value).trans
    ((congrArg (inner Real value) (intrinsicAbelianFullGraphToL2_smooth period hPeriod test)).trans
      (real_inner_comm _ _))

/-- On the faithful form domain, the maximal physical graph is exactly adjoint transport. -/
theorem intrinsicAbelianFullStrongMaximal_graph_iff_adjoint_transport (point : FullGraph) (value : Full) :
    (readout point, value) ∈ (maximal).graph ↔ (readout).adjoint value = riesz point := by
  refine (intrinsicAbelianFullStrongMaximal_graph_iff period hPeriod couplings (readout point) value).trans ?_
  constructor
  · intro h
    have hAll : (fun test : FullGraph => inner Real ((readout).adjoint value) test) =
        (fun test : FullGraph => inner Real (riesz point) test) := by
      apply (intrinsicAbelianFullSmooth_denseRange period hPeriod).equalizer
      · fun_prop
      · fun_prop
      · funext test
        exact (readout_adjoint_smooth period hPeriod value test).trans
          ((h test).symm.trans (smooth_test_riesz period hPeriod couplings point test))
    exact ext_inner_right Real (congrFun hAll)
  · intro h test
    exact (smooth_test_riesz period hPeriod couplings point test).trans
      ((congrArg (fun v : FullGraph => inner Real v (smooth test)) h).symm.trans
        (readout_adjoint_smooth period hPeriod value test))

/-- Domain membership is physical representability of the graph Riesz, not an assumed bound. -/
theorem intrinsicAbelianFullStrongMaximal_mem_domain_iff (point : FullGraph) :
    readout point ∈ (maximal).domain ↔ riesz point ∈ (readout).adjoint.range := by
  exact LinearPMap.mem_domain_iff.trans (exists_congr (fun value =>
    intrinsicAbelianFullStrongMaximal_graph_iff_adjoint_transport period hPeriod couplings point value))

/-- Every physically represented graph vector pairs with every completed graph test. -/
theorem intrinsicAbelianFullStrongMaximal_graph_pairing (point test : FullGraph) (value : Full)
    (h : (readout point, value) ∈ (maximal).graph) :
    inner Real value (readout test) = intrinsicAbelianFullGraphHessian period hPeriod couplings point test :=
  (ContinuousLinearMap.adjoint_inner_left readout test value).symm.trans
    ((congrArg (fun v : FullGraph => inner Real v test)
      ((intrinsicAbelianFullStrongMaximal_graph_iff_adjoint_transport period hPeriod couplings point value).mp h)).trans
      (InnerProductSpace.continuousLinearMapOfBilin_apply _ point test))

/-- The graph Riesz kernel agrees with the weak physical kernel inside the form domain. -/
theorem intrinsicAbelianFullStrongMaximal_zero_iff (point : FullGraph) :
    (readout point, 0) ∈ (maximal).graph ↔ riesz point = 0 := by
  refine (intrinsicAbelianFullStrongMaximal_graph_iff_adjoint_transport period hPeriod couplings point 0).trans ?_
  exact (congrArg (fun value : FullGraph => value = riesz point) (readout).adjoint.map_zero).to_iff.trans eq_comm

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongFormDomain4D
