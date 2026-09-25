import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkPairedAbelianHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

/-! Exact agreement of the native bulk Abelian BRST Hessian with the existing
off-shell graph form on the genuine paired smooth core. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianGraphPairing4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFrameCovectorC2Projection4D P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusProgramPT12FrameFreeAbelianOperatorFamily4D
open P0EFTJanusProgramPT12FrameFreeAbelianBilinearFamily4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothAbelianBRSTCore4D
open P0EFTJanusProgramPT12IntrinsicBulkPairedAbelianHessian4D
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : ChartedSpace ThroatCoverModel (Throat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (Throat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (Throat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Throat period hPeriod) := borel _
local instance : BorelSpace (Throat period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert := InnerProductSpace.complexToReal

private theorem mixed_density_apply
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric)
    (first second : FrameFreeAbelianBRSTFields period hPeriod frame) :
    frameFreeAbelianBRSTBilinearDensity period hPeriod frame metric variation first second =
      ∑ component : Fin 2,
        (finiteFrameAbelianScalarC2Readout period hPeriod component first.2.1 *
            finiteFrameC2AbelianLorenzComponentExpression period hPeriod frame metric variation
              (finiteFrameGaugeC2Projection period hPeriod frame metric second.1) component -
          (1 / 2 : Real) • (finiteFrameAbelianScalarC2Readout period hPeriod component first.2.1 *
            finiteFrameAbelianScalarC2Readout period hPeriod component second.2.1) +
          finiteFrameAbelianScalarC2Readout period hPeriod component first.2.2.1 *
            finiteFrameC2AbelianFPComponentExpression period hPeriod frame metric variation second.2.2.2 component) := by
  simp only [frameFreeAbelianBRSTBilinearDensity, sum_apply, _root_.add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    frameFreeAbelianLorenzOperatorFamily_apply, frameFreeAbelianFPOperatorFamily_apply]
  rfl

private theorem mixed_density_smooth
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPotential secondPotential : SmoothAbelianGaugePotential period hPeriod)
    (first second : GlobalAbelianNonminimalFields period hPeriod) (point : Q period hPeriod) :
    frameFreeAbelianBRSTBilinearDensity period hPeriod frame metric 0
        (finiteFrameSmoothAbelianBRSTCore period hPeriod frame metric 0 firstPotential first).2
        (finiteFrameSmoothAbelianBRSTCore period hPeriod frame metric 0 secondPotential second).2 point =
      globalGaugeLiePairingAt period hPeriod first.nakanishiLautrup.field
        (globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric secondPotential) point -
      (1 / 2 : Real) * globalGaugeLiePairingAt period hPeriod first.nakanishiLautrup.field
        second.nakanishiLautrup.field point +
      globalGaugeLiePairingAt period hPeriod first.antighost.field
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod metric second.ghost.field) point := by
  have hZero := (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric).map_zero
  have hDomain : smoothToGeneralMetricRelativeC2Core period hPeriod frame metric 0 ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame metric := by
    rw [hZero]
    exact zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame metric
  have hMetric : metric.tensor = metric.tensor + 0 := (add_zero _).symm
  have hReadout (field : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) :
      smoothToCanonicalPhysicalContinuousScalar period hPeriod (ghostComponent period hPeriod field component) point =
        field point component := rfl
  simp only [mixed_density_apply, finiteFrameSmoothAbelianBRSTCore,
    finiteFrameSmoothAbelianGaugeC2Coefficients_projected, finiteFrameAbelianScalarC2Readout_smooth, ← hZero,
    finiteFrameC2AbelianLorenzComponentExpression_smooth period hPeriod frame metric 0 metric hMetric hDomain,
    finiteFrameC2AbelianFPComponentExpression_smooth period hPeriod frame metric 0 metric hMetric hDomain,
    ContinuousMap.sum_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply,
    ContinuousMap.smul_apply, smul_eq_mul, hReadout, globalGaugeLiePairingAt,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "metric" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)

theorem intrinsicBulkPairedAbelianBilinear_smooth_eq_mixed
    (first second : GlobalPairedAbelianBRSTState period hPeriod) :
    intrinsicBulkPairedAbelianBilinear period hPeriod
        (intrinsicBulkSmoothPairedAbelianFields period hPeriod first)
        (intrinsicBulkSmoothPairedAbelianFields period hPeriod second) =
      globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod (fun _ => metric) first second
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  change finiteFrameBRSTCanonicalIntegralCLM period hPeriod
      (frameFreeAbelianBRSTBilinearDensity period hPeriod frame metric 0
        (finiteFrameSmoothAbelianBRSTCore period hPeriod frame metric 0
          (first.potential .plus) (first.nonminimal .plus)).2
        (finiteFrameSmoothAbelianBRSTCore period hPeriod frame metric 0
          (second.potential .plus) (second.nonminimal .plus)).2) +
    finiteFrameBRSTCanonicalIntegralCLM period hPeriod
      (frameFreeAbelianBRSTBilinearDensity period hPeriod frame metric 0
        (finiteFrameSmoothAbelianBRSTCore period hPeriod frame metric 0
          (first.potential .minus) (first.nonminimal .minus)).2
        (finiteFrameSmoothAbelianBRSTCore period hPeriod frame metric 0
          (second.potential .minus) (second.nonminimal .minus)).2) = _
  rw [← map_add, finiteFrameBRSTCanonicalIntegralCLM_apply]
  unfold globalPairedAbelianGaugeFermionBRSTMixedAction
  apply integral_congr_ae
  filter_upwards [] with point
  rw [ContinuousMap.add_apply, mixed_density_smooth, mixed_density_smooth]
  have hSectors : (Finset.univ : Finset Sector) = {.plus, .minus} := by decide
  simp only [globalPairedAbelianGaugeFermionBRSTMixedDensity, hSectors, Finset.sum_insert,
    Finset.sum_singleton, Finset.mem_singleton, reduceCtorEq, not_false_eq_true]

variable (couplings : GlobalCandidateAActionCouplings)
local instance coreNormedAddCommGroup : NormedAddCommGroup (IntrinsicBulkCore period hPeriod couplings) := inferInstance
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings

theorem intrinsicBulkBRSTHessian_smoothAbelian_eq_offShellGraph
    (first second : GlobalPairedAbelianBRSTState period hPeriod) :
    intrinsicBulkBRSTHessian period hPeriod couplings
        (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings first)
        (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings second) =
      globalPairedAbelianOffShellHessian period hPeriod (fun _ => metric)
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (fun _ => metric) first)
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (fun _ => metric) second) := by
  have hInput := congrArg₂
    (fun x y : IntrinsicBulkCore period hPeriod couplings => intrinsicBulkBRSTHessian period hPeriod couplings x y)
    (intrinsicBulkPairedAbelianInsertion_smooth period hPeriod couplings first).symm
    (intrinsicBulkPairedAbelianInsertion_smooth period hPeriod couplings second).symm
  have hPair := intrinsicBulkBRSTHessian_pairedAbelian period hPeriod couplings
    (intrinsicBulkSmoothPairedAbelianFields period hPeriod first)
    (intrinsicBulkSmoothPairedAbelianFields period hPeriod second)
  have hMixed := congrArg₂ (fun x y : Real => x + y)
    (intrinsicBulkPairedAbelianBilinear_smooth_eq_mixed period hPeriod first second)
    (intrinsicBulkPairedAbelianBilinear_smooth_eq_mixed period hPeriod second first)
  have hGraph := (globalPairedAbelianOffShellHessian_smooth_eq_BRST period hPeriod
    (fun _ => metric) first second).trans
      (globalPairedAbelianGaugeFermionBRSTPolarizationAction_eq_mixed period hPeriod
        (fun _ => metric) first second (intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
  exact hInput.trans (hPair.trans (hMixed.trans hGraph.symm))

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianGraphPairing4D
