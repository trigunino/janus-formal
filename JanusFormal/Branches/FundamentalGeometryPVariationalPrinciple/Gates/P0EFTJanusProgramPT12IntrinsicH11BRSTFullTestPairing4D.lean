import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicH11BRSTStrongPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkDiffeomorphismColumnProjection4D

/-! H11-source BRST pairings with full bulk tests and smooth diagonal readout.
The remaining bulk components are unrestricted. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicH11BRSTFullTestPairing4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothBRSTCore4D P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismBilinearFamily4D
open P0EFTJanusProgramPT12IntrinsicBulkPairedDiffeomorphismHessian4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
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
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12FrameFreeH11BRSTStrongSmooth4D
open P0EFTJanusProgramPT12FrameFreeH11BRSTStrongClosed4D
open P0EFTJanusProgramPT12IntrinsicBulkDiffeomorphismGraphPairing4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTColumns4D
open P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusReciprocalBimetricPotential
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "metric" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "State" => GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod
local notation "Source" => DiffeomorphismL2 period hPeriod metric
local notation "Ambient" => DiffeomorphismL2Ambient period hPeriod
local instance ambientGroup : NormedAddCommGroup Ambient := inferInstance
local instance : SeminormedAddCommGroup Ambient := (ambientGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Ambient := inferInstance
local instance : InnerProductSpace Real Ambient := inferInstance
local instance sourceGroup : NormedAddCommGroup Source := inferInstance
local instance : SeminormedAddCommGroup Source := (sourceGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Source := Submodule.normedSpace (diffeomorphismL2Space period hPeriod metric)
local instance : InnerProductSpace Real Source := Submodule.innerProductSpace (𝕜 := Real) _
local notation "smooth" => diffeomorphismL2Smooth period hPeriod metric
variable (couplings : GlobalCandidateAActionCouplings)
local instance : NormedAddCommGroup (IntrinsicBulkCore period hPeriod couplings) := inferInstance
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings
local notation "strong" => frameFreeH11BRSTStrongSmooth period hPeriod metric couplings
local notation "minimal" => frameFreeH11BRSTStrongMinimal period hPeriod metric couplings

open P0EFTJanusProgramPT12IntrinsicH11BRSTStrongPairing4D
open P0EFTJanusProgramPT12IntrinsicBulkGlobalBRSTHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkDiffeomorphismColumnProjection4D
local notation "Bulk" => IntrinsicBulkCore period hPeriod couplings
local notation "insert" => intrinsicBulkPairedDiffeomorphismInsertion period hPeriod couplings
local notation "readout" => intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings
local notation "fields" => intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod
local notation "hessian" => intrinsicBulkBRSTHessian period hPeriod couplings

theorem intrinsicH11BRSTStrongSmooth_full_test_pairing (first second : State)
    (test : Bulk) (hReadout : readout test = fields second) :
    inner Real (strong first) (smooth second) =
      hessian (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings first) test := by
  have hProjection := intrinsicBulkBRSTHessian_diffeomorphism_test_projection
    period hPeriod couplings (fields first) test
  have hTest := (congrArg insert hReadout).trans
    (intrinsicBulkPairedDiffeomorphismInsertion_smooth period hPeriod couplings second)
  have hResult := hProjection.trans
    (congrArg (fun input => hessian (insert (fields first)) input) hTest)
  exact (intrinsicH11BRSTStrongSmooth_pairing period hPeriod couplings first second).trans hResult.symm

private theorem insertion_metric_zero (field : State) (hMetric : field.metricPerturbation = 0) :
    intrinsicBulkSmoothBRSTInsertion period hPeriod couplings field =
    intrinsicBulkDiffeomorphismInsertion period hPeriod couplings
      (finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod frame metric field.nonminimal) := by
  unfold intrinsicBulkSmoothBRSTInsertion finiteFrameSmoothPairedDiffeomorphismBRSTCore
  rw [hMetric]
  simp only [Pi.zero_apply, map_zero]
  rfl

theorem intrinsicH11BRSTStrongSmooth_nonminimal_full_bulk
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (first second : State) (hMetric : first.metricPerturbation = 0)
    (test : Bulk) (hReadout : readout test = fields second) :
    inner Real (strong first) (smooth second) =
      intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
        (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings first) test := by
  have hInsertion := insertion_metric_zero period hPeriod couplings first hMetric
  exact (intrinsicH11BRSTStrongSmooth_full_test_pairing period hPeriod couplings first second test hReadout).trans
    ((congrArg (fun input => hessian input test) hInsertion).trans
      ((intrinsicBulkBRSTHessian_diffeomorphism_eq_bulk period hPeriod couplings interactionScale coefficients _ test).trans
        (congrArg (fun input => intrinsicBulkHessian period hPeriod couplings interactionScale coefficients input test)
          hInsertion).symm))

theorem intrinsicH11BRSTStrongSmooth_nonminimal_full_bound
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (first second : State) (hMetric : first.metricPerturbation = 0)
    (test : Bulk) (hReadout : readout test = fields second) :
    ‖intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings first) test‖ ≤
        ‖strong first‖ * ‖smooth second‖ := by
  rw [← intrinsicH11BRSTStrongSmooth_nonminimal_full_bulk period hPeriod couplings
    interactionScale coefficients first second hMetric test hReadout]
  exact norm_inner_le_norm _ _

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicH11BRSTFullTestPairing4D
