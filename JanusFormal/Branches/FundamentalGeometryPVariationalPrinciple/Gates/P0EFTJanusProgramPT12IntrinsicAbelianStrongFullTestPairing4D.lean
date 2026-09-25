import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAbelianColumnProjection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongClosed4D

/-! Full Maxwell--BRST L² columns against bulk tests with smooth paired Abelian readout. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianStrongFullTestPairing4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameC2AbelianBRSTAction4D P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
open P0EFTJanusProgramPT12FrameFreeAbelianBilinearFamily4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismBilinearFamily4D
open P0EFTJanusProgramPT12IntrinsicBulkPairedDiffeomorphismHessian4D
open P0EFTJanusProgramPT12BilinearSecondJetFreeze4D

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
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "metric" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12IntrinsicAbelianPotentialL2Core4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullL2Core4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullStrongSmooth4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullStrongClosed4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianColumnProjection4D
open P0EFTJanusProgramPT12IntrinsicBulkPairedAbelianHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusReciprocalBimetricPotential
local notation "State" => GlobalPairedAbelianBRSTState period hPeriod
local notation "Potential" => IntrinsicAbelianPotentialL2Core period hPeriod
local instance potentialGroup : NormedAddCommGroup Potential := inferInstance
local instance : SeminormedAddCommGroup Potential := (potentialGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Potential := inferInstance
local instance : InnerProductSpace Real Potential :=
  Submodule.innerProductSpace (𝕜 := Real) (intrinsicAbelianPotentialL2Submodule period hPeriod)
local notation "Gauge" => GlobalPairedGaugeLieL2 period hPeriod
local instance gaugeGroup : NormedAddCommGroup Gauge := inferInstance
local instance : SeminormedAddCommGroup Gauge := (gaugeGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Gauge := inferInstance
local instance : InnerProductSpace Real Gauge := inferInstance
local notation "Full" => IntrinsicAbelianFullL2 period hPeriod
local instance fullGroup : NormedAddCommGroup Full := inferInstance
local instance : SeminormedAddCommGroup Full := (fullGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Full := inferInstance
local instance : InnerProductSpace Real Full := inferInstance
variable (couplings : GlobalCandidateAActionCouplings)
local notation "Bulk" => IntrinsicBulkCore period hPeriod couplings
local instance : NormedAddCommGroup Bulk := inferInstance
local instance : NormedSpace Real Bulk :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings
local notation "insert" => intrinsicBulkPairedAbelianInsertion period hPeriod couplings
local notation "readout" => intrinsicBulkBRSTPairedAbelianReadout period hPeriod couplings
local notation "fields" => intrinsicBulkSmoothPairedAbelianFields period hPeriod
local notation "smooth" => intrinsicAbelianFullL2Smooth period hPeriod
local notation "strong" => intrinsicAbelianFullStrongSmooth period hPeriod couplings
local notation "minimal" => intrinsicAbelianFullStrongMinimal period hPeriod couplings
variable (interactionScale : Real) (coefficients : PotentialCoefficients)
local notation "hessian" => intrinsicBulkHessian period hPeriod couplings interactionScale coefficients

theorem intrinsicAbelianFullStrongSmooth_full_test_pairing (first second : State)
    (test : Bulk) (hReadout : readout test = fields second) :
    inner Real (strong first) (smooth second) = hessian (insert (fields first)) test := by
  have hProjection := intrinsicBulkHessian_pairedAbelian_test_projection period hPeriod couplings
    interactionScale coefficients (fields first) test
  have hResult := hProjection.trans
    (congrArg (fun value => hessian (insert (fields first)) (insert value)) hReadout)
  exact (intrinsicAbelianFullStrongSmooth_eq_bulkHessian period hPeriod couplings
    interactionScale coefficients first second).trans hResult.symm

theorem intrinsicAbelianFullStrongMinimal_full_test_pairing (first second : State)
    (test : Bulk) (hReadout : readout test = fields second) :
    inner Real (minimal ⟨smooth first,
      intrinsicAbelianFullStrongMinimal_smooth_mem period hPeriod couplings first⟩) (smooth second) =
        hessian (insert (fields first)) test :=
  (congrArg (fun value : Full => inner Real value (smooth second))
    (intrinsicAbelianFullStrongMinimal_smooth_apply period hPeriod couplings first)).trans
      (intrinsicAbelianFullStrongSmooth_full_test_pairing period hPeriod couplings
        interactionScale coefficients first second test hReadout)

theorem intrinsicAbelianFullStrongSmooth_full_test_bound (first second : State)
    (test : Bulk) (hReadout : readout test = fields second) :
    ‖hessian (insert (fields first)) test‖ ≤ ‖strong first‖ * ‖smooth second‖ := by
  rw [← intrinsicAbelianFullStrongSmooth_full_test_pairing period hPeriod couplings
    interactionScale coefficients first second test hReadout]
  exact norm_inner_le_norm _ _

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianStrongFullTestPairing4D
