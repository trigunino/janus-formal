import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicH11BRSTFullTestPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkEinsteinInteractionHessian4D

/-! The exact physical remainder of the H11-source BRST realization is the native
Einstein--interaction Hessian, against full bulk tests with smooth diagonal readout. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicH11PhysicalMetricRemainder4D
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

open P0EFTJanusProgramPT12IntrinsicH11BRSTFullTestPairing4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalMetricColumn4D
open P0EFTJanusProgramPT12IntrinsicBulkEinsteinInteractionHessian4D
local notation "metricInsert" => intrinsicBulkMetricInsertion period hPeriod couplings
local notation "metricReadout" => intrinsicBulkMetricReadout period hPeriod couplings
local notation "smoothInsert" => intrinsicBulkSmoothBRSTInsertion period hPeriod couplings
variable (interactionScale : Real) (coefficients : PotentialCoefficients)
local notation "physicalHessian" => intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
local notation "totalHessian" => intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
local notation "geometricHessian" => intrinsicBulkEinsteinInteractionHessian period hPeriod couplings interactionScale coefficients

theorem intrinsicH11PhysicalHessian_eq_EinsteinInteraction (first : State) (test : Bulk) :
    physicalHessian (smoothInsert first) test = geometricHessian (fields first).1 (metricReadout test) := by
  have hPhysical : physicalHessian (smoothInsert first) test =
      physicalHessian (metricInsert (fields first).1) test :=
    (intrinsicBulkPhysicalHessian_apply period hPeriod couplings interactionScale coefficients _ _).trans
      (intrinsicBulkPhysicalHessian_apply period hPeriod couplings interactionScale coefficients
        (metricInsert (fields first).1) test).symm
  exact hPhysical.trans (intrinsicBulkPhysicalHessian_metric_column period hPeriod couplings
    interactionScale coefficients (fields first).1 test)

/-- No terminal intertwiner is assumed: the only unrepresented summand is explicitly identified. -/
theorem intrinsicH11FullHessian_eq_geometric_add_BRST (first second : State)
    (test : Bulk) (hReadout : readout test = fields second) :
    totalHessian (smoothInsert first) test =
      geometricHessian (fields first).1 (metricReadout test) + inner Real (strong first) (smooth second) := by
  have hSplit : totalHessian (smoothInsert first) test =
      physicalHessian (smoothInsert first) test + hessian (smoothInsert first) test :=
    congrArg (fun form : Bulk →L[Real] Bulk →L[Real] Real => form (smoothInsert first) test)
      (intrinsicBulkHessian_eq_physical_add_BRST period hPeriod couplings interactionScale coefficients)
  exact hSplit.trans (congrArg₂ (fun x y : Real => x + y)
    (intrinsicH11PhysicalHessian_eq_EinsteinInteraction period hPeriod couplings interactionScale coefficients first test)
    (intrinsicH11BRSTStrongSmooth_full_test_pairing period hPeriod couplings first second test hReadout).symm)

theorem intrinsicH11FullHessian_smooth_remainder (first second : State) :
    totalHessian (smoothInsert first) (smoothInsert second) - inner Real (strong first) (smooth second) =
      geometricHessian (fields first).1 (fields second).1 := by
  have h := intrinsicH11FullHessian_eq_geometric_add_BRST period hPeriod couplings
    interactionScale coefficients first second (smoothInsert second) rfl
  exact sub_eq_iff_eq_add.mpr h

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicH11PhysicalMetricRemainder4D
