import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkSmoothAntighostRadical4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkBRSTColumns4D

/-! The shared antighost column of the full intrinsic bulk Hessian. The
physical block vanishes by the existing exact physical/BRST decomposition;
only the explicit opposite-Einstein-weight equation is imposed. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAntighostHessian4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothBRSTCore4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothAntighostRadical4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTColumns4D
open P0EFTJanusReciprocalBimetricPotential
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

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
local notation "metric" => P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
  (intrinsicBulkGeometry period hPeriod)
local notation "Ghost" => FiniteFrameDiffeomorphismC2Core period hPeriod frame
local instance : NormedAddCommGroup Ghost := inferInstance
local instance : NormedSpace Real Ghost := inferInstance
variable (couplings : GlobalCandidateAActionCouplings)
local notation "Bulk" => IntrinsicBulkCore period hPeriod couplings
local instance coreNormedAddCommGroup : NormedAddCommGroup Bulk := inferInstance
local instance : AddZeroClass Bulk := (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real Bulk :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings

/-- Bounded insertion into the actual antighost slot of the shared packet. -/
def intrinsicBulkDiffeomorphismAntighostInsertion : Ghost →L[Real] Bulk :=
  (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings).comp
    ((0 : Ghost →L[Real] Ghost).prod ((ContinuousLinearMap.id Real Ghost).prod 0))

@[simp] theorem intrinsicBulkDiffeomorphismAntighostInsertion_apply (antighost : Ghost) :
    intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings antighost =
      intrinsicBulkDiffeomorphismInsertion period hPeriod couplings (0, (antighost, 0)) := rfl

theorem intrinsicBulkDiffeomorphismAntighostInsertion_injective :
    Function.Injective (intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings) := by
  intro first second hEqual
  exact congrArg (fun input : Bulk => input.1.1.2.2.2.1) hEqual

/-- Full bulk column, for arbitrary completed C² antighost coefficients and
arbitrary native bulk tests, at arbitrary interaction/potential couplings. -/
theorem intrinsicBulkHessian_antighost_column_zero
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings + candidateAMinusEinsteinKineticWeight couplings = 0)
    (antighost : Ghost) (test : Bulk) :
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings antighost) test = 0 :=
  (intrinsicBulkBRSTHessian_diffeomorphism_eq_bulk period hPeriod couplings interactionScale coefficients
    (0, (antighost, 0)) test).symm.trans
      (intrinsicBulkBRSTHessian_antighost_column_zero period hPeriod couplings hWeights antighost test)

/-- The faithful smooth insertion uses exactly the same coefficient slot. -/
theorem intrinsicBulkSmoothAntighostInsertion_eq_coefficients
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    intrinsicBulkSmoothAntighostInsertion period hPeriod couplings antighost =
      intrinsicBulkDiffeomorphismAntighostInsertion period hPeriod couplings
        (intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod ⟨antighost.field⟩) := by
  have hZero := (intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod).map_zero
  change (((
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric 0,
      smoothToGeneralMetricRelativeC2Core period hPeriod frame metric 0),
    (0, (intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod 0,
      (intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod ⟨antighost.field⟩,
        intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod 0)))), 0), 0) = _
  rw [map_zero, hZero]
  rfl

theorem intrinsicBulkHessian_smoothAntighost_column_zero
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings + candidateAMinusEinsteinKineticWeight couplings = 0)
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) (test : Bulk) :
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkSmoothAntighostInsertion period hPeriod couplings antighost) test = 0 := by
  have hInsertion := congrArg
    (fun input : Bulk => intrinsicBulkHessian period hPeriod couplings interactionScale coefficients input test)
    (intrinsicBulkSmoothAntighostInsertion_eq_coefficients period hPeriod couplings antighost)
  exact hInsertion.trans (intrinsicBulkHessian_antighost_column_zero period hPeriod couplings
    interactionScale coefficients hWeights _ test)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAntighostHessian4D
