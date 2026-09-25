import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkMaxwellColumn4D

/-! Bounded self-adjoint realization of the physical Maxwell Hessian in the
Maxwell/Lorenz graph norm. This does not assert the Fredholm property. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphPairing4D
open P0EFTJanusProgramPT12IntrinsicBulkMaxwellColumn4D
open P0EFTJanusProgramPT12IntrinsicBulkMaxwellRestriction4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianBARestriction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
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
local instance ambientNormedGroup : NormedAddCommGroup (IntrinsicAbelianMaxwellLorenzAmbient period hPeriod) := inferInstance
local instance : SeminormedAddCommGroup (IntrinsicAbelianMaxwellLorenzAmbient period hPeriod) :=
  (ambientNormedGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real (IntrinsicAbelianMaxwellLorenzAmbient period hPeriod) := inferInstance
local instance graphNormedGroup : NormedAddCommGroup Graph := inferInstance
local instance : SeminormedAddCommGroup Graph := (graphNormedGroup period hPeriod).toSeminormedAddCommGroup
local instance graphInnerProductSpace : InnerProductSpace Real Graph :=
  Submodule.innerProductSpace (𝕜 := Real) (E := IntrinsicAbelianMaxwellLorenzAmbient period hPeriod)
    (intrinsicAbelianMaxwellLorenzSubmodule period hPeriod)
local instance graphNormedSpace : NormedSpace Real Graph :=
  (graphInnerProductSpace period hPeriod).toNormedSpace
local instance : Module Real Graph := (graphNormedSpace period hPeriod).toModule
local instance : NormedAddCommGroup (Graph →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Graph →L[Real] Real) := ContinuousLinearMap.toNormedSpace

variable (couplings : GlobalCandidateAActionCouplings)

private def pairedForm : Graph →L[Real] Graph →L[Real] Real :=
  couplings.plusMaxwellScale • intrinsicAbelianMaxwellGraphSectorPairing period hPeriod .plus +
    couplings.minusMaxwellScale • intrinsicAbelianMaxwellGraphSectorPairing period hPeriod .minus

def intrinsicAbelianMaxwellGraphHessian : Graph →L[Real] Graph →L[Real] Real :=
  pairedForm period hPeriod couplings + (pairedForm period hPeriod couplings).flip

def intrinsicAbelianMaxwellGraphRiesz : Graph →L[Real] Graph :=
  InnerProductSpace.continuousLinearMapOfBilin (intrinsicAbelianMaxwellGraphHessian period hPeriod couplings)

theorem intrinsicAbelianMaxwellGraphRiesz_pairing (first second : Graph) :
    inner Real (intrinsicAbelianMaxwellGraphRiesz period hPeriod couplings first) second =
      intrinsicAbelianMaxwellGraphHessian period hPeriod couplings first second :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ first second

theorem intrinsicAbelianMaxwellGraphRiesz_selfAdjoint :
    IsSelfAdjoint (intrinsicAbelianMaxwellGraphRiesz period hPeriod couplings) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro first second
  exact (intrinsicAbelianMaxwellGraphRiesz_pairing period hPeriod couplings first second).trans
    ((add_comm _ _).trans
      ((intrinsicAbelianMaxwellGraphRiesz_pairing period hPeriod couplings second first).symm.trans
        (real_inner_comm _ _)))

private def smoothCoefficients (potential : Smooth) : Gauge × Gauge :=
  (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame (potential .plus),
    finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame (potential .minus))

private theorem pairedForm_smooth (first second : Smooth) :
    pairedForm period hPeriod couplings
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first)
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second) =
      intrinsicBulkMaxwellPairing period hPeriod couplings
        (smoothCoefficients period hPeriod first) (smoothCoefficients period hPeriod second) := by
  change couplings.plusMaxwellScale * intrinsicAbelianMaxwellGraphSectorPairing period hPeriod .plus
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first)
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second) +
    couplings.minusMaxwellScale * intrinsicAbelianMaxwellGraphSectorPairing period hPeriod .minus
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first)
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second) = _
  rw [intrinsicAbelianMaxwellGraphSectorPairing_smooth, intrinsicAbelianMaxwellGraphSectorPairing_smooth]
  rfl

theorem intrinsicAbelianMaxwellGraphRiesz_smooth_pairing (first second : Smooth) :
    inner Real (intrinsicAbelianMaxwellGraphRiesz period hPeriod couplings
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first))
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second) =
      intrinsicBulkMaxwellPairing period hPeriod couplings
        (smoothCoefficients period hPeriod first) (smoothCoefficients period hPeriod second) +
      intrinsicBulkMaxwellPairing period hPeriod couplings
        (smoothCoefficients period hPeriod second) (smoothCoefficients period hPeriod first) := by
  exact (intrinsicAbelianMaxwellGraphRiesz_pairing period hPeriod couplings
    (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first)
    (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second)).trans
      (congrArg₂ (fun left right : Real => left + right)
        (pairedForm_smooth period hPeriod couplings first second)
        (pairedForm_smooth period hPeriod couplings second first))

open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkActionCore4D P0EFTJanusProgramPT12IntrinsicBulkAbelianLorenz4D
open P0EFTJanusReciprocalBimetricPotential
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (Throat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (Throat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (Throat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Throat period hPeriod) := borel _
local instance : BorelSpace (Throat period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert := InnerProductSpace.complexToReal
local notation "Core" => IntrinsicBulkCore period hPeriod couplings
local instance coreNormedGroup : NormedAddCommGroup Core := inferInstance
local instance : AddZeroClass Core := (coreNormedGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real Core :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings
local instance : NormedAddCommGroup (Core →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Core →L[Real] Real) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Core →L[Real] Core →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Core →L[Real] Core →L[Real] Real) := ContinuousLinearMap.toNormedSpace

theorem intrinsicAbelianMaxwellGraphRiesz_eq_physicalHessian
    (interactionScale : Real) (coefficients : PotentialCoefficients) (first second : Smooth) :
    inner Real (intrinsicAbelianMaxwellGraphRiesz period hPeriod couplings
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first))
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second) =
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianAInsertion period hPeriod couplings (smoothCoefficients period hPeriod first))
      (intrinsicBulkAbelianAInsertion period hPeriod couplings (smoothCoefficients period hPeriod second)) := by
  rw [intrinsicBulkPhysicalHessian_potential_potential]
  exact intrinsicAbelianMaxwellGraphRiesz_smooth_pairing period hPeriod couplings first second

theorem intrinsicAbelianMaxwellGraphRiesz_eq_physicalColumn
    (interactionScale : Real) (coefficients : PotentialCoefficients) (first second : Smooth)
    (test : Core)
    (hTest : intrinsicBulkAbelianPotentialReadout period hPeriod couplings test =
      smoothCoefficients period hPeriod second) :
    inner Real (intrinsicAbelianMaxwellGraphRiesz period hPeriod couplings
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first))
      (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second) =
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianAInsertion period hPeriod couplings (smoothCoefficients period hPeriod first)) test := by
  rw [intrinsicBulkPhysicalHessian_potential_column, hTest]
  exact intrinsicAbelianMaxwellGraphRiesz_smooth_pairing period hPeriod couplings first second

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D


