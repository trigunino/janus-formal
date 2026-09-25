import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongClosed4D

/-! Physical same-action Hessian columns represented by the closed native Maxwell Jacobi. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongPhysical4D
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
open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureSmoothAdjoint4D
open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPT12L2VolumeMultiplier4D

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureWeightColumns4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellSmoothWeight4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellCurvatureWeight4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphPairing4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
local notation "μ" => intrinsicCanonicalLorentzVolumeMeasure period hPeriod
local notation "Graph" => IntrinsicAbelianMaxwellLorenzGraph period hPeriod
local instance : NormedAddCommGroup Graph := inferInstance
local instance : NormedSpace Real Graph := inferInstance
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellCurvatureFactor4D

open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongSmooth4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongClosed4D
open P0EFTJanusProgramPT12IntrinsicBulkMaxwellRestriction4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianBARestriction4D
local instance : InnerProductSpace Real Graph :=
  Submodule.innerProductSpace (𝕜 := Real) (E := IntrinsicAbelianMaxwellLorenzAmbient period hPeriod)
    (intrinsicAbelianMaxwellLorenzSubmodule period hPeriod)
variable (couplings : GlobalCandidateAActionCouplings)
local notation "Gauge" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
private def smoothCoefficients (potential : Smooth) : Gauge × Gauge :=
  (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame (potential .plus),
    finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame (potential .minus))

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

/-- Every native physical Maxwell Hessian entry is the physical L² pairing of D* W D. -/
theorem intrinsicAbelianMaxwellStrongSmooth_eq_physicalHessian
    (interactionScale : Real) (coefficients : PotentialCoefficients) (first second : Smooth) :
    inner Real (intrinsicAbelianMaxwellStrongSmooth period hPeriod couplings first)
      (intrinsicAbelianPotentialL2Smooth period hPeriod second) =
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianAInsertion period hPeriod couplings (smoothCoefficients period hPeriod first))
      (intrinsicBulkAbelianAInsertion period hPeriod couplings (smoothCoefficients period hPeriod second)) := by
  exact (intrinsicAbelianMaxwellStrongSmooth_eq_graphHessian period hPeriod couplings first second).trans
    ((intrinsicAbelianMaxwellGraphRiesz_pairing period hPeriod couplings _ _).symm.trans
      (intrinsicAbelianMaxwellGraphRiesz_eq_physicalHessian period hPeriod couplings
        interactionScale coefficients first second))

/-- The same action column against any physical bulk test with the given potential readout. -/
theorem intrinsicAbelianMaxwellStrongSmooth_eq_physicalColumn
    (interactionScale : Real) (coefficients : PotentialCoefficients) (first second : Smooth)
    (test : Core)
    (hTest : intrinsicBulkAbelianPotentialReadout period hPeriod couplings test =
      smoothCoefficients period hPeriod second) :
    inner Real (intrinsicAbelianMaxwellStrongSmooth period hPeriod couplings first)
      (intrinsicAbelianPotentialL2Smooth period hPeriod second) =
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianAInsertion period hPeriod couplings (smoothCoefficients period hPeriod first)) test := by
  exact (intrinsicAbelianMaxwellStrongSmooth_eq_graphHessian period hPeriod couplings first second).trans
    ((intrinsicAbelianMaxwellGraphRiesz_pairing period hPeriod couplings _ _).symm.trans
      (intrinsicAbelianMaxwellGraphRiesz_eq_physicalColumn period hPeriod couplings
        interactionScale coefficients first second test hTest))

/-- The closed realization represents the physical Hessian on its certified smooth core. -/
theorem intrinsicAbelianMaxwellStrongMinimal_eq_physicalHessian
    (interactionScale : Real) (coefficients : PotentialCoefficients) (first second : Smooth) :
    inner Real (intrinsicAbelianMaxwellStrongMinimal period hPeriod couplings
      ⟨intrinsicAbelianPotentialL2Smooth period hPeriod first,
        intrinsicAbelianMaxwellStrongMinimal_smooth_mem period hPeriod couplings first⟩)
      (intrinsicAbelianPotentialL2Smooth period hPeriod second) =
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianAInsertion period hPeriod couplings (smoothCoefficients period hPeriod first))
      (intrinsicBulkAbelianAInsertion period hPeriod couplings (smoothCoefficients period hPeriod second)) := by
  exact (congrArg (fun value : Potential => inner Real value
    (intrinsicAbelianPotentialL2Smooth period hPeriod second))
    (intrinsicAbelianMaxwellStrongMinimal_smooth_apply period hPeriod couplings first)).trans
      (intrinsicAbelianMaxwellStrongSmooth_eq_physicalHessian period hPeriod couplings
        interactionScale coefficients first second)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongPhysical4D
