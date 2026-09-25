import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D

/-! Faithful realization of the genuine smooth diagonal diffeomorphism BRST
core in the intrinsic bulk completion. No completed BRST operator or quotient
descent is asserted. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkSmoothBRSTCore4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
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
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "base" => P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
  (intrinsicBulkGeometry period hPeriod)
private abbrev TangentSection := ContMDiffSection coverModelWithCorners CoverCoordinates ∞
  (fun point : Q period hPeriod => TangentSpace coverModelWithCorners point)

private theorem smoothCoefficients_injective :
    Function.Injective (finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame base) := by
  intro first second hEqual
  apply ContMDiffSection.ext
  intro point
  rw [← finiteFrameSmoothDiffeomorphismC2Coefficients_reconstructs period hPeriod frame base first point,
    ← finiteFrameSmoothDiffeomorphismC2Coefficients_reconstructs period hPeriod frame base second point, hEqual]

private theorem smoothCoefficients_zero :
    finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame base
      (0 : TangentSection period hPeriod) = 0 := by
  funext index
  change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
    (generalMetricFiniteFrameCoefficient period hPeriod frame base 0 index) = 0
  have hCoefficient : generalMetricFiniteFrameCoefficient period hPeriod frame base 0 index = 0 := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change generalMetricFiniteFrameCoefficientAt period hPeriod frame base point index 0 = 0
    exact map_zero _
  rw [hCoefficient, map_zero]

variable (couplings : GlobalCandidateAActionCouplings)
local instance coreNormedAddCommGroup : NormedAddCommGroup (IntrinsicBulkCore period hPeriod couplings) := inferInstance
local instance : AddZeroClass (IntrinsicBulkCore period hPeriod couplings) :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass

/-- Native paired smooth coefficients, with all other bulk sectors set to zero. -/
def intrinsicBulkSmoothBRSTInsertion
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    IntrinsicBulkCore period hPeriod couplings :=
  let paired := finiteFrameSmoothPairedDiffeomorphismBRSTCore period hPeriod frame frame frame
    base base base (state.metricPerturbation .plus) (state.metricPerturbation .minus) state.nonminimal
  (((paired.1, (0, paired.2)), 0), 0)

@[simp] theorem intrinsicBulkSmoothBRSTInsertion_metric
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings state).1.1.1 =
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame base (state.metricPerturbation .plus),
        smoothToGeneralMetricRelativeC2Core period hPeriod frame base (state.metricPerturbation .minus)) := rfl

theorem intrinsicBulkSmoothBRSTInsertion_injective :
    Function.Injective (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings) := by
  intro first second hEqual
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
  · funext sector
    cases sector with
    | plus =>
      apply smoothToGeneralMetricRelativeC2Core_injective period hPeriod frame base
      exact congrArg (fun input : IntrinsicBulkCore period hPeriod couplings => input.1.1.1.1) hEqual
    | minus =>
      apply smoothToGeneralMetricRelativeC2Core_injective period hPeriod frame base
      exact congrArg (fun input : IntrinsicBulkCore period hPeriod couplings => input.1.1.1.2) hEqual
  · apply GlobalDiffeomorphismNonminimalFields.ext
    · apply GlobalDiffeomorphismGhostField.ext
      apply smoothCoefficients_injective period hPeriod
      exact congrArg (fun input : IntrinsicBulkCore period hPeriod couplings => input.1.1.2.2.2.2) hEqual
    · apply GlobalDiffeomorphismAntighostField.ext
      apply smoothCoefficients_injective period hPeriod
      exact congrArg (fun input : IntrinsicBulkCore period hPeriod couplings => input.1.1.2.2.2.1) hEqual
    · apply GlobalDiffeomorphismNakanishiLautrupField.ext
      apply smoothCoefficients_injective period hPeriod
      exact congrArg (fun input : IntrinsicBulkCore period hPeriod couplings => input.1.1.2.2.1) hEqual

def intrinsicBulkPureGhostBRSTState (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod where
  metricPerturbation := 0
  nonminimal := {
    ghost := ghost
    antighost := zeroGlobalDiffeomorphismAntighostField period hPeriod
    nakanishiLautrup := zeroGlobalDiffeomorphismNakanishiLautrupField period hPeriod }

theorem intrinsicBulkSmoothBRSTInsertion_pureGhost (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    intrinsicBulkSmoothBRSTInsertion period hPeriod couplings (intrinsicBulkPureGhostBRSTState period hPeriod ghost) =
      intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings ghost := by
  change (((
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame base 0,
      smoothToGeneralMetricRelativeC2Core period hPeriod frame base 0),
    (0, (finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame base (0 : TangentSection period hPeriod),
      (finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame base (0 : TangentSection period hPeriod),
        finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame base ghost.field)))), 0), 0) = _
  rw [map_zero, smoothCoefficients_zero]
  rfl

/-- The existing real-linearized BRST differential at the actual two base metrics. -/
def intrinsicBulkSmoothBRST (state : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod :=
  globalCandidateADiagonalDiffeomorphismBRST period hPeriod
    (fun sector => match sector with
      | .plus => (intrinsicBulkGeometry period hPeriod).plusMetric
      | .minus => (intrinsicBulkGeometry period hPeriod).minusMetric) state

/-- Exact metric readout of the true BRST image of a smooth pure ghost. -/
theorem intrinsicBulkSmoothBRSTInsertion_BRST_pureGhost_metric
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings
      (intrinsicBulkSmoothBRST period hPeriod (intrinsicBulkPureGhostBRSTState period hPeriod ghost))).1.1.1 =
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame base
        (globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap period hPeriod
          (intrinsicBulkGeometry period hPeriod).plusMetric ghost),
      smoothToGeneralMetricRelativeC2Core period hPeriod frame base
        (globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap period hPeriod
          (intrinsicBulkGeometry period hPeriod).minusMetric ghost)) := rfl

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkSmoothBRSTCore4D
