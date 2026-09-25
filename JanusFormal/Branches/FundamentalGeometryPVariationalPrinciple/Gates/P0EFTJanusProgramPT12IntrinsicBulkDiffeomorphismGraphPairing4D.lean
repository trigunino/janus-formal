import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkPairedDiffeomorphismHessian4D

/-! The genuine native BRST Hessian agrees with the inhabited smooth-metric
off-shell graph form, retaining both metric columns and the shared triple. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkDiffeomorphismGraphPairing4D
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
private abbrev TangentSection := ContMDiffSection coverModelWithCorners CoverCoordinates ∞
  (fun point : Q period hPeriod => TangentSpace coverModelWithCorners point)

private theorem smoothCoefficients_add
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : TangentSection period hPeriod) :
    finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame metric (first + second) =
      finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame metric first +
        finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame metric second := by
  funext index
  have hCoefficient : generalMetricFiniteFrameCoefficient period hPeriod frame metric (first + second) index =
      generalMetricFiniteFrameCoefficient period hPeriod frame metric first index +
        generalMetricFiniteFrameCoefficient period hPeriod frame metric second index := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    exact (generalMetricFiniteFrameCoefficientAt period hPeriod frame metric point index).map_add
      (first point) (second point)
  exact (congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod) hCoefficient).trans
    ((smoothToCanonicalPhysicalScalarC2JetCore period hPeriod).map_add _ _)

private theorem smoothNonminimal_add
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod frame metric (first + second) =
      finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod frame metric first +
        finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod frame metric second := by
  apply Prod.ext
  · exact smoothCoefficients_add period hPeriod frame metric _ _
  · exact Prod.ext (smoothCoefficients_add period hPeriod frame metric _ _)
      (smoothCoefficients_add period hPeriod frame metric _ _)

private theorem frozenCoefficient_smooth
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric 0
        (finiteFrameSmoothDiffeomorphismBRSTCore period hPeriod frame metric 0 state).2
        (finiteFrameSmoothDiffeomorphismBRSTCore period hPeriod frame metric 0 state).2 =
      globalDiffeomorphismGaugeFermionBRSTVariation period hPeriod metric state := by
  have hVolume : smoothToGeneralMetricRelativeC2Core period hPeriod frame metric
      (0 : SmoothSymmetricCovariantTwoTensor period hPeriod) ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame metric := by
    rw [map_zero]
    exact zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame metric
  have hAction := finiteFrameC2DiffeomorphismBRSTAction_smooth period hPeriod frame metric 0 metric
    (add_zero _).symm hVolume state
  rw [finiteFrameSmoothDiffeomorphismBRSTCore, map_zero,
    frameFreeDiffeomorphismBRSTAction_eq_bilinear] at hAction
  exact hAction

local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "metric" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "State" => GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod
local notation "Fields" => IntrinsicBulkPairedDiffeomorphismCore period hPeriod
local instance : NormedAddCommGroup (GeneralMetricRelativeC2Core period hPeriod frame metric) := inferInstance
local instance : NormedSpace Real (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  Submodule.normedSpace (GeneralMetricRelativeC2Core period hPeriod frame metric)
local instance : NormedAddCommGroup (FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) := inferInstance
local instance : NormedSpace Real (FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) := inferInstance
local instance : NormedAddCommGroup Fields := inferInstance
local instance : NormedSpace Real Fields := inferInstance
local instance : NormedAddCommGroup
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod (fun _ => metric)) :=
  diagonalGraphNormedAddCommGroupValue period hPeriod (fun _ => metric)
local instance : NormedSpace Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod (fun _ => metric)) :=
  diagonalGraphNormedSpace period hPeriod (fun _ => metric)

theorem intrinsicBulkSmoothPairedDiffeomorphismFields_add (first second : State) :
    intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod (first + second) =
      intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod first +
        intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod second := by
  apply Prod.ext
  · exact Prod.ext ((smoothToGeneralMetricRelativeC2Core period hPeriod frame metric).map_add _ _)
      ((smoothToGeneralMetricRelativeC2Core period hPeriod frame metric).map_add _ _)
  · exact smoothNonminimal_add period hPeriod frame metric _ _

variable (couplings : GlobalCandidateAActionCouplings)

theorem intrinsicBulkPairedDiffeomorphismBilinear_smooth_diagonal (state : State) :
    intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings 0
        (intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod state)
        (intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod state) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period hPeriod couplings
        (fun _ => metric) state := by
  change candidateAPlusEinsteinKineticWeight couplings *
      frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric 0
        ((smoothToGeneralMetricRelativeC2Core period hPeriod frame metric (state.metricPerturbation .plus)),
          finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod frame frame metric
            (finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod frame metric state.nonminimal))
        ((smoothToGeneralMetricRelativeC2Core period hPeriod frame metric (state.metricPerturbation .plus)),
          finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod frame frame metric
            (finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod frame metric state.nonminimal)) +
    candidateAMinusEinsteinKineticWeight couplings *
      frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric 0
        ((smoothToGeneralMetricRelativeC2Core period hPeriod frame metric (state.metricPerturbation .minus)),
          finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod frame frame metric
            (finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod frame metric state.nonminimal))
        ((smoothToGeneralMetricRelativeC2Core period hPeriod frame metric (state.metricPerturbation .minus)),
          finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod frame frame metric
            (finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod frame metric state.nonminimal)) = _
  rw [finiteFrameDiffeomorphismNonminimalC2Transition_smooth]
  exact congrArg₂ (fun x y : Real => candidateAPlusEinsteinKineticWeight couplings * x +
    candidateAMinusEinsteinKineticWeight couplings * y)
      (frozenCoefficient_smooth period hPeriod frame metric
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod .plus state))
      (frozenCoefficient_smooth period hPeriod frame metric
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod .minus state))

theorem intrinsicBulkPairedDiffeomorphismBilinear_smooth_eq_graph (first second : State) :
    intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings 0
        (intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod first)
        (intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod second) +
      intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings 0
        (intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod second)
        (intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod first) =
      globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings (fun _ => metric)
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod (fun _ => metric) first)
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod (fun _ => metric) second) := by
  have hDiag (state : State) :=
    (intrinsicBulkPairedDiffeomorphismBilinear_smooth_diagonal period hPeriod couplings state).trans
      (globalCandidateADiagonalDiffeomorphismOffShellGraphAction_smooth_eq_BRST
        period hPeriod couplings (fun _ => metric) state).symm
  simp only [globalCandidateADiagonalDiffeomorphismOffShellGraphAction] at hDiag
  have hSum := hDiag (first + second)
  rw [intrinsicBulkSmoothPairedDiffeomorphismFields_add, map_add] at hSum
  simp only [map_add, _root_.add_apply] at hSum
  have hSym := globalCandidateADiagonalDiffeomorphismOffShellHessian_comm period hPeriod couplings
    (fun _ => metric)
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod (fun _ => metric) second)
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod (fun _ => metric) first)
  linarith only [hSum, hDiag first, hDiag second, hSym]

local instance : NormedAddCommGroup (IntrinsicBulkCore period hPeriod couplings) := inferInstance
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings

theorem intrinsicBulkBRSTHessian_smoothDiffeomorphism_eq_offShellGraph (first second : State) :
    intrinsicBulkBRSTHessian period hPeriod couplings
        (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings first)
        (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings second) =
      globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings (fun _ => metric)
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod (fun _ => metric) first)
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod (fun _ => metric) second) := by
  have hInput := congrArg₂
    (fun x y : IntrinsicBulkCore period hPeriod couplings => intrinsicBulkBRSTHessian period hPeriod couplings x y)
    (intrinsicBulkPairedDiffeomorphismInsertion_smooth period hPeriod couplings first).symm
    (intrinsicBulkPairedDiffeomorphismInsertion_smooth period hPeriod couplings second).symm
  exact hInput.trans ((intrinsicBulkBRSTHessian_pairedDiffeomorphism period hPeriod couplings
    (intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod first)
    (intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod second)).trans
      (intrinsicBulkPairedDiffeomorphismBilinear_smooth_eq_graph period hPeriod couplings first second))

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkDiffeomorphismGraphPairing4D
