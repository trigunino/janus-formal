import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkGlobalBRSTHessian4D

/-! The full native BRST diffeomorphism column factors through the diagonal readout,
including tests with arbitrary Abelian, matter and LL components. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkDiffeomorphismColumnProjection4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
private theorem zero_left_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (form : E →L[Real] E →L[Real] Real) (first second : E) (value : Real) :
    form 0 first + form 0 second + value = value := by simp

private theorem zero_right_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (form : E →L[Real] E →L[Real] Real) (first second : E) (value : Real) :
    form first 0 + form second 0 + value = value := by simp

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
local notation "metric" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "AbelianInput" => FiniteFrameC2AbelianBRSTCore period hPeriod frame metric
local notation "AbelianFields" => FrameFreeAbelianBRSTFields period hPeriod frame
local notation "DiffeomorphismInput" => IntrinsicBulkPairedDiffeomorphismCore period hPeriod
local notation "GaugeInput" => FiniteFramePairedC2FullBRSTGaugeCore period hPeriod frame frame frame metric metric
local instance : NormedAddCommGroup (GeneralMetricRelativeC2Core period hPeriod frame metric) := inferInstance
local instance : NormedSpace Real (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  Submodule.normedSpace (GeneralMetricRelativeC2Core period hPeriod frame metric)
local instance : NormedAddCommGroup
    (P0EFTJanusFiniteFrameDiffeomorphismC2Core4D.FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) :=
  inferInstance
local instance : NormedSpace Real
    (P0EFTJanusFiniteFrameDiffeomorphismC2Core4D.FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) :=
  inferInstance
local instance : NormedAddCommGroup AbelianFields := inferInstance
local instance : NormedSpace Real AbelianFields := inferInstance
local instance : NormedAddCommGroup AbelianInput := inferInstance
local instance : NormedSpace Real AbelianInput := inferInstance
local instance : NormedAddCommGroup DiffeomorphismInput := inferInstance
local instance : NormedSpace Real DiffeomorphismInput := inferInstance
local instance : NormedAddCommGroup GaugeInput := inferInstance
local instance : NormedSpace Real GaugeInput := inferInstance

variable (couplings : GlobalCandidateAActionCouplings)
local notation "Bulk" => IntrinsicBulkCore period hPeriod couplings
local instance coreNormedAddCommGroup : NormedAddCommGroup Bulk := inferInstance
local instance : AddZeroClass Bulk := (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real Bulk :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings
local instance : NormedAddCommGroup (Bulk →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Bulk →L[Real] Real) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Bulk →L[Real] Bulk →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Bulk →L[Real] Bulk →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

open P0EFTJanusProgramPT12IntrinsicBulkGlobalBRSTHessian4D
local notation "insert" => intrinsicBulkPairedDiffeomorphismInsertion period hPeriod couplings
local notation "readout" => intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings
local notation "diagonal" => intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings
local notation "globalForm" => intrinsicBulkGlobalBRSTBilinearFamily period hPeriod couplings
local notation "abelian" => frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric
local notation "plusInput" => intrinsicBulkBRSTAbelianPlusInput period hPeriod couplings
local notation "minusInput" => intrinsicBulkBRSTAbelianMinusInput period hPeriod couplings

theorem intrinsicBulkBRSTDiffeomorphismInput_insertion (fields : DiffeomorphismInput) :
    readout (insert fields) = fields := rfl

private theorem frozen_left (fields : DiffeomorphismInput) (test : Bulk) :
    globalForm 0 (insert fields) test = diagonal 0 fields (readout test) := by
  change abelian 0 0 (plusInput test).2 + abelian 0 0 (minusInput test).2 +
    diagonal 0 fields (readout test) = _
  exact zero_left_sum (abelian 0) _ _ _

private theorem frozen_right (fields : DiffeomorphismInput) (test : Bulk) :
    globalForm 0 test (insert fields) = diagonal 0 (readout test) fields := by
  change abelian 0 (plusInput test).2 0 + abelian 0 (minusInput test).2 0 +
    diagonal 0 (readout test) fields = _
  exact zero_right_sum (abelian 0) _ _ _

/-- All off-sector test components disappear by the actual global Hessian formula. -/
theorem intrinsicBulkBRSTHessian_diffeomorphism_column (fields : DiffeomorphismInput) (test : Bulk) :
    intrinsicBulkBRSTHessian period hPeriod couplings (insert fields) test =
      diagonal 0 fields (readout test) + diagonal 0 (readout test) fields :=
  (intrinsicBulkBRSTHessian_eq_globalBilinear period hPeriod couplings (insert fields) test).trans
    (congrArg₂ (fun x y : Real => x + y)
      (frozen_left period hPeriod couplings fields test)
      (frozen_right period hPeriod couplings fields test))

theorem intrinsicBulkBRSTHessian_diffeomorphism_test_projection
    (fields : DiffeomorphismInput) (test : Bulk) :
    intrinsicBulkBRSTHessian period hPeriod couplings (insert fields) test =
      intrinsicBulkBRSTHessian period hPeriod couplings (insert fields) (insert (readout test)) :=
  (intrinsicBulkBRSTHessian_diffeomorphism_column period hPeriod couplings fields test).trans
    (intrinsicBulkBRSTHessian_pairedDiffeomorphism period hPeriod couplings fields (readout test)).symm

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkDiffeomorphismColumnProjection4D
