import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkGlobalBRSTHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkPairedAbelianHessian4D

import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkMaxwellColumn4D

/-! Full native paired Abelian BRST columns against unrestricted bulk tests. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianColumnProjection4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

private theorem left_zero_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (form : E →L[Real] E →L[Real] Real) (test : E) (value : Real) :
    value + form 0 test = value := by simp

private theorem right_zero_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (form : E →L[Real] E →L[Real] Real) (test : E) (value : Real) :
    value + form test 0 = value := by simp

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
open P0EFTJanusProgramPT12IntrinsicBulkPairedAbelianHessian4D
local notation "Fields" => IntrinsicBulkPairedAbelianCore period hPeriod
local instance : NormedAddCommGroup Fields := inferInstance
local instance : NormedSpace Real Fields := inferInstance
local notation "insert" => intrinsicBulkPairedAbelianInsertion period hPeriod couplings
local notation "paired" => intrinsicBulkPairedAbelianBilinear period hPeriod
local notation "diagonal" => intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings
local notation "globalForm" => intrinsicBulkGlobalBRSTBilinearFamily period hPeriod couplings
local notation "abelian" => frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric
local notation "plusInput" => intrinsicBulkBRSTAbelianPlusInput period hPeriod couplings
local notation "minusInput" => intrinsicBulkBRSTAbelianMinusInput period hPeriod couplings
local notation "diffInput" => intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings

def intrinsicBulkBRSTPairedAbelianReadout : Bulk →L[Real] Fields :=
  ((ContinuousLinearMap.snd Real _ _).comp plusInput).prod
    ((ContinuousLinearMap.snd Real _ _).comp minusInput)
local notation "readout" => intrinsicBulkBRSTPairedAbelianReadout period hPeriod couplings

theorem intrinsicBulkBRSTPairedAbelianReadout_insertion (fields : Fields) :
    readout (insert fields) = fields := rfl

private theorem frozen_left (fields : Fields) (test : Bulk) :
    globalForm 0 (insert fields) test = paired fields (readout test) := by
  change (abelian 0 fields.1 (plusInput test).2 + abelian 0 fields.2 (minusInput test).2) +
    diagonal 0 0 (diffInput test) = _
  exact left_zero_tail (diagonal 0) _ _

private theorem frozen_right (fields : Fields) (test : Bulk) :
    globalForm 0 test (insert fields) = paired (readout test) fields := by
  change (abelian 0 (plusInput test).2 fields.1 + abelian 0 (minusInput test).2 fields.2) +
    diagonal 0 (diffInput test) 0 = _
  exact right_zero_tail (diagonal 0) _ _

theorem intrinsicBulkBRSTHessian_pairedAbelian_column (fields : Fields) (test : Bulk) :
    intrinsicBulkBRSTHessian period hPeriod couplings (insert fields) test =
      paired fields (readout test) + paired (readout test) fields :=
  (intrinsicBulkBRSTHessian_eq_globalBilinear period hPeriod couplings (insert fields) test).trans
    (congrArg₂ (fun x y : Real => x + y)
      (frozen_left period hPeriod couplings fields test)
      (frozen_right period hPeriod couplings fields test))

theorem intrinsicBulkBRSTHessian_pairedAbelian_test_projection (fields : Fields) (test : Bulk) :
    intrinsicBulkBRSTHessian period hPeriod couplings (insert fields) test =
      intrinsicBulkBRSTHessian period hPeriod couplings (insert fields) (insert (readout test)) :=
  (intrinsicBulkBRSTHessian_pairedAbelian_column period hPeriod couplings fields test).trans
    (intrinsicBulkBRSTHessian_pairedAbelian period hPeriod couplings fields (readout test)).symm

open P0EFTJanusProgramPT12IntrinsicBulkMaxwellColumn4D
open P0EFTJanusProgramPT12IntrinsicBulkMaxwellRestriction4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusReciprocalBimetricPotential

/-- The physical Maxwell and BRST contributions together depend only on the Abelian readout. -/
theorem intrinsicBulkHessian_pairedAbelian_test_projection
    (interactionScale : Real) (coefficients : PotentialCoefficients) (fields : Fields) (test : Bulk) :
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients (insert fields) test =
      intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
        (insert fields) (insert (readout test)) := by
  have hPhysical := (intrinsicBulkPhysicalHessian_pairedAbelian_column period hPeriod couplings
    interactionScale coefficients fields test).trans
      (intrinsicBulkPhysicalHessian_pairedAbelian_column period hPeriod couplings
        interactionScale coefficients fields (insert (readout test))).symm
  have hBRST := intrinsicBulkBRSTHessian_pairedAbelian_test_projection period hPeriod couplings fields test
  have hSplit (input : Bulk) :
      intrinsicBulkHessian period hPeriod couplings interactionScale coefficients (insert fields) input =
        intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients (insert fields) input +
          intrinsicBulkBRSTHessian period hPeriod couplings (insert fields) input :=
    congrArg (fun form : Bulk →L[Real] Bulk →L[Real] Real => form (insert fields) input)
      (intrinsicBulkHessian_eq_physical_add_BRST period hPeriod couplings interactionScale coefficients)
  exact (hSplit test).trans
    ((congrArg₂ (fun x y : Real => x + y) hPhysical hBRST).trans (hSplit (insert (readout test))).symm)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianColumnProjection4D
