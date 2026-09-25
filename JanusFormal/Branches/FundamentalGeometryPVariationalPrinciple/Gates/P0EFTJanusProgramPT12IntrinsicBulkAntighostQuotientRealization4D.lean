import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkSmoothAntighostBRSTQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkPairedDiffeomorphismHessian4D

/-! Faithful realization of the actual smooth antighost quotient in the closed
C² bulk quotient. No extension of BRST beyond its smooth domain is asserted. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAntighostQuotientRealization4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothBRSTCore4D
open P0EFTJanusProgramPT12IntrinsicBulkPairedDiffeomorphismHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkAntighostQuotient4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothAntighostBRSTQuotient4D
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
local notation "State" => GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod
local notation "Ghost" => GlobalDiffeomorphismGhostField period hPeriod
local notation "Fields" => IntrinsicBulkPairedDiffeomorphismCore period hPeriod
local instance : NormedAddCommGroup (GeneralMetricRelativeC2Core period hPeriod frame metric) := inferInstance
local instance : NormedSpace Real (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  Submodule.normedSpace (GeneralMetricRelativeC2Core period hPeriod frame metric)
local instance : NormedAddCommGroup (FiniteFrameDiffeomorphismC2Core period hPeriod frame) := inferInstance
local instance : NormedSpace Real (FiniteFrameDiffeomorphismC2Core period hPeriod frame) := inferInstance
local instance : NormedAddCommGroup Fields := inferInstance
local instance : NormedSpace Real Fields := inferInstance

private def metricReadout (sector : Sector) :
    State →ₗ[Real] SmoothSymmetricCovariantTwoTensor period hPeriod where
  toFun state := state.metricPerturbation sector
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def nonminimalReadout : State →ₗ[Real] Ghost × (Ghost × Ghost) where
  toFun state := (⟨state.nonminimal.nakanishiLautrup.field⟩,
    (⟨state.nonminimal.antighost.field⟩, state.nonminimal.ghost))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def smoothPairedFieldsLinearMap : State →ₗ[Real] Fields :=
  let metricMap := smoothToGeneralMetricRelativeC2Core period hPeriod frame metric
  let ghostMap := intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod
  ((metricMap.comp (metricReadout period hPeriod .plus)).prod
    (metricMap.comp (metricReadout period hPeriod .minus))).prod
      ((ghostMap.prodMap (ghostMap.prodMap ghostMap)).comp (nonminimalReadout period hPeriod))

private theorem smoothPairedFieldsLinearMap_apply (state : State) :
    smoothPairedFieldsLinearMap period hPeriod state =
      intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod state := rfl

variable (couplings : GlobalCandidateAActionCouplings)
local notation "Bulk" => IntrinsicBulkCore period hPeriod couplings
local instance bulkNormedAddCommGroup : NormedAddCommGroup Bulk := inferInstance
local instance : AddZeroClass Bulk :=
  (bulkNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance bulkNormedSpace : NormedSpace Real Bulk :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings
local instance : Module Real Bulk := (bulkNormedSpace period hPeriod couplings).toModule

def intrinsicBulkSmoothBRSTInsertionLinearMap : State →ₗ[Real] Bulk :=
  (intrinsicBulkPairedDiffeomorphismInsertion period hPeriod couplings).toLinearMap.comp
    (smoothPairedFieldsLinearMap period hPeriod)

@[simp] theorem intrinsicBulkSmoothBRSTInsertionLinearMap_apply (state : State) :
    intrinsicBulkSmoothBRSTInsertionLinearMap period hPeriod couplings state =
      intrinsicBulkSmoothBRSTInsertion period hPeriod couplings state :=
  (congrArg (intrinsicBulkPairedDiffeomorphismInsertion period hPeriod couplings)
    (smoothPairedFieldsLinearMap_apply period hPeriod state)).trans
      (intrinsicBulkPairedDiffeomorphismInsertion_smooth period hPeriod couplings state)

local notation "R" => intrinsicBulkAntighostRadical period hPeriod couplings
local notation "Rs" => intrinsicBulkSmoothAntighostStateRadical period hPeriod
local notation "Reduced" => IntrinsicBulkAntighostQuotient period hPeriod couplings

private def projectedSmoothInsertion : State →ₗ[Real] Reduced :=
  (R).mkQ.comp (intrinsicBulkSmoothBRSTInsertionLinearMap period hPeriod couplings)

private theorem projectedSmoothInsertion_ker :
    (projectedSmoothInsertion period hPeriod couplings).ker = Rs := by
  apply Submodule.ext
  intro state
  change (Submodule.Quotient.mk (intrinsicBulkSmoothBRSTInsertionLinearMap period hPeriod couplings state) : Reduced) = 0 ↔
    state ∈ Rs
  rw [Submodule.Quotient.mk_eq_zero, intrinsicBulkSmoothBRSTInsertionLinearMap_apply]
  exact (intrinsicBulkSmoothBRSTInsertion_mem_antighostRadical_iff period hPeriod couplings state).trans
    (intrinsicBulkSmoothAntighostStateRadical_mem_iff period hPeriod state).symm

/-- The smooth quotient embeds faithfully in the quotient of the actual bulk core. -/
def intrinsicBulkAntighostQuotientRealization :
    IntrinsicBulkSmoothAntighostBRSTQuotient period hPeriod →ₗ[Real] Reduced :=
  (Rs).liftQ (projectedSmoothInsertion period hPeriod couplings)
    (projectedSmoothInsertion_ker period hPeriod couplings).symm.le

@[simp] theorem intrinsicBulkAntighostQuotientRealization_mk (state : State) :
    intrinsicBulkAntighostQuotientRealization period hPeriod couplings
      (intrinsicBulkSmoothAntighostQuotientMap period hPeriod state) =
    intrinsicBulkAntighostQuotientMap period hPeriod couplings
      (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings state) :=
  congrArg (R).mkQ (intrinsicBulkSmoothBRSTInsertionLinearMap_apply period hPeriod couplings state)

theorem intrinsicBulkAntighostQuotientRealization_injective :
    Function.Injective (intrinsicBulkAntighostQuotientRealization period hPeriod couplings) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot (Rs)
    (projectedSmoothInsertion period hPeriod couplings)
    (projectedSmoothInsertion_ker period hPeriod couplings).symm.le
    (projectedSmoothInsertion_ker period hPeriod couplings).le)

def intrinsicBulkAntighostBRSTCoreEquiv :
    IntrinsicBulkSmoothAntighostBRSTQuotient period hPeriod ≃ₗ[Real]
      (intrinsicBulkAntighostQuotientRealization period hPeriod couplings).range :=
  LinearEquiv.ofInjective (intrinsicBulkAntighostQuotientRealization period hPeriod couplings)
    (intrinsicBulkAntighostQuotientRealization_injective period hPeriod couplings)

/-- The actual BRST differential on the realized smooth core of the C² quotient. -/
def intrinsicBulkAntighostBRSTCore :
    (intrinsicBulkAntighostQuotientRealization period hPeriod couplings).range →ₗ[Real]
      (intrinsicBulkAntighostQuotientRealization period hPeriod couplings).range :=
  (intrinsicBulkAntighostBRSTCoreEquiv period hPeriod couplings).toLinearMap.comp
    ((intrinsicBulkSmoothAntighostQuotientBRST period hPeriod).comp
      (intrinsicBulkAntighostBRSTCoreEquiv period hPeriod couplings).symm.toLinearMap)

theorem intrinsicBulkAntighostBRSTCore_square_zero
    (point : (intrinsicBulkAntighostQuotientRealization period hPeriod couplings).range) :
    intrinsicBulkAntighostBRSTCore period hPeriod couplings
      (intrinsicBulkAntighostBRSTCore period hPeriod couplings point) = 0 := by
  simp only [intrinsicBulkAntighostBRSTCore, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, intrinsicBulkSmoothAntighostQuotientBRST_square_zero,
    (intrinsicBulkAntighostBRSTCoreEquiv period hPeriod couplings).map_zero]

theorem intrinsicBulkAntighostBRSTCore_intertwining
    (point : IntrinsicBulkSmoothAntighostBRSTQuotient period hPeriod) :
    (intrinsicBulkAntighostBRSTCore period hPeriod couplings
      (intrinsicBulkAntighostBRSTCoreEquiv period hPeriod couplings point) : Reduced) =
    intrinsicBulkAntighostQuotientRealization period hPeriod couplings
      (intrinsicBulkSmoothAntighostQuotientBRST period hPeriod point) := by
  have h := congrArg (fun source : IntrinsicBulkSmoothAntighostBRSTQuotient period hPeriod =>
    (intrinsicBulkAntighostBRSTCoreEquiv period hPeriod couplings
      (intrinsicBulkSmoothAntighostQuotientBRST period hPeriod source) : Reduced))
    ((intrinsicBulkAntighostBRSTCoreEquiv period hPeriod couplings).symm_apply_apply point)
  exact h

theorem intrinsicBulkAntighostBRSTCore_smooth (state : State) :
    (intrinsicBulkAntighostBRSTCore period hPeriod couplings
      (intrinsicBulkAntighostBRSTCoreEquiv period hPeriod couplings
        (intrinsicBulkSmoothAntighostQuotientMap period hPeriod state)) : Reduced) =
    intrinsicBulkAntighostQuotientMap period hPeriod couplings
      (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings
        (intrinsicBulkSmoothBRST period hPeriod state)) :=
  (intrinsicBulkAntighostBRSTCore_intertwining period hPeriod couplings
    (intrinsicBulkSmoothAntighostQuotientMap period hPeriod state)).trans
      (intrinsicBulkAntighostQuotientRealization_mk period hPeriod couplings
        (intrinsicBulkSmoothBRST period hPeriod state))

open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D P0EFTJanusReciprocalBimetricPotential

theorem intrinsicBulkAntighostQuotientRealization_pairing
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings + candidateAMinusEinsteinKineticWeight couplings = 0)
    (first second : State) :
    intrinsicBulkAntighostQuotientHessian period hPeriod couplings interactionScale coefficients hWeights
      (intrinsicBulkAntighostQuotientRealization period hPeriod couplings
        (intrinsicBulkSmoothAntighostQuotientMap period hPeriod first))
      (intrinsicBulkAntighostQuotientRealization period hPeriod couplings
        (intrinsicBulkSmoothAntighostQuotientMap period hPeriod second)) =
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings first)
      (intrinsicBulkSmoothBRSTInsertion period hPeriod couplings second) := by
  have h := congrArg₂ (fun left right : Reduced =>
    intrinsicBulkAntighostQuotientHessian period hPeriod couplings interactionScale coefficients hWeights left right)
    (intrinsicBulkAntighostQuotientRealization_mk period hPeriod couplings first)
    (intrinsicBulkAntighostQuotientRealization_mk period hPeriod couplings second)
  exact h.trans (intrinsicBulkAntighostQuotientHessian_mk period hPeriod couplings
    interactionScale coefficients hWeights _ _)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAntighostQuotientRealization4D
