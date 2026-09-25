import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBoundaryAbelianGhostCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBoundaryCompleteAction4D

/-! The faithful Abelian ghost insertion represents the second variation of
the complete bulk + two GHY actions by the existing self-adjoint L² ghost block. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryAbelianGhostPairing4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusProgramPT12IntrinsicBoundaryBulkHessian4D

private theorem secondDerivative_linear_zero_left
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (action : F → Real) (projection : E →L[Real] F)
    (hC2 : ContDiffAt Real 2 action 0) (first second : E) (hFirst : projection first = 0) :
    scalarActionSecondDerivative (fun point => action (projection point)) first second = 0 := by
  rw [scalarActionSecondDerivative_linear_pullback action projection hC2 first second,
    hFirst, (scalarActionSecondDerivative action).map_zero, zero_apply]

private theorem eq_add_apply_drop_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {total physical brst : E →L[Real] E →L[Real] Real}
    (hTotal : total = physical + brst) (first second : E)
    (hPhysical : physical first second = 0) :
    total first second = brst first second := by
  rw [hTotal]
  simp only [_root_.add_apply, hPhysical, zero_add]

private theorem scalar_sum_drop {total bulk plus minus : Real}
    (hTotal : total = bulk + plus + minus) (hPlus : plus = 0) (hMinus : minus = 0) :
    total = bulk := by
  rw [hTotal, hPlus, hMinus, add_zero, add_zero]

private theorem zero_of_range {E X : Type*} (f : E → Real) (insertion : X → E) (point : E)
    (hRange : ∃ fields, point = insertion fields) (hZero : ∀ fields, f (insertion fields) = 0) :
    f point = 0 := by
  obtain ⟨fields, rfl⟩ := hRange
  exact hZero fields

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D P0EFTJanusProgramPT12GhostRotationDefect4D
open P0EFTJanusProgramPT12FrameFreeAbelianGhostSelfAdjoint4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothAbelianBRSTCore4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianGhostPairing4D
open P0EFTJanusProgramPT12IntrinsicBoundaryBulkCore4D
open P0EFTJanusProgramPT12IntrinsicBoundaryCompleteAction4D
open P0EFTJanusProgramPT12IntrinsicBoundaryAbelianGhostCore4D
open P0EFTJanusReciprocalBimetricPotential

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
variable (couplings : GlobalCandidateAActionCouplings)
local notation "Bulk" => IntrinsicBulkCore period hPeriod couplings
local notation "Core" => IntrinsicBoundaryBulkCore period hPeriod couplings
local notation "base" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local instance bulkNormedAddCommGroup : NormedAddCommGroup Bulk := inferInstance
local instance : SeminormedAddCommGroup Bulk :=
  (bulkNormedAddCommGroup period hPeriod couplings).toSeminormedAddCommGroup
local instance bulkNormedSpace : NormedSpace Real Bulk :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings
local instance : NormedAddCommGroup (Bulk →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Bulk →L[Real] Real) := ContinuousLinearMap.toNormedSpace
local instance coreNormedAddCommGroup : NormedAddCommGroup Core :=
  intrinsicBoundaryBulkCoreNormedAddCommGroup period hPeriod couplings
local instance : SeminormedAddCommGroup Core :=
  (coreNormedAddCommGroup period hPeriod couplings).toSeminormedAddCommGroup
local instance : AddCommGroup Core :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup
local instance : AddZeroClass Core :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance coreNormedSpace : NormedSpace Real Core :=
  intrinsicBoundaryBulkCoreNormedSpace period hPeriod couplings
local instance : Module Real Core := (coreNormedSpace period hPeriod couplings).toModule
local instance coreDualNormedAddCommGroup : NormedAddCommGroup (Core →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : SeminormedAddCommGroup (Core →L[Real] Real) :=
  (coreDualNormedAddCommGroup period hPeriod couplings).toSeminormedAddCommGroup
local instance : AddCommGroup (Core →L[Real] Real) :=
  (coreDualNormedAddCommGroup period hPeriod couplings).toAddCommGroup
local instance coreDualNormedSpace : NormedSpace Real (Core →L[Real] Real) := ContinuousLinearMap.toNormedSpace
local instance : Module Real (Core →L[Real] Real) := (coreDualNormedSpace period hPeriod couplings).toModule
local instance coreBilinearNormedAddCommGroup : NormedAddCommGroup (Core →L[Real] Core →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : Add (Core →L[Real] Core →L[Real] Real) :=
  (coreBilinearNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAdd
local instance : NormedSpace Real (Core →L[Real] Core →L[Real] Real) := ContinuousLinearMap.toNormedSpace

theorem intrinsicBoundaryPlusGHYHessian_ghost_zero (einsteinScale : Real)
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) (test : Core) :
    scalarActionSecondDerivative (intrinsicBoundaryPlusGHYAction period hPeriod couplings einsteinScale)
      (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings antighost ghost) test = 0 :=
  secondDerivative_linear_zero_left (intrinsicBoundaryFixedGHYAction period hPeriod einsteinScale)
    (intrinsicBoundaryBulkPlusJoint period hPeriod couplings)
    (intrinsicBoundaryFixedGHYAction_contDiffAt_zero period hPeriod einsteinScale) _ test
    (intrinsicBoundarySmoothAbelianGhostInsertion_plusJoint period hPeriod couplings antighost ghost)

theorem intrinsicBoundaryMinusGHYHessian_ghost_zero (einsteinScale : Real)
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) (test : Core) :
    scalarActionSecondDerivative (intrinsicBoundaryMinusGHYAction period hPeriod couplings einsteinScale)
      (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings antighost ghost) test = 0 :=
  secondDerivative_linear_zero_left (intrinsicBoundaryFixedGHYAction period hPeriod einsteinScale)
    (intrinsicBoundaryBulkMinusJoint period hPeriod couplings)
    (intrinsicBoundaryFixedGHYAction_contDiffAt_zero period hPeriod einsteinScale) _ test
    (intrinsicBoundarySmoothAbelianGhostInsertion_minusJoint period hPeriod couplings antighost ghost)

variable (plusEinsteinScale minusEinsteinScale interactionScale : Real) (coefficients : PotentialCoefficients)

private theorem completeGhost_eq_boundaryBulk
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) (test : Core) :
    intrinsicBoundaryCompleteHessian period hPeriod couplings
        plusEinsteinScale minusEinsteinScale interactionScale coefficients
        (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings antighost ghost) test =
      intrinsicBoundaryBulkHessian period hPeriod couplings interactionScale coefficients
        (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings antighost ghost) test := by
  have hSum := intrinsicBoundaryCompleteHessian_apply period hPeriod couplings
    plusEinsteinScale minusEinsteinScale interactionScale coefficients
    (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings antighost ghost) test
  have hPlus := intrinsicBoundaryPlusGHYHessian_ghost_zero period hPeriod couplings
    plusEinsteinScale antighost ghost test
  have hMinus := intrinsicBoundaryMinusGHYHessian_ghost_zero period hPeriod couplings
    minusEinsteinScale antighost ghost test
  have h := scalar_sum_drop hSum hPlus hMinus
  exact h

theorem intrinsicBoundaryCompleteHessian_ghost_eq_bulk
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) (test : Core) :
    intrinsicBoundaryCompleteHessian period hPeriod couplings
        plusEinsteinScale minusEinsteinScale interactionScale coefficients
        (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings antighost ghost) test =
      intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
        (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
          (pureAbelianGhostPair period hPeriod antighost ghost))
        (intrinsicBoundaryBulkProjection period hPeriod couplings test) := by
  have hBoundary := completeGhost_eq_boundaryBulk period hPeriod couplings
    plusEinsteinScale minusEinsteinScale interactionScale coefficients antighost ghost test
  have hBulk := intrinsicBoundaryBulkAction_hessian period hPeriod couplings interactionScale coefficients
    (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings antighost ghost) test
  exact hBoundary.trans hBulk

private theorem physicalGhost_zero
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) (test : Bulk) :
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
        (pureAbelianGhostPair period hPeriod antighost ghost)) test = 0 := by
  have hRange := intrinsicBulkSmoothGhostPair_mem_nonminimal period hPeriod couplings antighost ghost
  have h := zero_of_range
    (fun point : Bulk => intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients point test)
    (intrinsicBulkAbelianNonminimalInsertion period hPeriod couplings)
    (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
      (pureAbelianGhostPair period hPeriod antighost ghost)) hRange
    (fun fields => intrinsicBulkPhysicalHessian_abelianNonminimal_zero
      period hPeriod couplings interactionScale coefficients fields test)
  exact h

private theorem bulkGhost_eq_BRST
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) (test : Bulk) :
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
        (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
          (pureAbelianGhostPair period hPeriod antighost ghost)) test =
      intrinsicBulkBRSTHessian period hPeriod couplings
        (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
          (pureAbelianGhostPair period hPeriod antighost ghost)) test := by
  have hSum := intrinsicBulkHessian_eq_physical_add_BRST period hPeriod couplings interactionScale coefficients
  have hPhysical := physicalGhost_zero period hPeriod couplings interactionScale coefficients antighost ghost test
  have h := eq_add_apply_drop_left hSum
    (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
      (pureAbelianGhostPair period hPeriod antighost ghost)) test hPhysical
  exact h

theorem intrinsicBoundaryCompleteHessian_ghost_eq_BRST
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) (test : Core) :
    intrinsicBoundaryCompleteHessian period hPeriod couplings
        plusEinsteinScale minusEinsteinScale interactionScale coefficients
        (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings antighost ghost) test =
      intrinsicBulkBRSTHessian period hPeriod couplings
        (intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings
          (pureAbelianGhostPair period hPeriod antighost ghost))
        (intrinsicBoundaryBulkProjection period hPeriod couplings test) := by
  have hBulk := intrinsicBoundaryCompleteHessian_ghost_eq_bulk period hPeriod couplings
    plusEinsteinScale minusEinsteinScale interactionScale coefficients antighost ghost test
  have hBRST := bulkGhost_eq_BRST period hPeriod couplings interactionScale coefficients antighost ghost
    (intrinsicBoundaryBulkProjection period hPeriod couplings test)
  exact hBulk.trans hBRST

theorem intrinsicBoundaryCompleteHessian_ghost_eq_L2_pairing
    (a c b d : GlobalPairedGaugeLieSmooth period hPeriod) :
    intrinsicBoundaryCompleteHessian period hPeriod couplings
      plusEinsteinScale minusEinsteinScale interactionScale coefficients
      (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings a c)
      (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings b d) =
    inner Real (frameFreeAbelianGhostOperator period hPeriod (fun _ => base)
        (frameFreeAbelianGhostSmoothDomain period hPeriod (fun _ => base) a c))
      (WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod b,
        globalPairedGaugeLieL2LinearMap period hPeriod d)) :=
  (intrinsicBoundaryCompleteHessian_ghost_eq_BRST period hPeriod couplings
    plusEinsteinScale minusEinsteinScale interactionScale coefficients a c
    (intrinsicBoundarySmoothAbelianGhostInsertion period hPeriod couplings b d)).trans
    (intrinsicBulkBRSTHessian_ghost_eq_L2_pairing period hPeriod couplings a c b d)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryAbelianGhostPairing4D
