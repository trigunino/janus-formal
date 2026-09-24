import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAbelianBRestriction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalGhostCancellation4D

/-! Shared diffeomorphism ghosts in the inhabited intrinsic bulk core.
Opposite Einstein weights annihilate their full bulk Hessian column. The
physical matter/LL readout is recorded separately; no H11 extension, domain
equality, quotient, or Fredholm conclusion is installed here. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTDensity4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusReciprocalBimetricPotential
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
local notation "geometry" => intrinsicBulkGeometry period hPeriod
abbrev IntrinsicBulkDiffeomorphismGhostCore := FiniteFrameDiffeomorphismC2Core period hPeriod frame
local notation "Ghost" => IntrinsicBulkDiffeomorphismGhostCore period hPeriod
local notation "Packet" => FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame
local instance ghostNormedAddCommGroup : NormedAddCommGroup Ghost := inferInstance
local instance ghostNormedSpace : NormedSpace Real Ghost := inferInstance
local instance ghostAddZeroClass : AddZeroClass Ghost := inferInstance
local instance packetNormedAddCommGroup : NormedAddCommGroup Packet := inferInstance
local instance packetNormedSpace : NormedSpace Real Packet := inferInstance
variable (couplings : GlobalCandidateAActionCouplings)
local instance coreNormedAddCommGroup : NormedAddCommGroup
    (IntrinsicBulkCore period hPeriod couplings) := inferInstance
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod geometry frame couplings
local notation "Core" => IntrinsicBulkCore period hPeriod couplings
local instance coreAddZeroClass : AddZeroClass Core :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass

def intrinsicBulkDiffeomorphismInsertion : Packet →L[Real] Core :=
  let physical : Packet →L[Real] FiniteFramePairedC2PhysicalCore period hPeriod geometry frame :=
    (0 : Packet →L[Real] _).prod ((0 : Packet →L[Real] _).prod (ContinuousLinearMap.id Real Packet))
  (physical.prod 0).prod 0

@[simp] theorem intrinsicBulkDiffeomorphismInsertion_apply (fields : Packet) :
    intrinsicBulkDiffeomorphismInsertion period hPeriod couplings fields =
      (((0, (0, fields)), 0), 0) := rfl

def intrinsicBulkDiffeomorphismGhostInsertion : Ghost →L[Real] Core :=
  (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings).comp
    ((0 : Ghost →L[Real] Ghost).prod
      ((0 : Ghost →L[Real] Ghost).prod (ContinuousLinearMap.id Real Ghost)))

@[simp] theorem intrinsicBulkDiffeomorphismGhostInsertion_apply (ghost : Ghost) :
    intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost =
      intrinsicBulkDiffeomorphismInsertion period hPeriod couplings (0, (0, ghost)) := rfl

theorem intrinsicBulkDiffeomorphismGhostInsertion_injective :
    Function.Injective (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings) := by
  intro first second h
  exact congrArg (fun input : Core => input.1.1.2.2.2.2) h

/-- The ghost insertion has zero matter and LL readout, relevant to the H11 bridge. -/
theorem intrinsicBulkDiffeomorphismGhostInsertion_matterLL_zero (ghost : Ghost) :
    ((intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost).1.2,
      (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost).2) = (0, 0) := rfl

/-- Metric, Abelian/Maxwell, matter and LL slots are all zero on this insertion. -/
theorem intrinsicBulkDiffeomorphismGhostInsertion_physical_zero (ghost : Ghost) :
    (((intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost).1.1.1,
        (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost).1.1.2.1),
      ((intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost).1.2,
        (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost).2)) =
      ((0, 0), (0, 0)) := rfl

def intrinsicSmoothDiffeomorphismGhostCoefficients :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real] Ghost where
  toFun ghost := finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame
    (intrinsicBulkGeometry period hPeriod).plusMetric ghost.field
  map_add' first second := by
    funext index
    change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod _ =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod _ +
        smoothToCanonicalPhysicalScalarC2JetCore period hPeriod _
    rw [← map_add]
    apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    simp only [generalMetricFiniteFrameCoefficient_apply]
    exact map_add (generalMetricFiniteFrameCoefficientAt period hPeriod frame
      (intrinsicBulkGeometry period hPeriod).plusMetric point index) (first.field point) (second.field point)
  map_smul' scalar ghost := by
    funext index
    change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod _ =
      scalar • smoothToCanonicalPhysicalScalarC2JetCore period hPeriod _
    rw [← map_smul]
    apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    simp only [generalMetricFiniteFrameCoefficient_apply]
    exact map_smul (generalMetricFiniteFrameCoefficientAt period hPeriod frame
      (intrinsicBulkGeometry period hPeriod).plusMetric point index) scalar (ghost.field point)

def intrinsicBulkSmoothDiffeomorphismGhostInsertion :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real] Core :=
  (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings).toLinearMap.comp
    (intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod)

/-- Reconstruction makes this an injection of actual tangent ghosts, not redundant coordinates. -/
theorem intrinsicBulkSmoothDiffeomorphismGhostInsertion_injective :
    Function.Injective (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings) := by
  intro first second h
  have hCoefficients := intrinsicBulkDiffeomorphismGhostInsertion_injective period hPeriod couplings h
  change finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame (intrinsicBulkGeometry period hPeriod).plusMetric first.field =
    finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame (intrinsicBulkGeometry period hPeriod).plusMetric second.field at hCoefficients
  apply GlobalDiffeomorphismGhostField.ext
  apply ContMDiffSection.ext
  intro point
  rw [← finiteFrameSmoothDiffeomorphismC2Coefficients_reconstructs period hPeriod frame
      (intrinsicBulkGeometry period hPeriod).plusMetric first.field point,
    ← finiteFrameSmoothDiffeomorphismC2Coefficients_reconstructs period hPeriod frame
      (intrinsicBulkGeometry period hPeriod).plusMetric second.field point, hCoefficients]

def intrinsicBulkEraseDiffeomorphismAntighost : Core →L[Real] Core where
  toFun input := (((input.1.1.1, (input.1.1.2.1,
    (input.1.1.2.2.1, (0, input.1.1.2.2.2.2)))), input.1.2), input.2)
  map_add' _ _ := by simp [Prod.mk_add_mk]
  map_smul' _ _ := by simp [Prod.smul_mk]
  cont := by fun_prop

def intrinsicBulkEraseDiffeomorphismGhost : Core →L[Real] Core where
  toFun input := (((input.1.1.1, (input.1.1.2.1,
    (input.1.1.2.2.1, (input.1.1.2.2.2.1, 0)))), input.1.2), input.2)
  map_add' _ _ := by simp [Prod.mk_add_mk]
  map_smul' _ _ := by simp [Prod.smul_mk]
  cont := by fun_prop

@[simp] theorem intrinsicBulkEraseDiffeomorphismAntighost_apply (input : Core) :
    intrinsicBulkEraseDiffeomorphismAntighost period hPeriod couplings input =
      (((input.1.1.1, (input.1.1.2.1,
        (input.1.1.2.2.1, (0, input.1.1.2.2.2.2)))), input.1.2), input.2) := rfl

@[simp] theorem intrinsicBulkEraseDiffeomorphismGhost_apply (input : Core) :
    intrinsicBulkEraseDiffeomorphismGhost period hPeriod couplings input =
      (((input.1.1.1, (input.1.1.2.1,
        (input.1.1.2.2.1, (input.1.1.2.2.2.1, 0)))), input.1.2), input.2) := rfl

theorem intrinsicBulkEraseAntighost_ghost (ghost : Ghost) :
    intrinsicBulkEraseDiffeomorphismAntighost period hPeriod couplings
      (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost) =
      intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost := rfl

theorem intrinsicBulkEraseGhost_ghost (ghost : Ghost) :
    intrinsicBulkEraseDiffeomorphismGhost period hPeriod couplings
      (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost) = 0 := rfl

theorem intrinsicBulkAntighost_decomposition (test : Core) :
    intrinsicBulkEraseDiffeomorphismAntighost period hPeriod couplings test +
      intrinsicBulkDiffeomorphismInsertion period hPeriod couplings
        (0, (test.1.1.2.2.2.1, 0)) = test := by
  simp only [intrinsicBulkEraseDiffeomorphismAntighost_apply,
    intrinsicBulkDiffeomorphismInsertion_apply, Prod.mk_add_mk, add_zero, zero_add]

private theorem nonminimalTransition_noAntighost (field ghost : Ghost) :
    finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod frame frame
        (intrinsicBulkGeometry period hPeriod).plusMetric (field, (0, ghost)) =
      (finiteFrameDiffeomorphismC2Transition period hPeriod frame frame
          (intrinsicBulkGeometry period hPeriod).plusMetric field,
        (0, finiteFrameDiffeomorphismC2Transition period hPeriod frame frame
          (intrinsicBulkGeometry period hPeriod).plusMetric ghost)) := by
  let transition : Ghost →L[Real] Ghost := finiteFrameDiffeomorphismC2Transition
    period hPeriod frame frame (intrinsicBulkGeometry period hPeriod).plusMetric
  change (transition field, (transition (0 : Ghost), transition ghost)) = _
  rw [transition.map_zero]

private theorem sectorAction_noAntighost (metric tensor :
    P0EFTJanusProgramPGeneralMetricC2OpenDomain4D.GeneralMetricRelativeC2Core
      period hPeriod frame (intrinsicBulkGeometry period hPeriod).plusMetric) (field ghost : Ghost) :
    finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame (intrinsicBulkGeometry period hPeriod).plusMetric
        (metric, (tensor, (field, (0, ghost)))) =
      finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame (intrinsicBulkGeometry period hPeriod).plusMetric
        (metric, (tensor, (field, (0, 0)))) := by
  have hReadout := (finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame).map_zero
  simp only [finiteFrameC2DiffeomorphismBRSTAction, finiteFrameC2DiffeomorphismBRSTDensity,
    finiteFrameDiffeomorphismBRSTAttachNonminimalC2_apply,
    finiteFrameC2DiffeomorphismBRSTOperatorFeatures, finiteFrameDiffeomorphismBRSTC0Polynomial,
    hReadout, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]

variable (interactionScale : Real) (coefficients : PotentialCoefficients)

theorem intrinsicBulkAction_noAntighost_eraseGhost (input : Core) :
    intrinsicBulkAction period hPeriod couplings interactionScale coefficients
        (intrinsicBulkEraseDiffeomorphismAntighost period hPeriod couplings input) =
      intrinsicBulkAction period hPeriod couplings interactionScale coefficients
        (intrinsicBulkEraseDiffeomorphismGhost period hPeriod couplings
          (intrinsicBulkEraseDiffeomorphismAntighost period hPeriod couplings input)) := by
  simp only [intrinsicBulkAction, intrinsicBulkEraseDiffeomorphismAntighost_apply,
    intrinsicBulkEraseDiffeomorphismGhost_apply, finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterAction, finiteFramePairedC2PhysicalMaxwellAction,
    finiteFramePairedC2PhysicalAction, finiteFramePairedC2EinsteinBRSTAction,
    finiteFramePairedC2FullBRSTGaugeAction, finiteFramePairedC2PhysicalRecenter,
    finiteFramePairedC2PhysicalMaxwellProjection_apply,
    finiteFramePairedC2FullBRSTGaugeAbelianProjection_apply,
    finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection_apply,
    finiteFramePairedDiffeomorphismBRSTAction,
    finiteFramePairedDiffeomorphismBRSTPlusInput_apply, finiteFramePairedDiffeomorphismBRSTMinusInput_apply,
    finiteFrameSharedMetricDiffeomorphismBRSTInput_apply,
    nonminimalTransition_noAntighost, sectorAction_noAntighost]

variable (hWeights : candidateAPlusEinsteinKineticWeight couplings +
  candidateAMinusEinsteinKineticWeight couplings = 0)

include hWeights in
private theorem pairedAction_shared_zero (fields : Packet) :
    finiteFramePairedDiffeomorphismBRSTAction period hPeriod frame frame frame
      (intrinsicBulkGeometry period hPeriod).plusMetric (intrinsicBulkGeometry period hPeriod).plusMetric couplings ((0, 0), fields) = 0 := by
  simp only [finiteFramePairedDiffeomorphismBRSTAction,
    finiteFramePairedDiffeomorphismBRSTPlusInput_apply, finiteFramePairedDiffeomorphismBRSTMinusInput_apply]
  rw [← add_mul, hWeights, zero_mul]

include hWeights in
theorem intrinsicBulkAction_sharedDiffeomorphism_restriction (fields : Packet) :
    intrinsicBulkAction period hPeriod couplings interactionScale coefficients
        (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings fields) =
      intrinsicBulkAction period hPeriod couplings interactionScale coefficients 0 := by
  simp [intrinsicBulkAction, intrinsicBulkDiffeomorphismInsertion_apply,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterAction, finiteFramePairedC2PhysicalMaxwellAction,
    finiteFramePairedC2PhysicalAction, finiteFramePairedC2EinsteinBRSTAction,
    finiteFramePairedC2FullBRSTGaugeAction, finiteFramePairedC2PhysicalRecenter,
    intrinsicBulkMinusCenter_eq_zero, finiteFramePairedC2PhysicalMaxwellProjection_apply,
    finiteFramePairedC2FullBRSTGaugeAbelianProjection_apply,
    finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection_apply,
    pairedAction_shared_zero period hPeriod couplings hWeights]

include hWeights in
theorem intrinsicBulkHessian_sharedDiffeomorphism_zero (first second : Packet) :
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
        (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings first)
        (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings second) = 0 := by
  rw [← intrinsicBulkHessian_linear_pullback period hPeriod couplings interactionScale coefficients
    (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings) first second]
  have hFunction := funext (intrinsicBulkAction_sharedDiffeomorphism_restriction
    period hPeriod couplings interactionScale coefficients hWeights)
  rw [hFunction]
  simp

theorem intrinsicBulkHessian_ghost_noAntighost_zero (ghost : Ghost) (test : Core) :
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
        (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost)
        (intrinsicBulkEraseDiffeomorphismAntighost period hPeriod couplings test) = 0 := by
  let eraseBar := intrinsicBulkEraseDiffeomorphismAntighost period hPeriod couplings
  let eraseGhost := intrinsicBulkEraseDiffeomorphismGhost period hPeriod couplings
  have hFunction : (fun input : Core => intrinsicBulkAction period hPeriod couplings
      interactionScale coefficients (eraseBar input)) =
      (fun input : Core => intrinsicBulkAction period hPeriod couplings interactionScale coefficients
        ((eraseGhost.comp eraseBar) input)) :=
    funext (intrinsicBulkAction_noAntighost_eraseGhost period hPeriod couplings interactionScale coefficients)
  have h := congrArg (fun action : Core → Real => fderiv Real (fderiv Real action) 0
    (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost) test) hFunction
  have hL := intrinsicBulkHessian_linear_pullback period hPeriod couplings interactionScale coefficients
    eraseBar (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost) test
  have hR := intrinsicBulkHessian_linear_pullback period hPeriod couplings interactionScale coefficients
    (eraseGhost.comp eraseBar)
    (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost) test
  have hTransport := hL.symm.trans (h.trans hR)
  dsimp only [eraseBar, eraseGhost] at hTransport
  simp only [ContinuousLinearMap.comp_apply,
    intrinsicBulkEraseAntighost_ghost period hPeriod couplings ghost,
    intrinsicBulkEraseGhost_ghost period hPeriod couplings ghost] at hTransport
  have hZero := congrArg (fun operator : Core →L[Real] Real =>
    operator (eraseGhost (eraseBar test)))
    (intrinsicBulkHessian period hPeriod couplings interactionScale coefficients).map_zero
  exact hTransport.trans hZero

include hWeights in
/-- Vanishing against every bulk test, not merely an isotropic self-pairing. -/
theorem intrinsicBulkHessian_diagonalGhost_column_zero (ghost : Ghost) (test : Core) :
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost) test = 0 := by
  have hAntighost : intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost)
      (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings (0, (test.1.1.2.2.2.1, 0))) = 0 :=
    intrinsicBulkHessian_sharedDiffeomorphism_zero period hPeriod couplings
    interactionScale coefficients hWeights (0, (0, ghost)) (0, (test.1.1.2.2.2.1, 0))
  have hRow := (intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
    (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost)).map_add
      (intrinsicBulkEraseDiffeomorphismAntighost period hPeriod couplings test)
      (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings (0, (test.1.1.2.2.2.1, 0)))
  have hDecomposition := congrArg
    (intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost))
    (intrinsicBulkAntighost_decomposition period hPeriod couplings test)
  have hParts := congrArg₂ (fun first second : Real => first + second)
    (intrinsicBulkHessian_ghost_noAntighost_zero period hPeriod couplings
      interactionScale coefficients ghost test) hAntighost
  exact hDecomposition.symm.trans (hRow.trans (hParts.trans (zero_add (0 : Real))))

include hWeights in
theorem intrinsicBulkHessian_smoothDiagonalGhost_column_zero
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) (test : Core) :
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings ghost) test = 0 :=
  intrinsicBulkHessian_diagonalGhost_column_zero period hPeriod couplings interactionScale coefficients
    hWeights (intrinsicSmoothDiffeomorphismGhostCoefficients period hPeriod ghost) test

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
