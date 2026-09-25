import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBoundaryBulkHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryGHYAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryFixedParameterBase4D

/-! Bulk plus both genuine metric GHY contributions on the existing faithful
compatible core. The shared normal displacement is evaluated at parameter one. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryCompleteAction4D
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusProgramPT12IntrinsicBoundaryBulkHessian4D

section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
local instance : NormedAddCommGroup (E →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (E →L[Real] Real) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[Real] E →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (E →L[Real] E →L[Real] Real) := ContinuousLinearMap.toNormedSpace

private theorem linear_contDiffAt_zero (action : F → Real) (projection : E →L[Real] F)
    (hAction : ContDiffAt Real 2 action 0) :
    ContDiffAt Real 2 (fun x => action (projection x)) 0 := by
  have hAt : ContDiffAt Real 2 action (projection 0) := by simpa only [map_zero] using hAction
  exact hAt.comp 0 projection.contDiff.contDiffAt

private theorem secondDerivative_add (f g : E → Real)
    (hf : ContDiffAt Real 2 f 0) (hg : ContDiffAt Real 2 g 0) :
    scalarActionSecondDerivative (fun x => f x + g x) =
      scalarActionSecondDerivative f + scalarActionSecondDerivative g := by
  have hNearF : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt Real f x :=
    (hf.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))
  have hNearG : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt Real g x :=
    (hg.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))
  have hGradient : fderiv Real (fun x => f x + g x) =ᶠ[𝓝 (0 : E)]
      (fun x => fderiv Real f x + fderiv Real g x) := by
    filter_upwards [hNearF, hNearG] with x hF hG
    exact (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv
  have hF := (hf.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hG := (hg.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  exact hGradient.fderiv_eq.trans (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv

private theorem sumThree_contDiffAt_zero (f g h : E → Real)
    (hf : ContDiffAt Real 2 f 0) (hg : ContDiffAt Real 2 g 0) (hh : ContDiffAt Real 2 h 0) :
    ContDiffAt Real 2 (fun x => f x + g x + h x) 0 := (hf.add hg).add hh

private theorem secondDerivative_sumThree (f g h : E → Real)
    (hf : ContDiffAt Real 2 f 0) (hg : ContDiffAt Real 2 g 0) (hh : ContDiffAt Real 2 h 0) :
    scalarActionSecondDerivative (fun x => f x + g x + h x) =
      scalarActionSecondDerivative f + scalarActionSecondDerivative g + scalarActionSecondDerivative h :=
  (secondDerivative_add (fun x => f x + g x) h (hf.add hg) hh).trans
    (congrArg (fun K => K + scalarActionSecondDerivative h) (secondDerivative_add f g hf hg))

private theorem secondDerivative_sumThree_apply (f g h : E → Real)
    (hf : ContDiffAt Real 2 f 0) (hg : ContDiffAt Real 2 g 0) (hh : ContDiffAt Real 2 h 0)
    (first second : E) :
    scalarActionSecondDerivative (fun x => f x + g x + h x) first second =
      scalarActionSecondDerivative f first second + scalarActionSecondDerivative g first second +
        scalarActionSecondDerivative h first second := by
  rw [secondDerivative_sumThree f g h hf hg hh]
  rfl

private theorem secondDerivative_symmetric (f : E → Real) (hf : ContDiffAt Real 2 f 0) (x y : E) :
    scalarActionSecondDerivative f x y = scalarActionSecondDerivative f y x :=
  hf.isSymmSndFDerivAt (by norm_num) x y
end Calculus

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusOrientationDoubleCover P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBoundaryBulkCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryGHYAction4D
open P0EFTJanusProgramPT12FrameFreeBoundarySecondForm4D
open P0EFTJanusProgramPT12FrameFreeBoundaryFixedParameterBase4D
open P0EFTJanusReciprocalBimetricPotential

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
local instance : CompactSpace (CutThroatBoundary period hPeriod) :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
  Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert := InnerProductSpace.complexToReal
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "metric" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "Joint" => FrameFreeBoundaryJointCore period hPeriod frame metric
local instance : NormedAddCommGroup Joint := inferInstance
local instance : NormedSpace Real Joint := inferInstance

theorem zero_joint_one_mem_frameFreeBoundaryGHYDomain :
    ((0, 1) : Joint × Real) ∈ frameFreeBoundaryGHYDomain period hPeriod :=
  ⟨zero_joint_mem_frameFreeBoundarySecondFormDomain period hPeriod 1,
    zero_joint_mem_frameFreeBoundaryInducedVolumeDomain period hPeriod 1⟩

/-- The graph parameter is fixed; the normal field is the varying input. -/
def intrinsicBoundaryFixedGHYAction (einsteinScale : Real) (joint : Joint) : Real :=
  frameFreeBoundaryTwoSheetGHYAction period hPeriod einsteinScale (joint, 1)

theorem intrinsicBoundaryFixedGHYAction_contDiffAt_zero (einsteinScale : Real) :
    ContDiffAt Real 2 (intrinsicBoundaryFixedGHYAction period hPeriod einsteinScale) 0 := by
  have hBase := zero_joint_one_mem_frameFreeBoundaryGHYDomain period hPeriod
  have hAction := ((frameFreeBoundaryTwoSheetGHYAction_contDiffOn_two period hPeriod einsteinScale)
    (0, 1) hBase).contDiffAt ((frameFreeBoundaryGHYDomain_isOpen period hPeriod).mem_nhds hBase)
  exact hAction.comp 0 (contDiff_id.prodMk contDiff_const).contDiffAt

variable (couplings : GlobalCandidateAActionCouplings)
local notation "Core" => IntrinsicBoundaryBulkCore period hPeriod couplings
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
local instance coreBilinearNormedAddCommGroup : NormedAddCommGroup (Core →L[Real] Core →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : Add (Core →L[Real] Core →L[Real] Real) :=
  (coreBilinearNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAdd
local instance : NormedSpace Real (Core →L[Real] Core →L[Real] Real) := ContinuousLinearMap.toNormedSpace

def intrinsicBoundaryCompleteDomain : Set Core :=
  intrinsicBoundaryBulkDomain period hPeriod couplings ∩
    ((fun x => (intrinsicBoundaryBulkPlusJoint period hPeriod couplings x, (1 : Real))) ⁻¹'
      frameFreeBoundaryGHYDomain period hPeriod) ∩
    ((fun x => (intrinsicBoundaryBulkMinusJoint period hPeriod couplings x, (1 : Real))) ⁻¹'
      frameFreeBoundaryGHYDomain period hPeriod)

theorem intrinsicBoundaryCompleteDomain_isOpen : IsOpen (intrinsicBoundaryCompleteDomain period hPeriod couplings) :=
  ((intrinsicBoundaryBulkDomain_isOpen period hPeriod couplings).inter
    ((frameFreeBoundaryGHYDomain_isOpen period hPeriod).preimage
      ((intrinsicBoundaryBulkPlusJoint period hPeriod couplings).continuous.prodMk continuous_const))).inter
    ((frameFreeBoundaryGHYDomain_isOpen period hPeriod).preimage
      ((intrinsicBoundaryBulkMinusJoint period hPeriod couplings).continuous.prodMk continuous_const))

theorem intrinsicBoundaryCompleteDomain_zero_mem : (0 : Core) ∈ intrinsicBoundaryCompleteDomain period hPeriod couplings := by
  refine ⟨⟨intrinsicBoundaryBulkDomain_zero_mem period hPeriod couplings, ?_⟩, ?_⟩
  · change (intrinsicBoundaryBulkPlusJoint period hPeriod couplings 0, (1 : Real)) ∈
      frameFreeBoundaryGHYDomain period hPeriod
    simpa only [(intrinsicBoundaryBulkPlusJoint period hPeriod couplings).map_zero] using zero_joint_one_mem_frameFreeBoundaryGHYDomain period hPeriod
  · change (intrinsicBoundaryBulkMinusJoint period hPeriod couplings 0, (1 : Real)) ∈
      frameFreeBoundaryGHYDomain period hPeriod
    simpa only [(intrinsicBoundaryBulkMinusJoint period hPeriod couplings).map_zero] using zero_joint_one_mem_frameFreeBoundaryGHYDomain period hPeriod

def intrinsicBoundaryPlusGHYAction (einsteinScale : Real) (point : Core) : Real :=
  intrinsicBoundaryFixedGHYAction period hPeriod einsteinScale
    (intrinsicBoundaryBulkPlusJoint period hPeriod couplings point)
def intrinsicBoundaryMinusGHYAction (einsteinScale : Real) (point : Core) : Real :=
  intrinsicBoundaryFixedGHYAction period hPeriod einsteinScale
    (intrinsicBoundaryBulkMinusJoint period hPeriod couplings point)

theorem intrinsicBoundaryPlusGHYAction_contDiffAt_zero (einsteinScale : Real) :
    ContDiffAt Real 2 (intrinsicBoundaryPlusGHYAction period hPeriod couplings einsteinScale) 0 :=
  linear_contDiffAt_zero (intrinsicBoundaryFixedGHYAction period hPeriod einsteinScale)
    (intrinsicBoundaryBulkPlusJoint period hPeriod couplings)
    (intrinsicBoundaryFixedGHYAction_contDiffAt_zero period hPeriod einsteinScale)
theorem intrinsicBoundaryMinusGHYAction_contDiffAt_zero (einsteinScale : Real) :
    ContDiffAt Real 2 (intrinsicBoundaryMinusGHYAction period hPeriod couplings einsteinScale) 0 :=
  linear_contDiffAt_zero (intrinsicBoundaryFixedGHYAction period hPeriod einsteinScale)
    (intrinsicBoundaryBulkMinusJoint period hPeriod couplings)
    (intrinsicBoundaryFixedGHYAction_contDiffAt_zero period hPeriod einsteinScale)

variable (plusEinsteinScale minusEinsteinScale interactionScale : Real) (coefficients : PotentialCoefficients)

def intrinsicBoundaryCompleteAction (point : Core) : Real :=
  intrinsicBoundaryBulkAction period hPeriod couplings interactionScale coefficients point +
    intrinsicBoundaryPlusGHYAction period hPeriod couplings plusEinsteinScale point +
    intrinsicBoundaryMinusGHYAction period hPeriod couplings minusEinsteinScale point

theorem intrinsicBoundaryCompleteAction_contDiffAt_zero :
    ContDiffAt Real 2 (intrinsicBoundaryCompleteAction period hPeriod couplings
      plusEinsteinScale minusEinsteinScale interactionScale coefficients) 0 :=
  sumThree_contDiffAt_zero _ _ _
    (intrinsicBoundaryBulkAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)
    (intrinsicBoundaryPlusGHYAction_contDiffAt_zero period hPeriod couplings plusEinsteinScale)
    (intrinsicBoundaryMinusGHYAction_contDiffAt_zero period hPeriod couplings minusEinsteinScale)

def intrinsicBoundaryCompleteHessian : Core →L[Real] Core →L[Real] Real :=
  scalarActionSecondDerivative (intrinsicBoundaryCompleteAction period hPeriod couplings
    plusEinsteinScale minusEinsteinScale interactionScale coefficients)

theorem intrinsicBoundaryCompleteHessian_eq_sum :
    intrinsicBoundaryCompleteHessian period hPeriod couplings
        plusEinsteinScale minusEinsteinScale interactionScale coefficients =
      intrinsicBoundaryBulkHessian period hPeriod couplings interactionScale coefficients +
        scalarActionSecondDerivative (intrinsicBoundaryPlusGHYAction period hPeriod couplings plusEinsteinScale) +
        scalarActionSecondDerivative (intrinsicBoundaryMinusGHYAction period hPeriod couplings minusEinsteinScale) :=
  secondDerivative_sumThree _ _ _
    (intrinsicBoundaryBulkAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)
    (intrinsicBoundaryPlusGHYAction_contDiffAt_zero period hPeriod couplings plusEinsteinScale)
    (intrinsicBoundaryMinusGHYAction_contDiffAt_zero period hPeriod couplings minusEinsteinScale)

theorem intrinsicBoundaryCompleteHessian_apply (first second : Core) :
    intrinsicBoundaryCompleteHessian period hPeriod couplings
        plusEinsteinScale minusEinsteinScale interactionScale coefficients first second =
      intrinsicBoundaryBulkHessian period hPeriod couplings interactionScale coefficients first second +
        scalarActionSecondDerivative (intrinsicBoundaryPlusGHYAction period hPeriod couplings plusEinsteinScale) first second +
        scalarActionSecondDerivative (intrinsicBoundaryMinusGHYAction period hPeriod couplings minusEinsteinScale) first second :=
  secondDerivative_sumThree_apply _ _ _
    (intrinsicBoundaryBulkAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)
    (intrinsicBoundaryPlusGHYAction_contDiffAt_zero period hPeriod couplings plusEinsteinScale)
    (intrinsicBoundaryMinusGHYAction_contDiffAt_zero period hPeriod couplings minusEinsteinScale) first second

theorem intrinsicBoundaryCompleteHessian_symmetric (first second : Core) :
    intrinsicBoundaryCompleteHessian period hPeriod couplings
        plusEinsteinScale minusEinsteinScale interactionScale coefficients first second =
      intrinsicBoundaryCompleteHessian period hPeriod couplings
        plusEinsteinScale minusEinsteinScale interactionScale coefficients second first :=
  secondDerivative_symmetric _
    (intrinsicBoundaryCompleteAction_contDiffAt_zero period hPeriod couplings
      plusEinsteinScale minusEinsteinScale interactionScale coefficients) first second

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryCompleteAction4D
