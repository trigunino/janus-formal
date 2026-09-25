import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D

/-! Exact decomposition into the identified physical bulk and the native BRST
action, including their genuine second derivatives. Boundary GHY is separate. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff Topology

private theorem scalar_split (e g i m s l : Real) :
    e + g + i + m + s + l = (e + i + m + s + l) + g := by ring

private theorem contDiffAt_linear_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f : E → Real) (projection : E →L[Real] E) (hf : ContDiffAt Real 2 f 0) :
    ContDiffAt Real 2 (fun x => f (projection x)) 0 := by
  have hAt : ContDiffAt Real 2 f (projection 0) := by
    simpa only [projection.map_zero] using hf
  exact hAt.comp 0 projection.contDiff.contDiffAt

private theorem contDiffAt_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f p g : E → Real) (hSplit : ∀ x, f x = p x + g x)
    (hf : ContDiffAt Real 2 f 0) (hp : ContDiffAt Real 2 p 0) :
    ContDiffAt Real 2 g 0 := by
  have hFunction : g = fun x => f x - p x := by
    funext x
    linarith [hSplit x]
  rw [hFunction]
  exact hf.sub hp

private theorem second_fderiv_of_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f p g : E → Real) (hSplit : ∀ x, f x = p x + g x)
    (hp : ContDiffAt Real 2 p 0) (hg : ContDiffAt Real 2 g 0) :
    fderiv Real (fderiv Real f) 0 =
      fderiv Real (fderiv Real p) 0 + fderiv Real (fderiv Real g) 0 := by
  have hFunction : f = fun x => p x + g x := funext hSplit
  have hNearP : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt Real p x :=
    (hp.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))
  have hNearG : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt Real g x :=
    (hg.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))
  have hGradient : fderiv Real f =ᶠ[𝓝 (0 : E)]
      (fun x => fderiv Real p x + fderiv Real g x) := by
    filter_upwards [hNearP, hNearG] with x hP hG
    rw [hFunction]
    exact (hP.hasFDerivAt.add hG.hasFDerivAt).fderiv
  have hSecondP := (hp.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt
    (by norm_num)
  have hSecondG := (hg.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt
    (by norm_num)
  exact hGradient.fderiv_eq.trans (hSecondP.hasFDerivAt.add hSecondG.hasFDerivAt).fderiv

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalProjection4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D
open P0EFTJanusReciprocalBimetricPotential
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
variable (couplings : GlobalCandidateAActionCouplings)
local instance coreNormedAddCommGroup : NormedAddCommGroup (IntrinsicBulkCore period hPeriod couplings) := inferInstance
local instance : AddZeroClass (IntrinsicBulkCore period hPeriod couplings) :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings

/-- The native paired Abelian and diagonal diffeomorphism action, on unchanged fields. -/
def intrinsicBulkBRSTAction (input : IntrinsicBulkCore period hPeriod couplings) : Real :=
  finiteFramePairedC2FullBRSTGaugeAction period hPeriod
    (finiteSmoothTangentFrame period hPeriod) (finiteSmoothTangentFrame period hPeriod)
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicBulkGeometry period hPeriod).plusMetric (intrinsicBulkGeometry period hPeriod).plusMetric
    couplings input.1.1

theorem intrinsicBulkAction_eq_physical_add_BRST (interactionScale : Real)
    (coefficients : PotentialCoefficients) (input : IntrinsicBulkCore period hPeriod couplings) :
    intrinsicBulkAction period hPeriod couplings interactionScale coefficients input =
      intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients input +
        intrinsicBulkBRSTAction period hPeriod couplings input := by
  simp only [intrinsicBulkPhysicalAction_eq_summands, intrinsicBulkBRSTAction, intrinsicBulkAction,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterAction, finiteFramePairedC2PhysicalMaxwellAction,
    finiteFramePairedC2PhysicalAction, finiteFramePairedC2EinsteinBRSTAction,
    finiteFramePairedC2PhysicalRecenter, intrinsicBulkMinusCenter_eq_zero, zero_add]
  exact scalar_split _ _ _ _ _ _

theorem intrinsicBulkPhysicalAction_contDiffAt_zero (interactionScale : Real)
    (coefficients : PotentialCoefficients) :
    ContDiffAt Real 2 (intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients) 0 :=
  contDiffAt_linear_zero (intrinsicBulkAction period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkPhysicalProjection period hPeriod couplings)
    (intrinsicBulkAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)

theorem intrinsicBulkBRSTAction_contDiffAt_zero (interactionScale : Real)
    (coefficients : PotentialCoefficients) :
    ContDiffAt Real 2 (intrinsicBulkBRSTAction period hPeriod couplings) 0 :=
  contDiffAt_remainder
    (intrinsicBulkAction period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkBRSTAction period hPeriod couplings)
    (intrinsicBulkAction_eq_physical_add_BRST period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkPhysicalAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)

def intrinsicBulkBRSTHessian : IntrinsicBulkCore period hPeriod couplings →L[Real]
    IntrinsicBulkCore period hPeriod couplings →L[Real] Real :=
  fderiv Real (fderiv Real (intrinsicBulkBRSTAction period hPeriod couplings)) 0

theorem intrinsicBulkHessian_eq_physical_add_BRST (interactionScale : Real)
    (coefficients : PotentialCoefficients) :
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients =
      intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients +
        intrinsicBulkBRSTHessian period hPeriod couplings :=
  second_fderiv_of_add
    (intrinsicBulkAction period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkBRSTAction period hPeriod couplings)
    (intrinsicBulkAction_eq_physical_add_BRST period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkPhysicalAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkBRSTAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
