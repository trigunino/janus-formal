import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AffineHessianPullback4D
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The actual second derivative of the intrinsic bulk action on its inhabited Banach core. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkHessian4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
open P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12AffineHessianPullback4D

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

variable (couplings : GlobalCandidateAActionCouplings)
local instance : NormedAddCommGroup (IntrinsicBulkCore period hPeriod couplings) := inferInstance
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings
local notation "Core" => IntrinsicBulkCore period hPeriod couplings
local instance : AddZeroClass Core :=
  (inferInstance : NormedAddCommGroup Core).toAddCommGroup.toAddZeroClass
variable (interactionScale : Real) (coefficients : PotentialCoefficients)

def intrinsicBulkEuler (point : Core) : Core →L[Real] Real :=
  fderiv Real (intrinsicBulkAction period hPeriod couplings interactionScale coefficients) point

def intrinsicBulkHessian : Core →L[Real] Core →L[Real] Real :=
  fderiv Real (intrinsicBulkEuler period hPeriod couplings interactionScale coefficients) 0

theorem intrinsicBulkEuler_hasFDerivAt_zero :
    HasFDerivAt (intrinsicBulkEuler period hPeriod couplings interactionScale coefficients)
      (intrinsicBulkHessian period hPeriod couplings interactionScale coefficients) 0 :=
  ((intrinsicBulkAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients).fderiv_right
    (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt

theorem intrinsicBulkHessian_symmetric (first second : Core) :
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients first second =
      intrinsicBulkHessian period hPeriod couplings interactionScale coefficients second first :=
  (intrinsicBulkAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients).isSymmSndFDerivAt
    (by norm_num) first second

theorem intrinsicBulkHessian_norm_apply_le (first second : Core) :
    ‖intrinsicBulkHessian period hPeriod couplings interactionScale coefficients first second‖ ≤
      ‖intrinsicBulkHessian period hPeriod couplings interactionScale coefficients‖ * ‖first‖ * ‖second‖ := by
  let hessian := intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
  calc
    ‖hessian first second‖ ≤ ‖hessian first‖ * ‖second‖ := (hessian first).le_opNorm second
    _ ≤ (‖hessian‖ * ‖first‖) * ‖second‖ :=
      mul_le_mul_of_nonneg_right (hessian.le_opNorm first) (norm_nonneg second)

theorem intrinsicBulkHessian_linear_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (projection : E →L[Real] Core) (first second : E) :
    fderiv Real (fderiv Real (fun point : E =>
      intrinsicBulkAction period hPeriod couplings interactionScale coefficients (projection point)))
      0 first second =
      intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
        (projection first) (projection second) := by
  change _ = fderiv Real
    (fderiv Real (intrinsicBulkAction period hPeriod couplings interactionScale coefficients))
      0 (projection first) (projection second)
  simpa only [one_mul, zero_add] using
    scaledAffineHessian (intrinsicBulkAction period hPeriod couplings interactionScale coefficients)
      0 projection 1
      (intrinsicBulkAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)
      first second

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkHessian4D
