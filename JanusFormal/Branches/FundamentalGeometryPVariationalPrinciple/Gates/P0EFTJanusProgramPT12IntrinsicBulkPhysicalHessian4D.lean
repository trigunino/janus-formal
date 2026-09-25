import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkPhysicalProjection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D

/-! The Hessian of the identified physical bulk action, with exact zero
nonminimal columns. No boundary GHY or Hilbert-space realization is asserted. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianBRestriction4D
open P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalProjection4D
open P0EFTJanusReciprocalBimetricPotential
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

private theorem bilinear_zero_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (form : E →L[Real] E →L[Real] Real) (first second : E) (hFirst : first = 0) :
    form first second = 0 := by
  rw [hFirst, form.map_zero, zero_apply]

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
local notation "Core" => IntrinsicBulkCore period hPeriod couplings
local notation "BCore" => IntrinsicBulkAbelianBCore period hPeriod
local notation "Ghost" => IntrinsicBulkDiffeomorphismGhostCore period hPeriod
local notation "Packet" => FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod
  (finiteSmoothTangentFrame period hPeriod)
local instance coreNormedAddCommGroup : NormedAddCommGroup Core := inferInstance
local instance : AddZeroClass Core :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real Core :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings
local notation "projection" => intrinsicBulkPhysicalProjection period hPeriod couplings

abbrev IntrinsicBulkAbelianNonminimalCore :=
  FiniteFrameAbelianNonminimalC2Core period hPeriod × FiniteFrameAbelianNonminimalC2Core period hPeriod
local notation "AbelianPacket" => IntrinsicBulkAbelianNonminimalCore period hPeriod

def intrinsicBulkAbelianNonminimalInsertion : AbelianPacket →L[Real] Core :=
  let fields : AbelianPacket →L[Real] FiniteFramePairedC2AbelianGaugeFields period hPeriod
      (finiteSmoothTangentFrame period hPeriod) (finiteSmoothTangentFrame period hPeriod) :=
    ((0 : AbelianPacket →L[Real] _).prod (ContinuousLinearMap.fst Real _ _)).prod
      ((0 : AbelianPacket →L[Real] _).prod (ContinuousLinearMap.snd Real _ _))
  let physical : AbelianPacket →L[Real] FiniteFramePairedC2PhysicalCore period hPeriod
      (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) :=
    (0 : AbelianPacket →L[Real] _).prod (fields.prod 0)
  (physical.prod 0).prod 0

theorem intrinsicBulkPhysicalProjection_abelianNonminimal (fields : AbelianPacket) :
    projection (intrinsicBulkAbelianNonminimalInsertion period hPeriod couplings fields) = 0 := rfl

theorem intrinsicBulkPhysicalProjection_abelianB (field : BCore) :
    projection (intrinsicBulkAbelianBInsertion period hPeriod couplings field) = 0 := rfl

theorem intrinsicBulkPhysicalProjection_diffeomorphism (fields : Packet) :
    projection (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings fields) = 0 := rfl

theorem intrinsicBulkPhysicalProjection_diffeomorphismGhost (ghost : Ghost) :
    projection (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost) = 0 :=
  intrinsicBulkPhysicalProjection_diffeomorphism period hPeriod couplings (0, (0, ghost))

variable (interactionScale : Real) (coefficients : PotentialCoefficients)

def intrinsicBulkPhysicalHessian : Core →L[Real] Core →L[Real] Real :=
  fderiv Real (fderiv Real
    (intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients)) 0

theorem intrinsicBulkPhysicalHessian_apply (first second : Core) :
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients first second =
      intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
        (projection first) (projection second) :=
  intrinsicBulkHessian_linear_pullback period hPeriod couplings interactionScale coefficients projection first second

theorem intrinsicBulkPhysicalHessian_symmetric (first second : Core) :
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients first second =
      intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients second first :=
  (intrinsicBulkPhysicalHessian_apply period hPeriod couplings interactionScale coefficients first second).trans
    ((intrinsicBulkHessian_symmetric period hPeriod couplings interactionScale coefficients
      (projection first) (projection second)).trans
        (intrinsicBulkPhysicalHessian_apply period hPeriod couplings interactionScale coefficients second first).symm)

theorem intrinsicBulkPhysicalHessian_abelianB_zero (field : BCore) (test : Core) :
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianBInsertion period hPeriod couplings field) test = 0 :=
  (intrinsicBulkPhysicalHessian_apply period hPeriod couplings interactionScale coefficients
    (intrinsicBulkAbelianBInsertion period hPeriod couplings field) test).trans
      (bilinear_zero_left (intrinsicBulkHessian period hPeriod couplings interactionScale coefficients)
        (projection (intrinsicBulkAbelianBInsertion period hPeriod couplings field)) (projection test)
        (intrinsicBulkPhysicalProjection_abelianB period hPeriod couplings field))

theorem intrinsicBulkPhysicalHessian_diffeomorphism_zero (fields : Packet) (test : Core) :
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings fields) test = 0 :=
  (intrinsicBulkPhysicalHessian_apply period hPeriod couplings interactionScale coefficients
    (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings fields) test).trans
      (bilinear_zero_left (intrinsicBulkHessian period hPeriod couplings interactionScale coefficients)
        (projection (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings fields)) (projection test)
        (intrinsicBulkPhysicalProjection_diffeomorphism period hPeriod couplings fields))

theorem intrinsicBulkPhysicalHessian_diffeomorphismGhost_zero (ghost : Ghost) (test : Core) :
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkDiffeomorphismGhostInsertion period hPeriod couplings ghost) test = 0 :=
  intrinsicBulkPhysicalHessian_diffeomorphism_zero period hPeriod couplings interactionScale coefficients
    (0, (0, ghost)) test

theorem intrinsicBulkPhysicalHessian_abelianNonminimal_zero (fields : AbelianPacket) (test : Core) :
    intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianNonminimalInsertion period hPeriod couplings fields) test = 0 :=
  (intrinsicBulkPhysicalHessian_apply period hPeriod couplings interactionScale coefficients
    (intrinsicBulkAbelianNonminimalInsertion period hPeriod couplings fields) test).trans
      (bilinear_zero_left (intrinsicBulkHessian period hPeriod couplings interactionScale coefficients)
        (projection (intrinsicBulkAbelianNonminimalInsertion period hPeriod couplings fields))
        (projection test) (intrinsicBulkPhysicalProjection_abelianNonminimal period hPeriod couplings fields))

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D
