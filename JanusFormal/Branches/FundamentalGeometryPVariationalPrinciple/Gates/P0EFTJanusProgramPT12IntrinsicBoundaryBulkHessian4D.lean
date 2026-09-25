import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBoundaryBulkCore4D

/-! The actual second derivative on the compatible bulk/boundary core.
The generic definition avoids elaborating nested derivative instances on the
large geometric product. This remains the bulk action pulled back to that core. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryBulkHessian4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusProgramPT12AffineHessianPullback4D

/-- The genuine continuous second derivative at zero of a scalar action. -/
def scalarActionSecondDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (action : E → Real) : E →L[Real] E →L[Real] Real :=
  fderiv Real (fderiv Real action) 0

theorem scalarActionSecondDerivative_linear_pullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (action : F → Real) (projection : E →L[Real] F)
    (hC2 : ContDiffAt Real 2 action 0) (first second : E) :
    scalarActionSecondDerivative (fun point => action (projection point)) first second =
      scalarActionSecondDerivative action (projection first) (projection second) := by
  simpa only [scalarActionSecondDerivative, one_mul, zero_add] using
    scaledAffineHessian action 0 projection 1 hC2 first second

open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
open P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPT12IntrinsicBoundaryBulkCore4D
open P0EFTJanusReciprocalBimetricPotential
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0) (couplings : GlobalCandidateAActionCouplings)
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
local notation "Bulk" => IntrinsicBulkCore period hPeriod couplings
local notation "Core" => IntrinsicBoundaryBulkCore period hPeriod couplings
local instance bulkNormedAddCommGroup : NormedAddCommGroup Bulk := inferInstance
local instance : NormedSpace Real Bulk :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings
local instance : NormedAddCommGroup Core := intrinsicBoundaryBulkCoreNormedAddCommGroup period hPeriod couplings
local instance : NormedSpace Real Core := intrinsicBoundaryBulkCoreNormedSpace period hPeriod couplings

/-- No surrogate form: this is the second derivative of `intrinsicBoundaryBulkAction`. -/
def intrinsicBoundaryBulkHessian (interactionScale : Real) (coefficients : PotentialCoefficients) :
    Core →L[Real] Core →L[Real] Real :=
  scalarActionSecondDerivative
    (intrinsicBoundaryBulkAction period hPeriod couplings interactionScale coefficients)

theorem intrinsicBoundaryBulkAction_hessian (interactionScale : Real) (coefficients : PotentialCoefficients)
    (first second : Core) :
    intrinsicBoundaryBulkHessian period hPeriod couplings interactionScale coefficients first second =
      intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
        (intrinsicBoundaryBulkProjection period hPeriod couplings first)
        (intrinsicBoundaryBulkProjection period hPeriod couplings second) :=
  scalarActionSecondDerivative_linear_pullback
    (intrinsicBulkAction period hPeriod couplings interactionScale coefficients)
    (intrinsicBoundaryBulkProjection period hPeriod couplings)
    (intrinsicBulkAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients) first second

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryBulkHessian4D
