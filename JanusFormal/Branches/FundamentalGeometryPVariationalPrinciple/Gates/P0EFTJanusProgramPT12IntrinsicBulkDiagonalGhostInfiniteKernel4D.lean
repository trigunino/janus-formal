import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SmoothGhostInfiniteDimension4D

/-! Infinite-dimensional kernel of the actual intrinsic bulk Hessian at opposite
Einstein weights. This concerns the unreduced Banach bulk core only. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostInfiniteKernel4D
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
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
open P0EFTJanusProgramPT12SmoothGhostInfiniteDimension4D
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

variable (couplings : GlobalCandidateAActionCouplings)
local notation "Core" => IntrinsicBulkCore period hPeriod couplings
local instance coreNormedAddCommGroup : NormedAddCommGroup Core := inferInstance
local instance : NormedSpace Real Core :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings
local instance : AddZeroClass Core :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
variable (interactionScale : Real) (coefficients : PotentialCoefficients)
variable (hWeights : candidateAPlusEinsteinKineticWeight couplings +
  candidateAMinusEinsteinKineticWeight couplings = 0)
local notation "H" => intrinsicBulkHessian period hPeriod couplings interactionScale coefficients

include hWeights in
theorem intrinsicBulkHessian_smoothDiagonalGhost_zero
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    H (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings ghost) = 0 := by
  apply ContinuousLinearMap.ext
  intro test
  exact intrinsicBulkHessian_smoothDiagonalGhost_column_zero period hPeriod couplings
    interactionScale coefficients hWeights ghost test

/-- Actual smooth tangent ghosts inject into the kernel of the bulk Hessian. -/
def intrinsicBulkSmoothGhostKernelInclusion :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real] LinearMap.ker (H).toLinearMap :=
  (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings).codRestrict
    (LinearMap.ker (H).toLinearMap) (by
      intro ghost
      exact intrinsicBulkHessian_smoothDiagonalGhost_zero period hPeriod couplings
        interactionScale coefficients hWeights ghost)

theorem intrinsicBulkSmoothGhostKernelInclusion_injective :
    Function.Injective (intrinsicBulkSmoothGhostKernelInclusion period hPeriod couplings
      interactionScale coefficients hWeights) := by
  intro first second hEqual
  exact intrinsicBulkSmoothDiffeomorphismGhostInsertion_injective period hPeriod couplings
    (congrArg Subtype.val hEqual)

variable [Fact (0 < period)]

include hWeights in
theorem intrinsicBulkHessian_kernel_not_finiteDimensional :
    ¬ FiniteDimensional Real (LinearMap.ker (H).toLinearMap) := by
  intro hFinite
  letI := hFinite
  exact smoothDiffeomorphismGhost_not_finiteDimensional period hPeriod
    (FiniteDimensional.of_injective
      (intrinsicBulkSmoothGhostKernelInclusion period hPeriod couplings interactionScale coefficients hWeights)
      (intrinsicBulkSmoothGhostKernelInclusion_injective period hPeriod couplings
        interactionScale coefficients hWeights))

include hWeights in
/-- The unreduced bulk Hessian fails the usual Fredholm conjunction. -/
theorem intrinsicBulkHessian_not_fredholm :
    ¬ (IsClosed (LinearMap.range (H).toLinearMap : Set (Core →L[Real] Real)) ∧
      FiniteDimensional Real (LinearMap.ker (H).toLinearMap) ∧
      FiniteDimensional Real ((Core →L[Real] Real) ⧸ LinearMap.range (H).toLinearMap)) := by
  intro hFredholm
  exact intrinsicBulkHessian_kernel_not_finiteDimensional period hPeriod couplings
    interactionScale coefficients hWeights hFredholm.2.1

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostInfiniteKernel4D
