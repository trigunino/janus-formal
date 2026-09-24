import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAbelianBRestriction4D

/-! The exact B--B column of the actual intrinsic bulk Hessian. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianBHessian4D
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
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D P0EFTJanusProgramPT12IntrinsicBulkAbelianBRestriction4D
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
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings
local notation "BCore" => IntrinsicBulkAbelianBCore period hPeriod
variable (interactionScale : Real) (coefficients : PotentialCoefficients)

theorem intrinsicBulkAction_abelianB_hasFDerivAt (point : BCore) :
    HasFDerivAt (fun field : BCore => intrinsicBulkAction period hPeriod couplings interactionScale
      coefficients (intrinsicBulkAbelianBInsertion period hPeriod couplings field))
      (-intrinsicBulkAbelianBPairing period hPeriod point) point := by
  have hDiagonal := ((intrinsicBulkAbelianBPairing period hPeriod).hasFDerivAt (x := point)).clm_apply
    (hasFDerivAt_id (𝕜 := Real) point)
  have hQuadratic := (hasFDerivAt_const
    (intrinsicBulkAction period hPeriod couplings interactionScale coefficients 0) point).sub
      (hDiagonal.const_mul (1 / 2 : Real))
  have hRestriction : (fun field : BCore => intrinsicBulkAction period hPeriod couplings interactionScale
      coefficients (intrinsicBulkAbelianBInsertion period hPeriod couplings field)) =
      (fun field => intrinsicBulkAction period hPeriod couplings interactionScale coefficients 0 -
        (1 / 2 : Real) * intrinsicBulkAbelianBPairing period hPeriod field field) :=
    funext (intrinsicBulkAction_abelianB_restriction period hPeriod couplings interactionScale coefficients)
  rw [hRestriction]
  apply hQuadratic.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  change 0 - (1 / 2 : Real) *
      (intrinsicBulkAbelianBPairing period hPeriod point direction +
        intrinsicBulkAbelianBPairing period hPeriod direction point) =
    -intrinsicBulkAbelianBPairing period hPeriod point direction
  rw [intrinsicBulkAbelianBPairing_symmetric period hPeriod direction point]
  ring

theorem intrinsicBulkAction_abelianB_second_fderiv :
    fderiv Real (fderiv Real (fun field : BCore => intrinsicBulkAction period hPeriod couplings
      interactionScale coefficients (intrinsicBulkAbelianBInsertion period hPeriod couplings field))) 0 =
      -intrinsicBulkAbelianBPairing period hPeriod := by
  have hGradient : fderiv Real (fun field : BCore => intrinsicBulkAction period hPeriod couplings
      interactionScale coefficients (intrinsicBulkAbelianBInsertion period hPeriod couplings field)) =
      (fun field => -intrinsicBulkAbelianBPairing period hPeriod field) :=
    funext fun point => (intrinsicBulkAction_abelianB_hasFDerivAt period hPeriod couplings
      interactionScale coefficients point).fderiv
  rw [hGradient]
  exact (((intrinsicBulkAbelianBPairing period hPeriod).hasFDerivAt (x := 0)).neg).fderiv

theorem intrinsicBulkHessian_abelianB_abelianB (first second : BCore) :
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianBInsertion period hPeriod couplings first)
      (intrinsicBulkAbelianBInsertion period hPeriod couplings second) =
      -intrinsicBulkAbelianBPairing period hPeriod first second := by
  rw [← intrinsicBulkHessian_linear_pullback period hPeriod couplings interactionScale coefficients
    (intrinsicBulkAbelianBInsertion period hPeriod couplings) first second,
    intrinsicBulkAction_abelianB_second_fderiv]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianBHessian4D
