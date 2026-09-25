import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAbelianBHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAbelianBAHessian4D

/-! The native BRST Hessian has exactly the nonminimal columns of the actual
bulk Hessian, including its previously computed B--B and B--potential entries. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkBRSTColumns4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

private theorem bilinear_column_of_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (total physical brst : E →L[Real] E →L[Real] Real)
    (hSplit : total = physical + brst) (first second : E)
    (hPhysical : physical first second = 0) : brst first second = total first second := by
  have hValue : total first second = physical first second + brst first second :=
    congrArg (fun form : E →L[Real] E →L[Real] Real => form first second) hSplit
  simpa only [hPhysical, zero_add] using hValue.symm

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
open P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianBRestriction4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianBHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianLorenz4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianBARestriction4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianBAHessian4D
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

theorem intrinsicBulkBRSTHessian_diffeomorphism_eq_bulk
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod (finiteSmoothTangentFrame period hPeriod))
    (test : IntrinsicBulkCore period hPeriod couplings) :
    intrinsicBulkBRSTHessian period hPeriod couplings
      (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings fields) test =
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkDiffeomorphismInsertion period hPeriod couplings fields) test :=
  bilinear_column_of_split _ _ _
    (intrinsicBulkHessian_eq_physical_add_BRST period hPeriod couplings interactionScale coefficients) _ _
    (intrinsicBulkPhysicalHessian_diffeomorphism_zero period hPeriod couplings interactionScale coefficients fields test)

theorem intrinsicBulkBRSTHessian_abelianNonminimal_eq_bulk
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IntrinsicBulkAbelianNonminimalCore period hPeriod)
    (test : IntrinsicBulkCore period hPeriod couplings) :
    intrinsicBulkBRSTHessian period hPeriod couplings
      (intrinsicBulkAbelianNonminimalInsertion period hPeriod couplings fields) test =
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianNonminimalInsertion period hPeriod couplings fields) test :=
  bilinear_column_of_split _ _ _
    (intrinsicBulkHessian_eq_physical_add_BRST period hPeriod couplings interactionScale coefficients) _ _
    (intrinsicBulkPhysicalHessian_abelianNonminimal_zero period hPeriod couplings interactionScale coefficients fields test)

theorem intrinsicBulkBRSTHessian_abelianB_abelianB
    (first second : IntrinsicBulkAbelianBCore period hPeriod) :
    intrinsicBulkBRSTHessian period hPeriod couplings
      (intrinsicBulkAbelianBInsertion period hPeriod couplings first)
      (intrinsicBulkAbelianBInsertion period hPeriod couplings second) =
      -intrinsicBulkAbelianBPairing period hPeriod first second :=
  (bilinear_column_of_split _ _ _
    (intrinsicBulkHessian_eq_physical_add_BRST period hPeriod couplings 0 ⟨0, 0, 0, 0, 0⟩) _ _
    (intrinsicBulkPhysicalHessian_abelianB_zero period hPeriod couplings 0 ⟨0, 0, 0, 0, 0⟩ first
      (intrinsicBulkAbelianBInsertion period hPeriod couplings second))).trans
    (intrinsicBulkHessian_abelianB_abelianB period hPeriod couplings 0 ⟨0, 0, 0, 0, 0⟩ first second)

theorem intrinsicBulkBRSTHessian_abelianB_abelianA
    (field : IntrinsicBulkAbelianBCore period hPeriod) (potential : IntrinsicBulkAbelianACore period hPeriod) :
    intrinsicBulkBRSTHessian period hPeriod couplings
      (intrinsicBulkAbelianBInsertion period hPeriod couplings field)
      (intrinsicBulkAbelianAInsertion period hPeriod couplings potential) =
      intrinsicBulkAbelianBAPairing period hPeriod field potential :=
  (bilinear_column_of_split _ _ _
    (intrinsicBulkHessian_eq_physical_add_BRST period hPeriod couplings 0 ⟨0, 0, 0, 0, 0⟩) _ _
    (intrinsicBulkPhysicalHessian_abelianB_zero period hPeriod couplings 0 ⟨0, 0, 0, 0, 0⟩ field
      (intrinsicBulkAbelianAInsertion period hPeriod couplings potential))).trans
    (intrinsicBulkHessian_abelianB_abelianA period hPeriod couplings 0 ⟨0, 0, 0, 0, 0⟩ field potential)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkBRSTColumns4D
