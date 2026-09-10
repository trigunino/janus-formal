import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05FiniteNullHorizontalIntegrationMorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D

/-!
# Physical boundary-density bridge for T06

The relative classification is applied to the already constructed GHY density
and to the faithful finite null-face/joint transgression.  Both physical
families enter the T05 carrier through their proved integration maps and are
classified as horizontal boundaries, hence as relative null Lagrangians.

This bridge does not yet construct a BRST action or deck action on the full
relative-density carrier, so it is not a terminal T06 certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06PhysicalBoundaryDensityClassificationBridge4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05FiniteNullHorizontalIntegrationMorphism4D
open P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Horizontal boundary of the genuine completed GHY density. -/
def programPT06CanonicalGHYBoundaryDensity
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) :
    ProgramPT06RelativeDensity4D :=
  programPT05ExactT03RelativeBicomplex.dH 3 0
    (programPT05GHYDensityIntegratedRelativeCochain period hPeriod
      (programPT05CanonicalGHYLocalDensityCochain period hPeriod
        einsteinScale metric current))

/-- The completed GHY family is an actual relative boundary term and is
therefore variationally null in the T05 relative complex. -/
theorem programPT06CanonicalGHYBoundaryDensity_boundary_and_null
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) :
    IsRelativeBoundaryTerm
        (programPT06CanonicalGHYBoundaryDensity period hPeriod einsteinScale
          metric current) ∧
      IsRelativeNullLagrangian
        (programPT06CanonicalGHYBoundaryDensity period hPeriod einsteinScale
          metric current) := by
  have hBoundary : IsRelativeBoundaryTerm
      (programPT06CanonicalGHYBoundaryDensity period hPeriod einsteinScale
        metric current) := by
    exact ⟨programPT05GHYDensityIntegratedRelativeCochain period hPeriod
      (programPT05CanonicalGHYLocalDensityCochain period hPeriod
        einsteinScale metric current), rfl⟩
  have hHorizontal : IsHorizontalDensity
      (programPT06CanonicalGHYBoundaryDensity period hPeriod einsteinScale
        metric current) := by
    intro stratum
    cases stratum <;>
      simp [programPT06CanonicalGHYBoundaryDensity,
        programPT05ExactT03RelativeBicomplex,
        programPT05RelativeHorizontalDifferential,
        programPT05GHYDensityIntegratedRelativeCochain]
  exact ⟨hBoundary,
    (horizontalDensity_null_iff_boundary _ hHorizontal).2 hBoundary⟩

/-- The primitive used above evaluates in its non-null slot to the exact
completed GHY action. -/
theorem programPT06CanonicalGHYPrimitive_nonNull_eq_action
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) :
    programPT05GHYDensityIntegratedRelativeCochain period hPeriod
        (programPT05CanonicalGHYLocalDensityCochain period hPeriod
          einsteinScale metric current) .nonNullBoundary =
      (candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric current, 0) :=
  programPT05CanonicalGHYIntegratedRelativeCochain_nonNull_eq_action
    period hPeriod einsteinScale metric current

variable {NullFace : Type*} [Fintype NullFace]

/-- The complete integrated physical density packet (bulk, GHY, faithful
null faces and joints) satisfies the exhaustive relative null/boundary
equivalence. -/
theorem programPT06T03FaithfulGeometricDensity_null_iff_boundary
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    IsRelativeNullLagrangian
        (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
          couplings bulk ghy faithful input) ↔
      IsRelativeBoundaryTerm
        (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
          couplings bulk ghy faithful input) := by
  apply horizontalDensity_null_iff_boundary
  intro stratum
  cases stratum <;> rfl

/-- The faithful physical null-face transgression lands in the classified
top-degree relative boundary density. -/
theorem programPT06FaithfulNullJointBoundaryDensity_boundary_and_null
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ faithful.realization.geometry.domain) :
    IsRelativeBoundaryTerm
        (programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
          faithful input) ∧
      IsRelativeNullLagrangian
        (programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
          faithful input) := by
  have hBoundary : IsRelativeBoundaryTerm
      (programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
        faithful input) := by
    exact ⟨programPT05T03FaithfulNullTransgressionSourceIntegratedCochain
      faithful input,
      programPT05T03FaithfulNullTransgressionIntegration_commutes_dH
        faithful input hInput⟩
  have hHorizontal : IsHorizontalDensity
      (programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
        faithful input) := by
    intro stratum
    cases stratum <;>
      rfl
  exact ⟨hBoundary,
    (horizontalDensity_null_iff_boundary _ hHorizontal).2 hBoundary⟩

/-- The classified faithful target is the finite sum of the actual oriented
endpoint-joint action changes. -/
theorem programPT06FaithfulNullJointBoundaryDensity_joint_eq_actionChanges
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    (programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
        faithful input .joint).1 =
      ∑ face : NullFace,
        (reparametrizedEndpointJointAction
            (faithful.realization.geometry.toFiniteNullFaceActionDatum
              input face) -
          endpointJointAction
            (faithful.realization.geometry.toFiniteNullFaceActionDatum
              input face)) := by
  exact programPT05FiniteNullTransgressionTarget_eq_jointActionChanges
    (fun face =>
      faithful.realization.geometry.toFiniteNullFaceActionDatum input face)

end


end P0EFTJanusProgramPT06PhysicalBoundaryDensityClassificationBridge4D
end JanusFormal
