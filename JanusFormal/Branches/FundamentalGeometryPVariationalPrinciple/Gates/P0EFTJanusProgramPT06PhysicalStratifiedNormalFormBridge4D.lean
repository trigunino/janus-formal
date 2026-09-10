import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06StratifiedNullBoundaryNormalForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06PhysicalBoundaryDensityClassificationBridge4D

/-!
# Physical stratified normal-form bridge for T06

The genuine completed GHY density and the faithful finite null-face/joint
transgression are embedded into the independent T02/T05 product packet and
receive the unique constant-plus-normalized-boundary normal form for its
conjunctive predicate.  The complete integrated physical density packet
receives the same normal form exactly when it is a relative boundary term.

The local member of these embeddings is the zero T02 density.  Consequently
this gate connects the physical boundary families to the joined carrier but
does not turn the integrated relative component into a local density.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06PhysicalStratifiedNormalFormBridge4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 900000

noncomputable section

open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05FiniteNullHorizontalIntegrationMorphism4D
open P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D
open P0EFTJanusProgramPT06PhysicalBoundaryDensityClassificationBridge4D
open P0EFTJanusProgramPT06StratifiedNullBoundaryNormalForm4D
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The actual completed GHY boundary density has zero contact coordinate on
every relative stratum. -/
theorem programPT06CanonicalGHYBoundaryDensity_horizontal
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) :
    IsHorizontalDensity
      (programPT06CanonicalGHYBoundaryDensity period hPeriod einsteinScale
        metric current) := by
  intro stratum
  cases stratum <;>
    simp [programPT06CanonicalGHYBoundaryDensity,
      programPT05ExactT03RelativeBicomplex,
      programPT05RelativeHorizontalDifferential,
      programPT05GHYDensityIntegratedRelativeCochain]

/-- Hybrid product packet of the completed GHY boundary density. -/
def programPT06CanonicalGHYStratifiedPacket
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) :
    ProgramPT06StratifiedNullBoundaryPacket4D period hPeriod :=
  relativeDensityPacket period hPeriod
    (programPT06CanonicalGHYBoundaryDensity period hPeriod einsteinScale
      metric current)
    (programPT06CanonicalGHYBoundaryDensity_horizontal period hPeriod
      einsteinScale metric current)

/-- The physical completed GHY density has one unique stratified normal form. -/
theorem programPT06CanonicalGHYStratifiedPacket_existsUnique_normalForm
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) :
    ∃! normalForm : Real × ProgramPT06RelativeBoundaryPrimitive4D,
      IsStratifiedBoundaryNormalForm period hPeriod
        (programPT06CanonicalGHYStratifiedPacket period hPeriod einsteinScale
          metric current) normalForm := by
  apply (stratifiedVariationallyNull_iff_existsUnique_boundaryNormalForm
    period hPeriod _).1
  change IsStratifiedVariationallyNull period hPeriod
    (relativeDensityPacket period hPeriod
      (programPT06CanonicalGHYBoundaryDensity period hPeriod einsteinScale
        metric current) _)
  apply (relativeDensityPacket_null_iff_boundary period hPeriod _ _).2
  exact (programPT06CanonicalGHYBoundaryDensity_boundary_and_null period hPeriod
    einsteinScale metric current).1

variable {NullFace : Type*} [Fintype NullFace]

/-- The faithful null/joint transgression target is horizontal. -/
theorem programPT06FaithfulNullJointBoundaryDensity_horizontal
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    IsHorizontalDensity
      (programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
        faithful input) := by
  intro stratum
  cases stratum <;> rfl

/-- Hybrid product packet of the faithful physical null/joint boundary density. -/
def programPT06FaithfulNullJointStratifiedPacket
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    ProgramPT06StratifiedNullBoundaryPacket4D period hPeriod :=
  relativeDensityPacket period hPeriod
    (programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
      faithful input)
    (programPT06FaithfulNullJointBoundaryDensity_horizontal faithful input)

/-- Every admissible faithful null/joint target has one unique stratified
normal form. -/
theorem programPT06FaithfulNullJointStratifiedPacket_existsUnique_normalForm
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ faithful.realization.geometry.domain) :
    ∃! normalForm : Real × ProgramPT06RelativeBoundaryPrimitive4D,
      IsStratifiedBoundaryNormalForm period hPeriod
        (programPT06FaithfulNullJointStratifiedPacket period hPeriod faithful
          input) normalForm := by
  apply (stratifiedVariationallyNull_iff_existsUnique_boundaryNormalForm
    period hPeriod _).1
  change IsStratifiedVariationallyNull period hPeriod
    (relativeDensityPacket period hPeriod
      (programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
        faithful input) _)
  apply (relativeDensityPacket_null_iff_boundary period hPeriod _ _).2
  exact (programPT06FaithfulNullJointBoundaryDensity_boundary_and_null
    faithful input hInput).1

/-- The complete integrated bulk/SpinC/LL/GHY/null/joint packet is horizontal. -/
theorem programPT06T03FaithfulGeometricDensity_horizontal
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    IsHorizontalDensity
      (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
        couplings bulk ghy faithful input) := by
  intro stratum
  cases stratum <;> rfl

/-- Hybrid product representative of the complete integrated physical density
packet. -/
def programPT06T03FaithfulGeometricStratifiedPacket
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    ProgramPT06StratifiedNullBoundaryPacket4D period hPeriod :=
  relativeDensityPacket period hPeriod
    (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
      couplings bulk ghy faithful input)
    (programPT06T03FaithfulGeometricDensity_horizontal period hPeriod
      couplings bulk ghy faithful input)

/-- The complete physical packet is a relative boundary exactly when its
hybrid representative has a unique normal form. -/
theorem programPT06T03FaithfulGeometricDensity_boundary_iff_existsUnique_normalForm
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    IsRelativeBoundaryTerm
        (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
          couplings bulk ghy faithful input) ↔
      ∃! normalForm : Real × ProgramPT06RelativeBoundaryPrimitive4D,
        IsStratifiedBoundaryNormalForm period hPeriod
          (programPT06T03FaithfulGeometricStratifiedPacket period hPeriod
            couplings bulk ghy faithful input) normalForm := by
  rw [← relativeDensityPacket_null_iff_boundary period hPeriod
    (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
      couplings bulk ghy faithful input)
    (programPT06T03FaithfulGeometricDensity_horizontal period hPeriod
      couplings bulk ghy faithful input)]
  exact stratifiedVariationallyNull_iff_existsUnique_boundaryNormalForm
    period hPeriod _

end

end P0EFTJanusProgramPT06PhysicalStratifiedNormalFormBridge4D
end JanusFormal
