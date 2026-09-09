import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05CanonicalVerticalIntegrationEvaluation4D

/-!
# Stratified local vertical density complex

This module fixes the null-face intervals and lifts every density coefficient
in that fibre to the vertical generator in horizontal degree four.  Sectorwise
integration of the lift is exactly Gate 841's integrated `dV`.  Consequently
its integrated image satisfies both `dV² = 0` and the mixed bicomplex identity.

The non-linear interval data is a parameter, rather than an element of the
density fibre.  The SpinC graph frontier enters only through its already
defined scalar action coefficient.  The construction is the generator lift
of the existing two-term vertical realization; it does not assert a Frechet
derivative with respect to field jets.  No local horizontal restriction or
Stokes map is introduced here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05StratifiedLocalVerticalDensityComplex4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
open P0EFTJanusProgramPT05CanonicalVerticalIntegrationEvaluation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Contact-degree-one representatives in the fibre over fixed null-face
intervals.  All genuine density fields remain on their geometric carriers;
the non-local SpinC frontier is represented only by its scalar coefficient. -/
structure ProgramPT05FixedCarrierStratifiedVerticalDensityCochain
    (period : Real) (hPeriod : period ≠ 0)
    (NullFace : Type*)
    (_nullFaceInterval : NullFace → OrientedNullInterval) where
  bulkVerticalDensity : C(EffectiveQuotient period hPeriod, Real)
  spinCVerticalCoefficient : Real
  llVerticalDensity : C(EffectiveThroat period hPeriod, Real)
  nonNullBoundaryVerticalDensity :
    CandidateANormalBoundaryScalarField period hPeriod
  nullBoundaryVerticalDensity : NullFace → Real → Real
  jointVerticalDensity : NullFace → ProgramPT05NullJointEndpoint → Real

/-- Local vertical-generator lift in horizontal degree four.  The sign of the
Gate-819 vertical differential is positive in this degree. -/
def programPT05GeometricStratifiedLocalDV4
    {NullFace : Type*}
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    ProgramPT05FixedCarrierStratifiedVerticalDensityCochain period hPeriod
      NullFace density.nullFaceInterval where
  bulkVerticalDensity := density.bulkDensity
  spinCVerticalCoefficient :=
    programPT05BulkSpinCFrontierAction period hPeriod couplings
      density.spinCFrontier
  llVerticalDensity := density.llDensity
  nonNullBoundaryVerticalDensity := density.nonNullBoundaryDensity
  nullBoundaryVerticalDensity := density.nullBoundaryDensity
  jointVerticalDensity := density.jointDensity

/-- Sectorwise integration of a local vertical density.  Each integral is
placed in the vertical-generator coordinate of the Gate-819 carrier. -/
def programPT05IntegrateGeometricStratifiedVerticalDensityCochain
    {NullFace : Type*} [Fintype NullFace]
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierStratifiedVerticalDensityCochain period
      hPeriod NullFace nullFaceInterval) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 1
  | .bulk =>
      (0,
        (programPT05GeometricBulkDensityIntegral period hPeriod
            density.bulkVerticalDensity +
          density.spinCVerticalCoefficient) +
        programPT05GeometricLLDensityIntegral period hPeriod
          density.llVerticalDensity)
  | .nonNullBoundary =>
      (0, programPT05GeometricGHYDensityIntegral period hPeriod
        density.nonNullBoundaryVerticalDensity)
  | .nullBoundary =>
      (0, programPT05GeometricNullBoundaryDensityIntegral
        nullFaceInterval density.nullBoundaryVerticalDensity)
  | .joint =>
      (0, programPT05GeometricJointDensityIntegral
        density.jointVerticalDensity)

/-- The local vertical lift commutes exactly with sectorwise integration for
every stratified packet.  No regularity contract is required because this is
the generator differential of the concrete two-term realization. -/
theorem programPT05GeometricStratifiedLocalDV4_integration_commutes
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    programPT05IntegrateGeometricStratifiedVerticalDensityCochain period
        hPeriod density.nullFaceInterval
          (programPT05GeometricStratifiedLocalDV4 period hPeriod couplings
            density) =
      programPT05ExactT03RelativeBicomplex.dV 4 0
        (programPT05GeometricDensityIntegrationMap period hPeriod couplings
          density) := by
  rw [programPT05GeometricDensityIntegrationMap_dV_eq_integratedVertical]
  funext stratum
  cases stratum <;> rfl

/-- The integrated local vertical lift inherits the genuine square-zero law. -/
theorem programPT05GeometricStratifiedLocalDV4_integrated_squared
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    programPT05ExactT03RelativeBicomplex.dV 4 1
        (programPT05IntegrateGeometricStratifiedVerticalDensityCochain period
          hPeriod density.nullFaceInterval
            (programPT05GeometricStratifiedLocalDV4 period hPeriod couplings
              density)) = 0 := by
  rw [programPT05GeometricStratifiedLocalDV4_integration_commutes]
  exact programPT05ExactT03RelativeBicomplex.dV_dV 4 0
    (programPT05GeometricDensityIntegrationMap period hPeriod couplings
      density)

/-- The local vertical edge and the existing integrated horizontal edge obey
the mixed bicomplex identity after sectorwise integration. -/
theorem programPT05GeometricStratifiedLocalDV4_integrated_mixed_anticommutes
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (density : ProgramPT05GeometricStratifiedDensityCochain period hPeriod
      couplings NullFace) :
    programPT05ExactT03RelativeBicomplex.dV 5 0
          (programPT05ExactT03RelativeBicomplex.dH 4 0
            (programPT05GeometricDensityIntegrationMap period hPeriod
              couplings density)) +
        programPT05ExactT03RelativeBicomplex.dH 4 1
          (programPT05IntegrateGeometricStratifiedVerticalDensityCochain period
            hPeriod density.nullFaceInterval
              (programPT05GeometricStratifiedLocalDV4 period hPeriod couplings
                density)) = 0 := by
  rw [programPT05GeometricStratifiedLocalDV4_integration_commutes]
  exact programPT05ExactT03RelativeBicomplex.mixed_anticommutes 4 0
    (programPT05GeometricDensityIntegrationMap period hPeriod couplings
      density)

end
end P0EFTJanusProgramPT05StratifiedLocalVerticalDensityComplex4D
end JanusFormal
