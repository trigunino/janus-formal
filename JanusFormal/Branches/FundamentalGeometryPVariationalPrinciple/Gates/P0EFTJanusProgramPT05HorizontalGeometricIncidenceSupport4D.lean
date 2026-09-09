import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05MissingHorizontalGeometricContracts4D

/-!
# Reduced support for the two missing horizontal geometric incidences

The current API has no incidence map from an abstract finite null face into
the canonical cut collar, and no codimension-two trace carrier attached to
the completed orientation boundary.  Consequently a genuine restriction or
trace cannot yet be constructed from the existing geometric objects.

This module records the smallest reduced operators that such geometry must
induce after the joint carriers have been integrated: a linear restriction
from cut-bulk densities to null-face densities, and a linear trace from
completed boundary fields to endpoint coefficients.  Their Stokes and trace
laws are required only at the canonical sources used here.  These supports
produce Gate 852's contract and its conditional commuting square; no support
or terminal T05 conclusion is asserted to exist.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05HorizontalGeometricIncidenceSupport4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT05CutBulkLocalDensityStokesBridge4D
open P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05AvailableStratifiedHorizontalComplex4D
open P0EFTJanusProgramPT05MissingHorizontalGeometricContracts4D

/-- Scalar densities on the canonical product collar used by Gate 821. -/
abbrev ProgramPT05CutBulkDensityField :=
  CanonicalLatitudeBase → Real → Real

/-- Reduced scalar densities on a finite family of null intervals. -/
abbrev ProgramPT05NullFaceDensity (NullFace : Type*) :=
  NullFace → Real → Real

/-- Reduced endpoint coefficients after integration on each joint carrier. -/
abbrev ProgramPT05JointCoefficient (NullFace : Type*) :=
  NullFace → ProgramPT05NullJointEndpoint → Real

/-- The linear density transfer that an actual cut-collar/null-face
incidence map, including its induced density weight, must provide. -/
structure ProgramPT05BulkToNullRestrictionOperator (NullFace : Type*) where
  toLinearMap : ProgramPT05CutBulkDensityField →ₗ[Real]
    ProgramPT05NullFaceDensity NullFace

/-- The linear reduced trace that an actual codimension-two joint carrier
and its integration map must provide. -/
structure ProgramPT05GHYToJointTraceOperator
    (period : Real) (hPeriod : period ≠ 0) (NullFace : Type*) where
  toLinearMap : CandidateANormalBoundaryScalarField period hPeriod →ₗ[Real]
    ProgramPT05JointCoefficient NullFace

variable (period : Real) (hPeriod : period ≠ 0)

/-- Apply a proposed geometric restriction to Gate 821's actual canonical
cut-bulk density. -/
def programPT05CanonicalBulkToNullRestrictedDensity
    {NullFace : Type*}
    (field test : SmoothQuotientField period hPeriod Real)
    (restriction : ProgramPT05BulkToNullRestrictionOperator NullFace) :
    ProgramPT05NullFaceDensity NullFace :=
  restriction.toLinearMap
    (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod field test).bulkDensity

/-- Apply a proposed reduced joint trace to an actual completed boundary
scalar field. -/
def programPT05GHYToJointTracedDensity
    {NullFace : Type*}
    (trace : ProgramPT05GHYToJointTraceOperator period hPeriod NullFace)
    (density : CandidateANormalBoundaryScalarField period hPeriod) :
    ProgramPT05JointCoefficient NullFace :=
  trace.toLinearMap density

/-- Gate 824's canonical GHY integrand passed through a proposed reduced
joint trace. -/
def programPT05CanonicalGHYToJointTracedDensity
    {NullFace : Type*}
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric ×
      Real)
    (trace : ProgramPT05GHYToJointTraceOperator period hPeriod NullFace) :
    ProgramPT05JointCoefficient NullFace :=
  programPT05GHYToJointTracedDensity period hPeriod trace
    (programPT05CanonicalGHYLocalDensityCochain period hPeriod
      einsteinScale metric current).nonNullBoundaryDensity

/-- The single missing Stokes law for a proposed bulk-to-null restriction,
specialized to Gate 821's canonical density. -/
structure ProgramPT05CanonicalBulkToNullStokesSupport
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (restriction : ProgramPT05BulkToNullRestrictionOperator NullFace) : Prop where
  integration :
    programPT05CutBulkDensityIntegral period hPeriod
        (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod
          field test) =
      programPT05GeometricNullBoundaryDensityIntegral
        (fun face ↦ (faces face).interval)
        (programPT05CanonicalBulkToNullRestrictedDensity period hPeriod
          field test restriction)

/-- The single missing integrated trace law for a proposed GHY-to-joint
operator, specialized to Gate 824's canonical completed GHY density. -/
structure ProgramPT05CanonicalGHYToJointTraceSupport
    {NullFace : Type*} [Fintype NullFace]
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric ×
      Real)
    (trace : ProgramPT05GHYToJointTraceOperator period hPeriod NullFace) : Prop where
  integration :
    programPT05GeometricJointDensityIntegral
        (programPT05CanonicalGHYToJointTracedDensity period hPeriod
          einsteinScale metric current trace) =
      programPT05GeometricGHYDensityIntegral period hPeriod
        (programPT05CanonicalGHYLocalDensityCochain period hPeriod
          einsteinScale metric current).nonNullBoundaryDensity

/-- The two reduced operators supply the local-density fields expected by
Gate 852. -/
def programPT05CanonicalHorizontalDensityDataOfIncidence
    {NullFace : Type*}
    (field test : SmoothQuotientField period hPeriod Real)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric ×
      Real)
    (restriction : ProgramPT05BulkToNullRestrictionOperator NullFace)
    (trace : ProgramPT05GHYToJointTraceOperator period hPeriod NullFace) :
    ProgramPT05MissingHorizontalDensityData NullFace where
  bulkToNullDensity :=
    programPT05CanonicalBulkToNullRestrictedDensity period hPeriod field test
      restriction
  nonNullToJointDensity :=
    programPT05CanonicalGHYToJointTracedDensity period hPeriod einsteinScale
      metric current trace

/-- The two exact support laws assemble Gate 852's previously abstract
geometric contract. -/
theorem programPT05CanonicalHorizontalIncidence_missingGeometryContract
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric ×
      Real)
    (restriction : ProgramPT05BulkToNullRestrictionOperator NullFace)
    (trace : ProgramPT05GHYToJointTraceOperator period hPeriod NullFace)
    (hBulk : ProgramPT05CanonicalBulkToNullStokesSupport period hPeriod
      field test faces restriction)
    (hGHY : ProgramPT05CanonicalGHYToJointTraceSupport period hPeriod
      einsteinScale metric current trace) :
    ProgramPT05MissingHorizontalGeometryContract period hPeriod field test
      faces
      (programPT05CanonicalGHYLocalDensityCochain period hPeriod
        einsteinScale metric current).nonNullBoundaryDensity
      (programPT05CanonicalHorizontalDensityDataOfIncidence period hPeriod
        field test einsteinScale metric current restriction trace) := by
  constructor
  · simpa [programPT05CanonicalHorizontalDensityDataOfIncidence] using
      hBulk.integration
  · simpa [programPT05CanonicalHorizontalDensityDataOfIncidence] using
      hGHY.integration

/-- With both geometric supports, Gate 852's integrated horizontal square
commutes for the canonical cut-bulk and GHY densities. -/
theorem programPT05CanonicalHorizontalIncidence_integration_commutes
    {NullFace : Type*} [Fintype NullFace]
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric ×
      Real)
    (restriction : ProgramPT05BulkToNullRestrictionOperator NullFace)
    (trace : ProgramPT05GHYToJointTraceOperator period hPeriod NullFace)
    (hBulk : ProgramPT05CanonicalBulkToNullStokesSupport period hPeriod
      field test faces restriction)
    (hGHY : ProgramPT05CanonicalGHYToJointTraceSupport period hPeriod
      einsteinScale metric current trace)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    programPT05AvailableStratifiedIntegratedDH
        (programPT05ContractCompletedHorizontalSource period hPeriod field test
          faces
          (programPT05CanonicalGHYLocalDensityCochain period hPeriod
            einsteinScale metric current).nonNullBoundaryDensity) =
      programPT05ContractCompletedHorizontalTarget period hPeriod field test
        faces
        (programPT05CanonicalHorizontalDensityDataOfIncidence period hPeriod
          field test einsteinScale metric current restriction trace) := by
  exact programPT05ContractCompletedHorizontal_integration_commutes
    period hPeriod massSquared field test faces
    (programPT05CanonicalGHYLocalDensityCochain period hPeriod
      einsteinScale metric current).nonNullBoundaryDensity
    (programPT05CanonicalHorizontalDensityDataOfIncidence period hPeriod
      field test einsteinScale metric current restriction trace)
    (programPT05CanonicalHorizontalIncidence_missingGeometryContract
      period hPeriod field test faces einsteinScale metric current restriction
      trace hBulk hGHY)
    contracts

/-- The resulting integrated target is a horizontal cycle by Gate 819's
already proved cellular square-zero law.  Existence of either geometric
support remains an input. -/
theorem programPT05CanonicalHorizontalIncidence_target_isCycle
    {NullFace : Type*} [Fintype NullFace]
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric ×
      Real)
    (restriction : ProgramPT05BulkToNullRestrictionOperator NullFace)
    (trace : ProgramPT05GHYToJointTraceOperator period hPeriod NullFace)
    (hBulk : ProgramPT05CanonicalBulkToNullStokesSupport period hPeriod
      field test faces restriction)
    (hGHY : ProgramPT05CanonicalGHYToJointTraceSupport period hPeriod
      einsteinScale metric current trace)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    programPT05AvailableStratifiedIntegratedDHNext
        (programPT05ContractCompletedHorizontalTarget period hPeriod field test
          faces
          (programPT05CanonicalHorizontalDensityDataOfIncidence period hPeriod
            field test einsteinScale metric current restriction trace)) = 0 := by
  exact programPT05ContractCompletedHorizontalTarget_isCycle
    period hPeriod massSquared field test faces
    (programPT05CanonicalGHYLocalDensityCochain period hPeriod
      einsteinScale metric current).nonNullBoundaryDensity
    (programPT05CanonicalHorizontalDensityDataOfIncidence period hPeriod
      field test einsteinScale metric current restriction trace)
    (programPT05CanonicalHorizontalIncidence_missingGeometryContract
      period hPeriod field test faces einsteinScale metric current restriction
      trace hBulk hGHY)
    contracts

end
end P0EFTJanusProgramPT05HorizontalGeometricIncidenceSupport4D
end JanusFormal
