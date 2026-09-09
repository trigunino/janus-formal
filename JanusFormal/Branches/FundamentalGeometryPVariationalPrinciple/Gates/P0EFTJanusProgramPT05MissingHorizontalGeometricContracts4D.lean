import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05AvailableStratifiedHorizontalComplex4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05FixedCarrierNullJointLocalHorizontalComplex4D

/-!
# Minimal contracts for the two missing horizontal incidences

The implemented local horizontal pieces cover the cut-bulk to non-null edge
and the null-transgression to joint edge.  No existing theorem supplies a
cut-bulk to null restriction or a non-null GHY density trace at the joints.

This module isolates exactly those two missing geometric inputs.  The data are
an actual null-face density and an actual joint density.  The two contract
fields state only their sectorwise integration laws.  From them, the existing
Stokes and FTOC theorems give both completed horizontal commuting squares and
the square-zero law on their graded product.

The contracts are not constructed here.  In particular, this is not a full
local-density bicomplex or a closure certificate for T05.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05MissingHorizontalGeometricContracts4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05CutBulkLocalDensityStokesBridge4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05AvailableStratifiedHorizontalComplex4D
open P0EFTJanusProgramPT05FixedCarrierNullJointLocalBicomplex4D

/-- Local representatives for the two incidence arrows that have no current
geometric construction. -/
structure ProgramPT05MissingHorizontalDensityData (NullFace : Type*) where
  bulkToNullDensity : NullFace → Real → Real
  nonNullToJointDensity :
    NullFace → ProgramPT05NullJointEndpoint → Real

variable (period : Real) (hPeriod : period ≠ 0)

/-- The two missing integration laws, kept separate from their local density
data.  The first is the absent bulk-to-null restriction/Stokes identity.  The
second is the absent oriented non-null-to-joint GHY trace identity. -/
structure ProgramPT05MissingHorizontalGeometryContract
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (nonNullBoundaryDensity :
      CandidateANormalBoundaryScalarField period hPeriod)
    (data : ProgramPT05MissingHorizontalDensityData NullFace) : Prop where
  bulkToNull_integration :
    programPT05CutBulkDensityIntegral period hPeriod
        (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod
          field test) =
      programPT05GeometricNullBoundaryDensityIntegral
        (fun face ↦ (faces face).interval) data.bulkToNullDensity
  nonNullToJoint_integration :
    programPT05GeometricJointDensityIntegral data.nonNullToJointDensity =
      programPT05GeometricGHYDensityIntegral period hPeriod
        nonNullBoundaryDensity

/-- Full degree-four cut-bulk target after adding the contracted null-face
component to the already proved non-null component. -/
def programPT05ContractCompletedCutBulkHorizontalTarget
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (data : ProgramPT05MissingHorizontalDensityData NullFace) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 5 0
  | .bulk => 0
  | .nonNullBoundary =>
      (-programPT05NonNullBoundaryDensityIntegral period hPeriod
        (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod
          field test), 0)
  | .nullBoundary =>
      (programPT05GeometricNullBoundaryDensityIntegral
        (fun face ↦ (faces face).interval) data.bulkToNullDensity, 0)
  | .joint => 0

/-- The completed cut-bulk local target commutes with Gate 819's whole first
horizontal step, conditional only on the missing bulk-to-null law. -/
theorem programPT05ContractCompletedCutBulkHorizontal_integration_commutes
    {NullFace : Type*} [Fintype NullFace]
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (nonNullBoundaryDensity :
      CandidateANormalBoundaryScalarField period hPeriod)
    (data : ProgramPT05MissingHorizontalDensityData NullFace)
    (contract : ProgramPT05MissingHorizontalGeometryContract period hPeriod
      field test faces nonNullBoundaryDensity data) :
    programPT05ExactT03RelativeBicomplex.dH 4 0
        (programPT05CutBulkDensityIntegratedCochain period hPeriod
          (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod
            field test)) =
      programPT05ContractCompletedCutBulkHorizontalTarget period hPeriod
        field test faces data := by
  funext stratum
  cases stratum with
  | bulk => rfl
  | nonNullBoundary =>
      apply Prod.ext
      · exact programPT05CanonicalCutBulkLocalDensity_stokes period hPeriod
          massSquared field test
      · rfl
  | nullBoundary =>
      apply Prod.ext
      · exact contract.bulkToNull_integration
      · rfl
  | joint =>
      simp [programPT05ExactT03RelativeBicomplex,
        programPT05RelativeHorizontalDifferential,
        programPT05CutBulkDensityIntegratedCochain,
        programPT05ContractCompletedCutBulkHorizontalTarget]

/-- Boundary source containing an actual GHY density and Gate 849's canonical
null transgression, both in horizontal degree three. -/
def programPT05ContractCompletedBoundaryHorizontalSource
    {NullFace : Type*} [Fintype NullFace]
    (faces : NullFace → FiniteNullFaceActionDatum)
    (nonNullBoundaryDensity :
      CandidateANormalBoundaryScalarField period hPeriod) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 3 0
  | .bulk => 0
  | .nonNullBoundary =>
      (programPT05GeometricGHYDensityIntegral period hPeriod
        nonNullBoundaryDensity, 0)
  | .nullBoundary =>
      (programPT05GeometricNullBoundaryDensityIntegral
        (fun face ↦ (faces face).interval)
        (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
          faces).nullBoundaryDensity, 0)
  | .joint => 0

/-- Sum of the contracted non-null corner trace and the already constructed
oriented null corner trace. -/
def programPT05ContractCompletedBoundaryJointDensity
    {NullFace : Type*}
    (faces : NullFace → FiniteNullFaceActionDatum)
    (data : ProgramPT05MissingHorizontalDensityData NullFace)
    (face : NullFace) (endpoint : ProgramPT05NullJointEndpoint) : Real :=
  data.nonNullToJointDensity face endpoint +
    (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
      faces).jointDensity face endpoint

/-- Integrated joint target of the completed degree-three boundary source. -/
def programPT05ContractCompletedBoundaryHorizontalTarget
    {NullFace : Type*} [Fintype NullFace]
    (faces : NullFace → FiniteNullFaceActionDatum)
    (data : ProgramPT05MissingHorizontalDensityData NullFace) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0
  | .bulk => 0
  | .nonNullBoundary => 0
  | .nullBoundary => 0
  | .joint =>
      (programPT05GeometricJointDensityIntegral
        (programPT05ContractCompletedBoundaryJointDensity faces data), 0)

/-- Integration distributes over the two local joint traces. -/
theorem programPT05ContractCompletedBoundaryJointDensity_integral
    {NullFace : Type*} [Fintype NullFace]
    (faces : NullFace → FiniteNullFaceActionDatum)
    (data : ProgramPT05MissingHorizontalDensityData NullFace) :
    programPT05GeometricJointDensityIntegral
        (programPT05ContractCompletedBoundaryJointDensity faces data) =
      programPT05GeometricJointDensityIntegral
          data.nonNullToJointDensity +
        programPT05GeometricJointDensityIntegral
          (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
            faces).jointDensity := by
  unfold programPT05GeometricJointDensityIntegral
    programPT05ContractCompletedBoundaryJointDensity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro face _
  ring

/-- Gate 849's canonical null trace integrates to the negative of its source
density, with no new geometric input. -/
theorem programPT05CanonicalFixedCarrierNullJointTrace_integral
    {NullFace : Type*} [Fintype NullFace]
    (faces : NullFace → FiniteNullFaceActionDatum)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    programPT05GeometricJointDensityIntegral
        (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
          faces).jointDensity =
      -programPT05GeometricNullBoundaryDensityIntegral
        (fun face ↦ (faces face).interval)
        (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
          faces).nullBoundaryDensity := by
  have h := congrArg
    (fun cochain => (cochain RelativeJetStratum4D.joint).1)
    (programPT05CanonicalFixedCarrierNullJointLocalDH_integration_commutes
      faces contracts)
  change
    0 - programPT05GeometricNullBoundaryDensityIntegral
        (fun face ↦ (faces face).interval)
        (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
          faces).nullBoundaryDensity =
      programPT05GeometricJointDensityIntegral
        (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
          faces).jointDensity at h
  linarith

/-- The completed non-null/null boundary source commutes with its whole local
joint target.  The only unproved input used here is the non-null corner trace
field of the contract. -/
theorem programPT05ContractCompletedBoundaryHorizontal_integration_commutes
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (nonNullBoundaryDensity :
      CandidateANormalBoundaryScalarField period hPeriod)
    (data : ProgramPT05MissingHorizontalDensityData NullFace)
    (contract : ProgramPT05MissingHorizontalGeometryContract period hPeriod
      field test faces nonNullBoundaryDensity data)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    programPT05ExactT03RelativeBicomplex.dH 3 0
        (programPT05ContractCompletedBoundaryHorizontalSource period hPeriod
          faces nonNullBoundaryDensity) =
      programPT05ContractCompletedBoundaryHorizontalTarget faces data := by
  funext stratum
  cases stratum with
  | bulk => rfl
  | nonNullBoundary => rfl
  | nullBoundary => rfl
  | joint =>
      apply Prod.ext
      · change
          programPT05GeometricGHYDensityIntegral period hPeriod
                nonNullBoundaryDensity -
              programPT05GeometricNullBoundaryDensityIntegral
                (fun face ↦ (faces face).interval)
                (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
                  faces).nullBoundaryDensity =
            programPT05GeometricJointDensityIntegral
              (programPT05ContractCompletedBoundaryJointDensity faces data)
        rw [programPT05ContractCompletedBoundaryJointDensity_integral,
          contract.nonNullToJoint_integration,
          programPT05CanonicalFixedCarrierNullJointTrace_integral faces
            contracts]
        ring
      · simp [programPT05ExactT03RelativeBicomplex,
          programPT05RelativeHorizontalDifferential,
          programPT05ContractCompletedBoundaryHorizontalSource,
          programPT05ContractCompletedBoundaryHorizontalTarget]

/-- Graded source for the two now-completed horizontal component maps. -/
def programPT05ContractCompletedHorizontalSource
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (nonNullBoundaryDensity :
      CandidateANormalBoundaryScalarField period hPeriod) :
    ProgramPT05AvailableStratifiedHorizontalSource :=
  (programPT05CutBulkDensityIntegratedCochain period hPeriod
      (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod
        field test),
    programPT05ContractCompletedBoundaryHorizontalSource period hPeriod faces
      nonNullBoundaryDensity)

/-- Graded target with both formerly missing components populated. -/
def programPT05ContractCompletedHorizontalTarget
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (data : ProgramPT05MissingHorizontalDensityData NullFace) :
    ProgramPT05AvailableStratifiedHorizontalTarget :=
  (programPT05ContractCompletedCutBulkHorizontalTarget period hPeriod field
      test faces data,
    programPT05ContractCompletedBoundaryHorizontalTarget faces data)

/-- Under exactly the two displayed geometric contracts, integration commutes
with both completed components of the graded horizontal differential. -/
theorem programPT05ContractCompletedHorizontal_integration_commutes
    {NullFace : Type*} [Fintype NullFace]
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (nonNullBoundaryDensity :
      CandidateANormalBoundaryScalarField period hPeriod)
    (data : ProgramPT05MissingHorizontalDensityData NullFace)
    (contract : ProgramPT05MissingHorizontalGeometryContract period hPeriod
      field test faces nonNullBoundaryDensity data)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    programPT05AvailableStratifiedIntegratedDH
        (programPT05ContractCompletedHorizontalSource period hPeriod field test
          faces nonNullBoundaryDensity) =
      programPT05ContractCompletedHorizontalTarget period hPeriod field test
        faces data := by
  apply Prod.ext
  · exact programPT05ContractCompletedCutBulkHorizontal_integration_commutes
      period hPeriod massSquared field test faces nonNullBoundaryDensity data
        contract
  · exact programPT05ContractCompletedBoundaryHorizontal_integration_commutes
      period hPeriod field test faces nonNullBoundaryDensity data contract
        contracts

/-- The completed geometric target is an integrated horizontal cycle.  This
is a consequence of the proved Gate-819 square-zero law, not another field of
the geometric contract. -/
theorem programPT05ContractCompletedHorizontalTarget_isCycle
    {NullFace : Type*} [Fintype NullFace]
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (nonNullBoundaryDensity :
      CandidateANormalBoundaryScalarField period hPeriod)
    (data : ProgramPT05MissingHorizontalDensityData NullFace)
    (contract : ProgramPT05MissingHorizontalGeometryContract period hPeriod
      field test faces nonNullBoundaryDensity data)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    programPT05AvailableStratifiedIntegratedDHNext
        (programPT05ContractCompletedHorizontalTarget period hPeriod field test
          faces data) = 0 := by
  rw [← programPT05ContractCompletedHorizontal_integration_commutes
    period hPeriod massSquared field test faces nonNullBoundaryDensity data
      contract contracts]
  exact programPT05AvailableStratifiedIntegratedDH_squared _

end
end P0EFTJanusProgramPT05MissingHorizontalGeometricContracts4D
end JanusFormal
