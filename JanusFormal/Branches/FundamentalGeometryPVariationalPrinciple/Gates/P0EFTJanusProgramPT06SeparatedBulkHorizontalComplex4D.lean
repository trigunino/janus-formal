import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalNonNullTargetFullDHObstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DirectionalNullJointJetStokesBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05MissingHorizontalGeometricContracts4D

/-!
# Separated bulk horizontal complex

The Gate-819 differential copies one bulk component to both boundary strata.
Gate 893, however, realizes only the non-null incidence.  This gate replaces
that first integrated step by two typed source slots: one for the non-null
incidence and one for the still-separate null incidence.

The next Gate-819 step vanishes exactly when the two integrated bulk values
agree.  Restricting to that compatibility submodule therefore gives a
two-step horizontal sequence with zero composite while retaining the existing
null-to-joint source and differential unchanged.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06SeparatedBulkHorizontalComplex4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05CutBulkLocalDensityStokesBridge4D
open P0EFTJanusProgramPT05NullJointLocalDensityIncidence4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05AvailableStratifiedHorizontalComplex4D
open P0EFTJanusProgramPT05MissingHorizontalGeometricContracts4D
open P0EFTJanusProgramPT06AffineJetCutBulkStokesBridge4D
open P0EFTJanusProgramPT06DirectionalNullJointJetStokesBridge4D

/-- Separate integrated bulk values for the non-null and null incidences. -/
abbrev ProgramPT06SeparatedBulkHorizontalRawSource :=
  ProgramPT05PhysicalJetComponent .bulk 4 0 ×
    ProgramPT05PhysicalJetComponent .bulk 4 0

/-- The first horizontal step reads the two boundary incidences from their
distinct source slots. -/
def programPT06SeparatedBulkIntegratedDH :
    ProgramPT06SeparatedBulkHorizontalRawSource →ₗ[Real]
      RelativeJetCochain ProgramPT05PhysicalJetComponent 5 0 where
  toFun source
    | .bulk => 0
    | .nonNullBoundary => source.1
    | .nullBoundary => source.2
    | .joint => 0
  map_add' first second := by
    funext stratum
    cases stratum <;> simp
  map_smul' scalar source := by
    funext stratum
    cases stratum <;> simp

@[simp] theorem programPT06SeparatedBulkIntegratedDH_nonNullBoundary
    (source : ProgramPT06SeparatedBulkHorizontalRawSource) :
    programPT06SeparatedBulkIntegratedDH source .nonNullBoundary =
      source.1 := by
  rfl

@[simp] theorem programPT06SeparatedBulkIntegratedDH_nullBoundary
    (source : ProgramPT06SeparatedBulkHorizontalRawSource) :
    programPT06SeparatedBulkIntegratedDH source .nullBoundary = source.2 := by
  rfl

/-- The only square-zero defect of the separated first step is the mismatch
between its two independently supplied bulk values. -/
theorem programPT06SeparatedBulkIntegratedDH_next_eq_zero_iff
    (source : ProgramPT06SeparatedBulkHorizontalRawSource) :
    programPT05ExactT03RelativeBicomplex.dH 5 0
        (programPT06SeparatedBulkIntegratedDH source) = 0 ↔
      source.1 = source.2 := by
  constructor
  · intro hZero
    have hJoint := congrFun hZero RelativeJetStratum4D.joint
    exact sub_eq_zero.mp (by
      simpa [programPT05ExactT03RelativeBicomplex,
        programPT05RelativeHorizontalDifferential,
        programPT06SeparatedBulkIntegratedDH] using hJoint)
  · intro hAgreement
    funext stratum
    cases stratum <;>
      simp [programPT05ExactT03RelativeBicomplex,
        programPT05RelativeHorizontalDifferential,
        programPT06SeparatedBulkIntegratedDH, hAgreement]

/-- Linear compatibility locus on which the two geometric sources represent
the same integrated bulk class. -/
def programPT06CompatibleSeparatedBulkSourceSubmodule :
    Submodule Real ProgramPT06SeparatedBulkHorizontalRawSource where
  carrier source := source.1 = source.2
  zero_mem' := rfl
  add_mem' := by
    intro first second hFirst hSecond
    change first.1 = first.2 at hFirst
    change second.1 = second.2 at hSecond
    change first.1 + second.1 = first.2 + second.2
    rw [hFirst, hSecond]
  smul_mem' := by
    intro scalar source hSource
    change source.1 = source.2 at hSource
    change scalar • source.1 = scalar • source.2
    rw [hSource]

abbrev ProgramPT06CompatibleSeparatedBulkHorizontalSource :=
  ↥(programPT06CompatibleSeparatedBulkSourceSubmodule)

/-- The separated first step restricted to compatible integrated sources. -/
def programPT06CompatibleSeparatedBulkIntegratedDH :
  ProgramPT06CompatibleSeparatedBulkHorizontalSource →ₗ[Real]
      RelativeJetCochain ProgramPT05PhysicalJetComponent 5 0 :=
  programPT06SeparatedBulkIntegratedDH.comp
    (programPT06CompatibleSeparatedBulkSourceSubmodule).subtype

theorem programPT06CompatibleSeparatedBulkIntegratedDH_squared
    (source : ProgramPT06CompatibleSeparatedBulkHorizontalSource) :
    programPT05ExactT03RelativeBicomplex.dH 5 0
        (programPT06CompatibleSeparatedBulkIntegratedDH source) = 0 := by
  have hAgreement :
      (source : ProgramPT06SeparatedBulkHorizontalRawSource).1 =
        (source : ProgramPT06SeparatedBulkHorizontalRawSource).2 := by
    exact source.property
  simpa [programPT06CompatibleSeparatedBulkIntegratedDH] using
    (programPT06SeparatedBulkIntegratedDH_next_eq_zero_iff
      (source : ProgramPT06SeparatedBulkHorizontalRawSource)).2 hAgreement

/-- Corrected graded source: two compatible bulk-incidence values together
with the existing degree-three boundary source. -/
abbrev ProgramPT06SeparatedStratifiedHorizontalSource :=
  ProgramPT06CompatibleSeparatedBulkHorizontalSource ×
    RelativeJetCochain ProgramPT05PhysicalJetComponent 3 0

/-- Corrected first step.  The null-to-joint factor remains the exact
Gate-819 operator used by Gate 899. -/
def programPT06SeparatedStratifiedIntegratedDH :
    ProgramPT06SeparatedStratifiedHorizontalSource →ₗ[Real]
      ProgramPT05AvailableStratifiedHorizontalTarget where
  toFun source :=
    (programPT06CompatibleSeparatedBulkIntegratedDH source.1,
      programPT05ExactT03RelativeBicomplex.dH 3 0 source.2)
  map_add' first second := by
    apply Prod.ext <;> simp
  map_smul' scalar source := by
    apply Prod.ext <;> simp

/-- The corrected graded operator is square-zero on every compatible source. -/
theorem programPT06SeparatedStratifiedIntegratedDH_squared
    (source : ProgramPT06SeparatedStratifiedHorizontalSource) :
    programPT05AvailableStratifiedIntegratedDHNext
        (programPT06SeparatedStratifiedIntegratedDH source) = 0 := by
  apply Prod.ext
  · simpa [programPT05AvailableStratifiedIntegratedDHNext,
      programPT06SeparatedStratifiedIntegratedDH] using
      programPT06CompatibleSeparatedBulkIntegratedDH_squared source.1
  · simpa [programPT05AvailableStratifiedIntegratedDHNext,
      programPT06SeparatedStratifiedIntegratedDH] using
      (programPT05ExactT03RelativeBicomplex.dH_dH 3 0 source.2)

/-- Operator form of the separated two-step zero-composite law. -/
theorem programPT06SeparatedStratifiedIntegratedDH_comp_eq_zero :
    programPT05AvailableStratifiedIntegratedDHNext.comp
        programPT06SeparatedStratifiedIntegratedDH = 0 := by
  apply LinearMap.ext
  intro source
  exact programPT06SeparatedStratifiedIntegratedDH_squared source

/-- Gates 899/905 occupy the unchanged second factor of the separated
sequence. -/
theorem programPT06DirectionalNullJointJet_dH_joint_in_separatedComplex
    (bulkSource : ProgramPT06CompatibleSeparatedBulkHorizontalSource)
    (assignedDirection : Fin 3)
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) :
    (programPT06SeparatedStratifiedIntegratedDH
      (bulkSource,
        programPT05NullBoundaryDensityIntegratedCochain face
          (programPT06DirectionalNullJointJetLocalDensityCochain
            assignedDirection face))).2 .joint =
      (programPT05JointDensityIntegratedCochain
        (programPT06DirectionalNullJointJetLocalDensityCochain
          assignedDirection face)) .joint := by
  simpa [programPT06SeparatedStratifiedIntegratedDH] using
    programPT06DirectionalNullJointJetLocalDensity_dH_joint
      assignedDirection face contract

variable (period : Real) (hPeriod : period ≠ 0)

/-- The Gate-893 non-null bulk value and the contract-supplied null bulk value
form two distinct sources.  The missing bulk-to-null integration law is
exactly their compatibility proof. -/
def programPT06ContractCompatibleSeparatedBulkSource
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (data : ProgramPT05MissingHorizontalDensityData NullFace)
    (hBulkToNull :
      programPT05CutBulkDensityIntegral period hPeriod
          (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod
            field test) =
        programPT05GeometricNullBoundaryDensityIntegral
          (fun face ↦ (faces face).interval) data.bulkToNullDensity) :
    ProgramPT06CompatibleSeparatedBulkHorizontalSource := by
  refine ⟨
    ((programPT05CutBulkDensityIntegratedCochain period hPeriod
      (programPT06CanonicalCutBulkJetLocalDensityCochain period hPeriod
        field test)) .bulk,
    (programPT05GeometricNullBoundaryDensityIntegral
      (fun face ↦ (faces face).interval) data.bulkToNullDensity, 0)), ?_⟩
  change
    (programPT05CutBulkDensityIntegratedCochain period hPeriod
      (programPT06CanonicalCutBulkJetLocalDensityCochain period hPeriod
        field test)) .bulk =
      (programPT05GeometricNullBoundaryDensityIntegral
        (fun face ↦ (faces face).interval) data.bulkToNullDensity, 0)
  apply Prod.ext
  · change
      programPT05CutBulkDensityIntegral period hPeriod
          (programPT06CanonicalCutBulkJetLocalDensityCochain period hPeriod
            field test) =
        programPT05GeometricNullBoundaryDensityIntegral
          (fun face ↦ (faces face).interval) data.bulkToNullDensity
    rw [programPT06CanonicalCutBulkJetLocalDensityCochain_eq_geometric]
    exact hBulkToNull
  · rfl

/-- Gate 852's conditional completed target is unchanged, but now arises from
two separately typed bulk sources instead of copying the non-null source into
the null slot. -/
theorem programPT06ContractSeparatedBulkIntegration_commutes
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (data : ProgramPT05MissingHorizontalDensityData NullFace)
    (hBulkToNull :
      programPT05CutBulkDensityIntegral period hPeriod
          (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod
            field test) =
        programPT05GeometricNullBoundaryDensityIntegral
          (fun face ↦ (faces face).interval) data.bulkToNullDensity) :
    programPT06CompatibleSeparatedBulkIntegratedDH
        (programPT06ContractCompatibleSeparatedBulkSource period hPeriod
          field test faces data hBulkToNull) =
      programPT05ContractCompletedCutBulkHorizontalTarget period hPeriod
        field test faces data := by
  funext stratum
  cases stratum with
  | bulk => rfl
  | nonNullBoundary =>
      change
        (programPT05CutBulkDensityIntegral period hPeriod
          (programPT06CanonicalCutBulkJetLocalDensityCochain period hPeriod
            field test), 0) =
        (-programPT05NonNullBoundaryDensityIntegral period hPeriod
          (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod
            field test), 0)
      rw [programPT06CanonicalCutBulkJetLocalDensityCochain_eq_geometric]
      rw [programPT05CanonicalCutBulkLocalDensity_stokes period hPeriod
        0 field test]
  | nullBoundary => rfl
  | joint => rfl

end
end P0EFTJanusProgramPT06SeparatedBulkHorizontalComplex4D
end JanusFormal
