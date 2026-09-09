import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05FixedCarrierNullJointLocalHorizontalComplex4D

/-!
# Affine null-to-joint local exactness

On every nondegenerate fixed oriented null interval, two prescribed joint
values admit an explicit affine null-density extension.  This extension is a
right inverse to Gate 849's local null-to-joint differential, so the Gate 850
two-step complex is exact at its joint term on this trace-compatible
sub-fibre.

The integration statement below records the exact Stokes residual of this
extension.  It does not assert a bulk-to-null edge or force an arbitrary
affine extension to satisfy the geometric transgression identity.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05AffineNullJointLocalExactness4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05FixedCarrierNullJointLocalBicomplex4D
open P0EFTJanusProgramPT05FixedCarrierNullJointLocalHorizontalComplex4D

/-- Affine interpolation of two endpoint values on an oriented interval. -/
def programPT05OrientedAffineNullDensity
    (interval : OrientedNullInterval)
    (endpointDensity : ProgramPT05NullJointEndpoint → Real)
    (parameter : Real) : Real :=
  endpointDensity .initial +
    ((parameter - interval.initialParameter) /
      (interval.finalParameter - interval.initialParameter)) *
        (endpointDensity .final - endpointDensity .initial)

@[simp]
theorem programPT05OrientedAffineNullDensity_initial
    (interval : OrientedNullInterval)
    (endpointDensity : ProgramPT05NullJointEndpoint → Real) :
    programPT05OrientedAffineNullDensity interval endpointDensity
        interval.initialParameter = endpointDensity .initial := by
  simp [programPT05OrientedAffineNullDensity]

@[simp]
theorem programPT05OrientedAffineNullDensity_final
    (interval : OrientedNullInterval)
    (endpointDensity : ProgramPT05NullJointEndpoint → Real)
    (hNondegenerate :
      interval.finalParameter ≠ interval.initialParameter) :
    programPT05OrientedAffineNullDensity interval endpointDensity
        interval.finalParameter = endpointDensity .final := by
  have hLength :
      interval.finalParameter - interval.initialParameter ≠ 0 :=
    sub_ne_zero.mpr hNondegenerate
  rw [programPT05OrientedAffineNullDensity, div_self hLength]
  ring

/-- A source is trace-compatible when its stored joint values are its actual
endpoint evaluations. -/
def ProgramPT05FixedCarrierNullJointTraceCompatible
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval) : Prop :=
  ∀ face,
    density.nullBoundaryDensity face
          (nullFaceInterval face).initialParameter =
        density.jointDensity face .initial ∧
      density.nullBoundaryDensity face
          (nullFaceInterval face).finalParameter =
        density.jointDensity face .final

/-- Explicit affine extension of an arbitrary joint density. -/
def programPT05FixedCarrierAffineNullJointRightInverse
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real) :
    ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval where
  nullBoundaryDensity := fun face ↦
    programPT05OrientedAffineNullDensity (nullFaceInterval face)
      (jointDensity face)
  jointDensity := jointDensity

/-- On nondegenerate intervals the affine extension has the prescribed
endpoint traces. -/
theorem programPT05FixedCarrierAffineNullJointRightInverse_traceCompatible
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (hNondegenerate : ∀ face,
      (nullFaceInterval face).finalParameter ≠
        (nullFaceInterval face).initialParameter)
    (jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real) :
    ProgramPT05FixedCarrierNullJointTraceCompatible nullFaceInterval
      (programPT05FixedCarrierAffineNullJointRightInverse nullFaceInterval
        jointDensity) := by
  intro face
  constructor
  · exact programPT05OrientedAffineNullDensity_initial
      (nullFaceInterval face) (jointDensity face)
  · exact programPT05OrientedAffineNullDensity_final
      (nullFaceInterval face) (jointDensity face) (hNondegenerate face)

/-- Gate 849's local horizontal differential has the affine extension as an
explicit right inverse. -/
@[simp]
theorem programPT05FixedCarrierNullJointLocalDH_affineRightInverse
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real) :
    programPT05FixedCarrierNullJointLocalDH
        (programPT05FixedCarrierAffineNullJointRightInverse nullFaceInterval
          jointDensity) =
      jointDensity := by
  rfl

/-- The local null-to-joint differential is surjective. -/
theorem programPT05FixedCarrierNullJointLocalDH_surjective
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval) :
    Function.Surjective
      (fun density : ProgramPT05FixedCarrierNullJointTransgressionDensity
          NullFace nullFaceInterval ↦
        programPT05FixedCarrierNullJointLocalDH density) := by
  intro jointDensity
  exact ⟨programPT05FixedCarrierAffineNullJointRightInverse
    nullFaceInterval jointDensity, rfl⟩

/-- Under the necessary nondegeneracy hypothesis, every joint density has a
trace-compatible affine preimage. -/
theorem programPT05FixedCarrierNullJointLocalDH_traceCompatible_surjective
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (hNondegenerate : ∀ face,
      (nullFaceInterval face).finalParameter ≠
        (nullFaceInterval face).initialParameter)
    (jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real) :
    ∃ density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
        nullFaceInterval,
      ProgramPT05FixedCarrierNullJointTraceCompatible nullFaceInterval
          density ∧
        programPT05FixedCarrierNullJointLocalDH density = jointDensity := by
  exact ⟨programPT05FixedCarrierAffineNullJointRightInverse
      nullFaceInterval jointDensity,
    programPT05FixedCarrierAffineNullJointRightInverse_traceCompatible
      nullFaceInterval hNondegenerate jointDensity,
    programPT05FixedCarrierNullJointLocalDH_affineRightInverse
      nullFaceInterval jointDensity⟩

/-- A degenerate interval can only carry equal endpoint traces. -/
theorem programPT05FixedCarrierNullJointTraceCompatible_degenerate
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval)
    (hTrace : ProgramPT05FixedCarrierNullJointTraceCompatible
      nullFaceInterval density)
    (face : NullFace)
    (hDegenerate : (nullFaceInterval face).finalParameter =
      (nullFaceInterval face).initialParameter) :
    density.jointDensity face .initial =
      density.jointDensity face .final := by
  rcases hTrace face with ⟨hInitial, hFinal⟩
  rw [← hInitial, ← hFinal, hDegenerate]

/-- Retraction of all local sources onto their affine trace-compatible
representatives. -/
def programPT05FixedCarrierAffineNullJointProjection
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval) :
    ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval :=
  programPT05FixedCarrierAffineNullJointRightInverse nullFaceInterval
    (programPT05FixedCarrierNullJointLocalDH density)

@[simp]
theorem programPT05FixedCarrierAffineNullJointProjection_preserves_dH
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval) :
    programPT05FixedCarrierNullJointLocalDH
        (programPT05FixedCarrierAffineNullJointProjection nullFaceInterval
          density) =
      programPT05FixedCarrierNullJointLocalDH density := by
  rfl

@[simp]
theorem programPT05FixedCarrierAffineNullJointProjection_idempotent
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval) :
    programPT05FixedCarrierAffineNullJointProjection nullFaceInterval
        (programPT05FixedCarrierAffineNullJointProjection nullFaceInterval
          density) =
      programPT05FixedCarrierAffineNullJointProjection nullFaceInterval
        density := by
  rfl

/-- Exactness of the Gate 850 two-step local complex at the joint term. -/
theorem programPT05FixedCarrierNullJointLocalComplex_exact_at_joint
    {NullFace : Type*}
    (nullFaceInterval : NullFace → OrientedNullInterval) :
    Set.range
        (fun density : ProgramPT05FixedCarrierNullJointTransgressionDensity
            NullFace nullFaceInterval ↦
          programPT05FixedCarrierNullJointLocalDH density) =
      {jointDensity |
        programPT05FixedCarrierJointLocalDHNext jointDensity = 0} := by
  ext jointDensity
  constructor
  · intro _
    rfl
  · intro _
    exact ⟨programPT05FixedCarrierAffineNullJointRightInverse
      nullFaceInterval jointDensity, rfl⟩

/-- Integrated null contribution of the affine right inverse. -/
def programPT05FixedCarrierAffineNullIntegral
    {NullFace : Type*} [Fintype NullFace]
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real) : Real :=
  programPT05GeometricNullBoundaryDensityIntegral nullFaceInterval
    (programPT05FixedCarrierAffineNullJointRightInverse nullFaceInterval
      jointDensity).nullBoundaryDensity

@[simp]
theorem programPT05FixedCarrierAffineNullSource_integral
    {NullFace : Type*} [Fintype NullFace]
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real) :
    (programPT05IntegrateFixedCarrierNullTransgressionSource
        nullFaceInterval
        (programPT05FixedCarrierAffineNullJointRightInverse nullFaceInterval
          jointDensity) .nullBoundary).1 =
      programPT05FixedCarrierAffineNullIntegral nullFaceInterval
        jointDensity := by
  rfl

@[simp]
theorem programPT05FixedCarrierAffineJointTarget_integral
    {NullFace : Type*} [Fintype NullFace]
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real) :
    (programPT05IntegrateFixedCarrierNullJointTarget
        (programPT05FixedCarrierAffineNullJointRightInverse nullFaceInterval
          jointDensity) .joint).1 =
      programPT05GeometricJointDensityIntegral jointDensity := by
  rfl

/-- Exact integration criterion: the affine right inverse commutes with the
integrated horizontal edge exactly when its null and joint integrals satisfy
the oriented Stokes cancellation. -/
theorem programPT05FixedCarrierAffineNullJoint_integration_commutes_iff
    {NullFace : Type*} [Fintype NullFace]
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real) :
    programPT05ExactT03RelativeBicomplex.dH 3 0
        (programPT05IntegrateFixedCarrierNullTransgressionSource
          nullFaceInterval
          (programPT05FixedCarrierAffineNullJointRightInverse
            nullFaceInterval jointDensity)) =
      programPT05IntegrateFixedCarrierNullJointTarget
        (programPT05FixedCarrierAffineNullJointRightInverse
          nullFaceInterval jointDensity) ↔
    programPT05FixedCarrierAffineNullIntegral nullFaceInterval jointDensity +
        programPT05GeometricJointDensityIntegral jointDensity = 0 := by
  constructor
  · intro hCommutes
    have hJoint := congrArg Prod.fst (congrFun hCommutes .joint)
    change
      0 - programPT05FixedCarrierAffineNullIntegral nullFaceInterval
          jointDensity =
        programPT05GeometricJointDensityIntegral jointDensity at hJoint
    linarith
  · intro hStokes
    funext stratum
    cases stratum with
    | bulk => rfl
    | nonNullBoundary => rfl
    | nullBoundary => rfl
    | joint =>
        apply Prod.ext
        · change
            0 - programPT05FixedCarrierAffineNullIntegral nullFaceInterval
                jointDensity =
              programPT05GeometricJointDensityIntegral jointDensity
          linarith
        · simp [programPT05ExactT03RelativeBicomplex,
            programPT05RelativeHorizontalDifferential,
            programPT05IntegrateFixedCarrierNullTransgressionSource,
            programPT05IntegrateFixedCarrierNullJointTarget]

end
end P0EFTJanusProgramPT05AffineNullJointLocalExactness4D
end JanusFormal
