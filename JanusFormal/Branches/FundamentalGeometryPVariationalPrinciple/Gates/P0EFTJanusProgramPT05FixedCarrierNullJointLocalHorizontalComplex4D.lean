import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05FixedCarrierNullJointLocalBicomplex4D

/-!
# Fixed-carrier null/joint local horizontal complex

Gate 849 constructs the local horizontal edge from a null transgression to
its oriented joint traces.  The joint stratum has no outgoing incidence in
Gate 819.  This module represents that empty successor explicitly, proves
that the local horizontal differential squares to zero, and shows that the
second edge commutes with integration in contact degrees zero and one.

Together with Gate 849's FTOC theorem this gives a two-step local horizontal
complex on the normalization-transgression sub-fibre.  It does not construct
the missing bulk-to-null restriction or a non-null-boundary-to-joint corner
trace; those require new geometric trace and Stokes data.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05FixedCarrierNullJointLocalHorizontalComplex4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05FixedCarrierNullJointLocalBicomplex4D

/-- The empty family of local density carriers after the joint stratum. -/
abbrev ProgramPT05FixedCarrierJointHorizontalSuccessorDensity := Fin 0 → Real

/-- There is no outgoing local incidence from a joint. -/
def programPT05FixedCarrierJointLocalDHNext
    {NullFace : Type*}
    (_jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real) :
    ProgramPT05FixedCarrierJointHorizontalSuccessorDensity :=
  0

/-- The fixed-carrier null-to-joint local horizontal differential squares to
zero before integration. -/
@[simp]
theorem programPT05FixedCarrierNullJointLocalDH_squared
    {NullFace : Type*}
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval) :
    programPT05FixedCarrierJointLocalDHNext
        (programPT05FixedCarrierNullJointLocalDH density) = 0 := by
  rfl

/-- The same local square-zero law in contact degree one. -/
@[simp]
theorem programPT05FixedCarrierNullJointVerticalLocalDH_squared
    {NullFace : Type*}
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierNullJointVerticalTransgressionDensity
      NullFace nullFaceInterval) :
    programPT05FixedCarrierJointLocalDHNext
        (programPT05FixedCarrierNullJointVerticalLocalDH density) = 0 := by
  rfl

/-- Integration of the empty successor is the zero relative cochain. -/
def programPT05IntegrateFixedCarrierJointHorizontalSuccessor
    (contactDegree : Nat)
    (_density : ProgramPT05FixedCarrierJointHorizontalSuccessorDensity) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 5 contactDegree :=
  0

/-- Gate 849's integrated joint target is killed by the next Gate-819
horizontal differential, exactly as its empty local successor is. -/
theorem programPT05FixedCarrierJointLocalDHNext_integration_commutes
    {NullFace : Type*} [Fintype NullFace]
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval) :
    programPT05ExactT03RelativeBicomplex.dH 4 0
        (programPT05IntegrateFixedCarrierNullJointTarget density) =
      programPT05IntegrateFixedCarrierJointHorizontalSuccessor 0
        (programPT05FixedCarrierJointLocalDHNext
          (programPT05FixedCarrierNullJointLocalDH density)) := by
  funext stratum
  cases stratum <;>
    simp [programPT05IntegrateFixedCarrierNullJointTarget,
      programPT05IntegrateFixedCarrierJointHorizontalSuccessor,
      programPT05FixedCarrierJointLocalDHNext,
      programPT05ExactT03RelativeBicomplex,
      programPT05RelativeHorizontalDifferential]

/-- Integration of a contact-degree-one joint trace. -/
def programPT05IntegrateFixedCarrierNullJointVerticalTarget
    {NullFace : Type*} [Fintype NullFace]
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierNullJointVerticalTransgressionDensity
      NullFace nullFaceInterval) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 1
  | .bulk => 0
  | .nonNullBoundary => 0
  | .nullBoundary => 0
  | .joint =>
      (0, programPT05GeometricJointDensityIntegral
        (programPT05FixedCarrierNullJointVerticalLocalDH density))

/-- The empty second horizontal edge also commutes with integration in contact
degree one. -/
theorem programPT05FixedCarrierJointVerticalLocalDHNext_integration_commutes
    {NullFace : Type*} [Fintype NullFace]
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierNullJointVerticalTransgressionDensity
      NullFace nullFaceInterval) :
    programPT05ExactT03RelativeBicomplex.dH 4 1
        (programPT05IntegrateFixedCarrierNullJointVerticalTarget density) =
      programPT05IntegrateFixedCarrierJointHorizontalSuccessor 1
        (programPT05FixedCarrierJointLocalDHNext
          (programPT05FixedCarrierNullJointVerticalLocalDH density)) := by
  funext stratum
  cases stratum <;>
    simp [programPT05IntegrateFixedCarrierNullJointVerticalTarget,
      programPT05IntegrateFixedCarrierJointHorizontalSuccessor,
      programPT05FixedCarrierJointLocalDHNext,
      programPT05ExactT03RelativeBicomplex,
      programPT05RelativeHorizontalDifferential]

/-- The canonical finite-family FTOC edge and the empty joint successor form
a two-step integration morphism. -/
theorem programPT05CanonicalFixedCarrierNullJointHorizontalComplex_commutes
    {NullFace : Type*} [Fintype NullFace]
    (faces : NullFace → FiniteNullFaceActionDatum)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    programPT05ExactT03RelativeBicomplex.dH 3 0
        (programPT05IntegrateFixedCarrierNullTransgressionSource
          (fun face ↦ (faces face).interval)
          (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
            faces)) =
      programPT05IntegrateFixedCarrierNullJointTarget
          (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
            faces) ∧
    programPT05ExactT03RelativeBicomplex.dH 4 0
        (programPT05IntegrateFixedCarrierNullJointTarget
          (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
            faces)) = 0 := by
  constructor
  · exact programPT05CanonicalFixedCarrierNullJointLocalDH_integration_commutes
      faces contracts
  · simpa [programPT05IntegrateFixedCarrierJointHorizontalSuccessor] using
      (programPT05FixedCarrierJointLocalDHNext_integration_commutes
        (programPT05CanonicalFixedCarrierNullJointTransgressionDensity faces))

end
end P0EFTJanusProgramPT05FixedCarrierNullJointLocalHorizontalComplex4D
end JanusFormal
