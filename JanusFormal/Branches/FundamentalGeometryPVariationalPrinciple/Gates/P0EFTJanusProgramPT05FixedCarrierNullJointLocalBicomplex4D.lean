import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05FiniteNullHorizontalIntegrationMorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05StratifiedLocalVerticalDensityComplex4D

/-!
# Fixed-carrier null/joint local bicomplex edge

This module isolates the local null-transgression fibre over fixed oriented
face intervals.  A source contains a null-face density and its two oriented
joint traces; the available local horizontal edge is the trace projection.
For the canonical reparametrization shift, Gate 823's FTOC proves that this
edge commutes with finite-family integration and Gate 819's `dH`.

The signed local vertical lifts in horizontal degrees three and four cancel
pointwise on the joint traces and satisfy the mixed identity after
integration.  This only realizes the normalization-transgression sub-fibre.
It supplies no bulk restriction, non-null incidence, or general local
horizontal differential.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05FixedCarrierNullJointLocalBicomplex4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators Interval
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05NullJointLocalDensityIncidence4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05FiniteNullHorizontalIntegrationMorphism4D
open P0EFTJanusProgramPT05StratifiedLocalVerticalDensityComplex4D

/-- Local null density together with its oriented endpoint traces, in the
fibre over fixed face intervals. -/
structure ProgramPT05FixedCarrierNullJointTransgressionDensity
    (NullFace : Type*)
    (_nullFaceInterval : NullFace → OrientedNullInterval) where
  nullBoundaryDensity : NullFace → Real → Real
  jointDensity : NullFace → ProgramPT05NullJointEndpoint → Real

/-- Canonical finite-family transgression supplied by the actual null
reparametrization shift. -/
def programPT05CanonicalFixedCarrierNullJointTransgressionDensity
    {NullFace : Type*}
    (faces : NullFace → FiniteNullFaceActionDatum) :
    ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      (fun face ↦ (faces face).interval) where
  nullBoundaryDensity := fun face ↦
    (programPT05CanonicalNullJointLocalDensityCochain
      (faces face)).nullBoundaryDensity
  jointDensity := fun face endpoint ↦
    match endpoint with
    | .initial =>
        (programPT05CanonicalNullJointLocalDensityCochain
          (faces face)).initialJointDensity
    | .final =>
        (programPT05CanonicalNullJointLocalDensityCochain
          (faces face)).finalJointDensity

/-- The genuinely available local horizontal edge: take the oriented joint
trace already carried by the null transgression. -/
def programPT05FixedCarrierNullJointLocalDH
    {NullFace : Type*}
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval) :
    NullFace → ProgramPT05NullJointEndpoint → Real :=
  density.jointDensity

/-- Integrate the horizontal source, supported on the null stratum. -/
def programPT05IntegrateFixedCarrierNullTransgressionSource
    {NullFace : Type*} [Fintype NullFace]
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 3 0
  | .bulk => 0
  | .nonNullBoundary => 0
  | .nullBoundary =>
      (programPT05GeometricNullBoundaryDensityIntegral nullFaceInterval
        density.nullBoundaryDensity, 0)
  | .joint => 0

/-- Integrate the local horizontal target, supported on the joint stratum. -/
def programPT05IntegrateFixedCarrierNullJointTarget
    {NullFace : Type*} [Fintype NullFace]
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0
  | .bulk => 0
  | .nonNullBoundary => 0
  | .nullBoundary => 0
  | .joint =>
      (programPT05GeometricJointDensityIntegral
        (programPT05FixedCarrierNullJointLocalDH density), 0)

/-- The canonical fixed-carrier source is exactly Gate 834's integrated
finite-family source. -/
theorem programPT05CanonicalFixedCarrierNullSource_eq_gate834
    {NullFace : Type*} [Fintype NullFace]
    (faces : NullFace → FiniteNullFaceActionDatum) :
    programPT05IntegrateFixedCarrierNullTransgressionSource
        (fun face ↦ (faces face).interval)
        (programPT05CanonicalFixedCarrierNullJointTransgressionDensity faces) =
      programPT05FiniteNullTransgressionSourceIntegratedCochain faces := by
  funext stratum
  cases stratum <;> rfl

/-- The canonical fixed-carrier target is exactly Gate 834's integrated joint
target. -/
theorem programPT05CanonicalFixedCarrierNullTarget_eq_gate834
    {NullFace : Type*} [Fintype NullFace]
    (faces : NullFace → FiniteNullFaceActionDatum) :
    programPT05IntegrateFixedCarrierNullJointTarget
        (programPT05CanonicalFixedCarrierNullJointTransgressionDensity faces) =
      programPT05FiniteNullTransgressionTargetIntegratedCochain faces := by
  funext stratum
  cases stratum <;> rfl

/-- On the canonical transgression sub-fibre, local `dH` commutes with
integration by the proved facewise FTOC contracts. -/
theorem programPT05CanonicalFixedCarrierNullJointLocalDH_integration_commutes
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
          faces) := by
  rw [programPT05CanonicalFixedCarrierNullSource_eq_gate834,
    programPT05CanonicalFixedCarrierNullTarget_eq_gate834]
  exact programPT05FiniteNullTransgressionIntegration_commutes_dH
    faces contracts

/-- Contact-degree-one local transgression in horizontal degree three. -/
structure ProgramPT05FixedCarrierNullJointVerticalTransgressionDensity
    (NullFace : Type*)
    (_nullFaceInterval : NullFace → OrientedNullInterval) where
  nullBoundaryVerticalDensity : NullFace → Real → Real
  jointVerticalDensity : NullFace → ProgramPT05NullJointEndpoint → Real

/-- Gate 819's vertical sign is negative in horizontal degree three. -/
def programPT05FixedCarrierNullJointLocalDV3
    {NullFace : Type*}
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval) :
    ProgramPT05FixedCarrierNullJointVerticalTransgressionDensity NullFace
      nullFaceInterval where
  nullBoundaryVerticalDensity := fun face parameter ↦
    -density.nullBoundaryDensity face parameter
  jointVerticalDensity := fun face endpoint ↦
    -density.jointDensity face endpoint

/-- Horizontal trace of a contact-degree-one null transgression. -/
def programPT05FixedCarrierNullJointVerticalLocalDH
    {NullFace : Type*}
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierNullJointVerticalTransgressionDensity
      NullFace nullFaceInterval) :
    NullFace → ProgramPT05NullJointEndpoint → Real :=
  density.jointVerticalDensity

/-- Integration of the signed local degree-three vertical source. -/
def programPT05IntegrateFixedCarrierNullVerticalSource
    {NullFace : Type*} [Fintype NullFace]
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierNullJointVerticalTransgressionDensity
      NullFace nullFaceInterval) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 3 1
  | .bulk => 0
  | .nonNullBoundary => 0
  | .nullBoundary =>
      (0, programPT05GeometricNullBoundaryDensityIntegral nullFaceInterval
        density.nullBoundaryVerticalDensity)
  | .joint => 0

/-- The signed local degree-three lift commutes with integration and Gate
819's `dV`. -/
theorem programPT05FixedCarrierNullJointLocalDV3_integration_commutes
    {NullFace : Type*} [Fintype NullFace]
    (nullFaceInterval : NullFace → OrientedNullInterval)
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval) :
    programPT05IntegrateFixedCarrierNullVerticalSource nullFaceInterval
        (programPT05FixedCarrierNullJointLocalDV3 density) =
      programPT05ExactT03RelativeBicomplex.dV 3 0
        (programPT05IntegrateFixedCarrierNullTransgressionSource
          nullFaceInterval density) := by
  funext stratum
  cases stratum <;>
    apply Prod.ext <;>
    norm_num [programPT05IntegrateFixedCarrierNullVerticalSource,
      programPT05FixedCarrierNullJointLocalDV3,
      programPT05IntegrateFixedCarrierNullTransgressionSource,
      programPT05GeometricNullBoundaryDensityIntegral,
      programPT05ExactT03RelativeBicomplex,
      programPT05RelativeVerticalDifferential]

/-- Degree-four local vertical lift of the horizontal joint target, expressed
in Gate 846's fixed-carrier vertical packet and supported only on joints. -/
def programPT05FixedCarrierNullJointTargetLocalDV4
    {NullFace : Type*}
    (period : Real) (hPeriod : period ≠ 0)
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval) :
    ProgramPT05FixedCarrierStratifiedVerticalDensityCochain period hPeriod
      NullFace nullFaceInterval where
  bulkVerticalDensity := 0
  spinCVerticalCoefficient := 0
  llVerticalDensity := 0
  nonNullBoundaryVerticalDensity := 0
  nullBoundaryVerticalDensity := 0
  jointVerticalDensity := programPT05FixedCarrierNullJointLocalDH density

/-- Gate 846's degree-four target lift and the degree-three source lift obey
the mixed sign cancellation at every endpoint, before integration. -/
theorem programPT05FixedCarrierNullJointLocal_mixed_pointwise
    {NullFace : Type*}
    (period : Real) (hPeriod : period ≠ 0)
    {nullFaceInterval : NullFace → OrientedNullInterval}
    (density : ProgramPT05FixedCarrierNullJointTransgressionDensity NullFace
      nullFaceInterval)
    (face : NullFace) (endpoint : ProgramPT05NullJointEndpoint) :
    (programPT05FixedCarrierNullJointTargetLocalDV4 period hPeriod density).jointVerticalDensity
        face endpoint +
        programPT05FixedCarrierNullJointVerticalLocalDH
          (programPT05FixedCarrierNullJointLocalDV3 density) face endpoint =
      0 := by
  simp [programPT05FixedCarrierNullJointTargetLocalDV4,
    programPT05FixedCarrierNullJointLocalDH,
    programPT05FixedCarrierNullJointVerticalLocalDH,
    programPT05FixedCarrierNullJointLocalDV3]

/-- The canonical local horizontal edge and signed local vertical source obey
the full mixed identity after integration. -/
theorem programPT05CanonicalFixedCarrierNullJointLocal_mixed_after_integration
    {NullFace : Type*} [Fintype NullFace]
    (faces : NullFace → FiniteNullFaceActionDatum)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    programPT05ExactT03RelativeBicomplex.dV 4 0
          (programPT05IntegrateFixedCarrierNullJointTarget
            (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
              faces)) +
        programPT05ExactT03RelativeBicomplex.dH 3 1
          (programPT05IntegrateFixedCarrierNullVerticalSource
            (fun face ↦ (faces face).interval)
            (programPT05FixedCarrierNullJointLocalDV3
              (programPT05CanonicalFixedCarrierNullJointTransgressionDensity
                faces))) = 0 := by
  rw [← programPT05CanonicalFixedCarrierNullJointLocalDH_integration_commutes
      faces contracts,
    programPT05FixedCarrierNullJointLocalDV3_integration_commutes]
  exact programPT05ExactT03RelativeBicomplex.mixed_anticommutes 3 0
    (programPT05IntegrateFixedCarrierNullTransgressionSource
      (fun face ↦ (faces face).interval)
      (programPT05CanonicalFixedCarrierNullJointTransgressionDensity faces))

end
end P0EFTJanusProgramPT05FixedCarrierNullJointLocalBicomplex4D
end JanusFormal
