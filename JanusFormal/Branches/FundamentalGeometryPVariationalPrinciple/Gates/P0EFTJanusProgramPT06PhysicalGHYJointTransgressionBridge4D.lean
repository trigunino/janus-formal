import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06FaithfulPhysicalFaceIncidence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06LocalGHYJointTransgression4D

/-!
# Physical GHY-to-joint transgression bridge

This module records the geometric data needed to apply the local
GHY-to-joint FTOC of Gate 1072 to the actual Candidate-A first-sheet
boundary density.  The collar is incident with the same supplied faithful
null-face realization and the same physical metric used by Gate 1071.

The only global hypothesis is a coarea formula for the measured collar,
stated for every completed boundary scalar field.  The final GHY-to-joint
identity is then derived from that formula and the local primitive.  No
faithful realization or collar datum is asserted to exist.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06PhysicalGHYJointTransgressionBridge4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open scoped Interval
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05HorizontalGeometricIncidenceSupport4D
open P0EFTJanusProgramPT06FaithfulPhysicalFaceIncidence4D
open P0EFTJanusProgramPT06LocalGHYJointTransgression4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance physicalGHYOrientationBoundaryMeasurableSpace :
    MeasurableSpace (OrientationBoundary period hPeriod) :=
  borel _

local instance physicalGHYOrientationBoundaryBorelSpace :
    BorelSpace (OrientationBoundary period hPeriod) where
  measurable_eq := rfl

/-- A measured physical GHY collar whose null corner is the supplied
faithful realization.  `firstSheet_coarea` is a structural disintegration
formula for every boundary scalar field, rather than the desired final
GHY-to-joint equality. -/
structure ProgramPT06PhysicalGHYJointCollarDatum
    (NullFace JointPoint : Type*) [Fintype NullFace]
    [MeasurableSpace JointPoint]
    (plusBase : RegularGeneralLorentzMetric period hPeriod)
    (faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) where
  carrier : ProgramPT06MeasuredJointCarrier JointPoint
  faceIncidence : ∀ face,
    ProgramPT06FaithfulPhysicalFaceIncidenceDatum
      period hPeriod plusBase faithful input face
  screenCoordinate : NullFace → JointPoint →
    FiniteNullFaceScreenCoordinate2
  collarMap : NullFace → JointPoint → Real →
    OrientationBoundary period hPeriod
  collarMap_measurable : ∀ face,
    Measurable (fun pair : JointPoint × Real ↦
      collarMap face pair.1 pair.2)
  interval_order : ∀ face,
    (faithful.realization.geometry.interval face).initialParameter ≤
      (faithful.realization.geometry.interval face).finalParameter
  source_mem_domain : ∀ face point parameter,
    parameter ∈
        uIcc (faithful.realization.geometry.interval face).initialParameter
          (faithful.realization.geometry.interval face).finalParameter →
      (parameter, screenCoordinate face point) ∈
        (faceIncidence face).sourceDomain
  collarMap_eq_boundaryMap : ∀ face point parameter,
    parameter ∈
        uIcc (faithful.realization.geometry.interval face).initialParameter
          (faithful.realization.geometry.interval face).finalParameter →
      collarMap face point parameter =
        (faceIncidence face).boundaryMap
          (parameter, screenCoordinate face point)
  initial_orientation_compatible : ∀ face,
    faithful.realization.geometry.initialJointOrientationSign face = -1
  final_orientation_compatible : ∀ face,
    faithful.realization.geometry.finalJointOrientationSign face = 1
  fiberWeight : NullFace → JointPoint → Real → Real
  firstSheet_coarea :
    ∀ density : CandidateANormalBoundaryScalarField period hPeriod,
      programPT05GeometricGHYDensityIntegral period hPeriod density =
        ∑ face : NullFace,
          ∫ pair : JointPoint × Real,
            fiberWeight face pair.1 pair.2 *
              density (collarMap face pair.1 pair.2)
            ∂(carrier.measure.prod
              (volume.restrict
                (uIoc
                  (faithful.realization.geometry.interval face).initialParameter
                  (faithful.realization.geometry.interval face).finalParameter)))

/-- The faithful physical coordinate of every interior collar point is its
faithful embedding coordinate. -/
theorem programPT06PhysicalGHYJointCollar_coordinate
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input)
    (face : NullFace) (point : JointPoint) (parameter : Real)
    (hParameter : parameter ∈
      uIcc (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) :
    (geometry.faceIncidence face).physicalChart
        (P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D.cutThroatBoundaryToBulk
          period hPeriod (geometry.collarMap face point parameter)) =
      faithful.realization.geometry.embedding input face
        (parameter, geometry.screenCoordinate face point) := by
  rw [geometry.collarMap_eq_boundaryMap face point parameter hParameter]
  exact (geometry.faceIncidence face).face_coordinate _
    (geometry.source_mem_domain face point parameter hParameter)

/-- Parameter selected by one oriented endpoint. -/
def programPT06PhysicalGHYJointEndpointParameter
    {NullFace : Type*} [Fintype NullFace]
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    (face : NullFace) : ProgramPT05NullJointEndpoint → Real
  | .initial =>
      (faithful.realization.geometry.interval face).initialParameter
  | .final =>
      (faithful.realization.geometry.interval face).finalParameter

/-- Both corners of the measured collar are incident with the endpoint of
the same faithful embedding. -/
theorem programPT06PhysicalGHYJointCollar_endpoint_coordinate
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input)
    (face : NullFace) (point : JointPoint)
    (endpoint : ProgramPT05NullJointEndpoint) :
    (geometry.faceIncidence face).physicalChart
        (P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D.cutThroatBoundaryToBulk
          period hPeriod
          (geometry.collarMap face point
            (programPT06PhysicalGHYJointEndpointParameter
              (faithful := faithful) face endpoint))) =
      faithful.realization.geometry.embedding input face
        (programPT06PhysicalGHYJointEndpointParameter
            (faithful := faithful) face endpoint,
          geometry.screenCoordinate face point) := by
  apply programPT06PhysicalGHYJointCollar_coordinate period hPeriod geometry
  cases endpoint with
  | initial =>
      exact left_mem_uIcc
  | final =>
      exact right_mem_uIcc

/-- The local GHY scalar before multiplying by its coarea weight is the
pullback of the actual completed Candidate-A boundary density. -/
def programPT06PhysicalGHYLocalDensity
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input)
    (density : CandidateANormalBoundaryScalarField period hPeriod) :
    NullFace → JointPoint → Real → Real :=
  fun face point parameter ↦
    density (geometry.collarMap face point parameter)

@[simp]
theorem programPT06PhysicalGHYLocalDensity_eq_pullback
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input)
    (density : CandidateANormalBoundaryScalarField period hPeriod)
    (face : NullFace) (point : JointPoint) (parameter : Real) :
    programPT06PhysicalGHYLocalDensity period hPeriod geometry density
        face point parameter =
      density (geometry.collarMap face point parameter) :=
  rfl

/-- For the canonical GHY cochain this pullback is the genuine Candidate-A
GHY integrand evaluated on the measured collar. -/
@[simp]
theorem programPT06PhysicalCanonicalGHYLocalDensity_apply
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input)
    (einsteinScale : Real)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod
      plusBase × Real)
    (face : NullFace) (point : JointPoint) (parameter : Real) :
    programPT06PhysicalGHYLocalDensity period hPeriod geometry
        (programPT05CanonicalGHYLocalDensityCochain period hPeriod
          einsteinScale plusBase current).nonNullBoundaryDensity
        face point parameter =
      candidateANormalBoundaryGHYIntegrandFiberEvaluation period hPeriod
        einsteinScale plusBase current
        (geometry.collarMap face point parameter) :=
  rfl

/-- A local primitive for one actual boundary density.  Analytic hypotheses
are precisely those consumed by Gate 1072. -/
structure ProgramPT06PhysicalGHYJointDensityTransgression
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input)
    (density : CandidateANormalBoundaryScalarField period hPeriod) where
  primitive : NullFace → JointPoint → Real → Real
  primitive_hasDerivAt : ∀ face point parameter,
    HasDerivAt (primitive face point)
      (geometry.fiberWeight face point parameter *
        programPT06PhysicalGHYLocalDensity period hPeriod geometry density
          face point parameter) parameter
  weightedDensity_intervalIntegrable : ∀ face point,
    IntervalIntegrable
      (fun parameter ↦
        geometry.fiberWeight face point parameter *
          programPT06PhysicalGHYLocalDensity period hPeriod geometry density
            face point parameter)
      volume
      (faithful.realization.geometry.interval face).initialParameter
      (faithful.realization.geometry.interval face).finalParameter
  initial_integrable : ∀ face,
    Integrable
      (fun point ↦ primitive face point
        (faithful.realization.geometry.interval face).initialParameter)
      geometry.carrier.measure
  final_integrable : ∀ face,
    Integrable
      (fun point ↦ primitive face point
        (faithful.realization.geometry.interval face).finalParameter)
      geometry.carrier.measure

/-- Forget the physical incidence while retaining exactly Gate 1072's local
transgression data. -/
def ProgramPT06PhysicalGHYJointDensityTransgression.toLocalData
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    {geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input}
    {density : CandidateANormalBoundaryScalarField period hPeriod}
    (data : ProgramPT06PhysicalGHYJointDensityTransgression period hPeriod
      geometry density) :
    ProgramPT06LocalGHYJointTransgressionData NullFace JointPoint where
  carrier := geometry.carrier
  interval := faithful.realization.geometry.interval
  fiberWeight := geometry.fiberWeight
  localGHYDensity :=
    programPT06PhysicalGHYLocalDensity period hPeriod geometry density
  primitive := data.primitive
  primitive_hasDerivAt := data.primitive_hasDerivAt
  weightedDensity_intervalIntegrable :=
    data.weightedDensity_intervalIntegrable

/-- Endpoint trace coefficient produced by the physical local primitive. -/
def programPT06PhysicalGHYJointCoefficient
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    {geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input}
    {density : CandidateANormalBoundaryScalarField period hPeriod}
    (data : ProgramPT06PhysicalGHYJointDensityTransgression period hPeriod
      geometry density) : ProgramPT05JointCoefficient NullFace :=
  programPT06LocalGHYJointCoefficient data.toLocalData

/-- Gate 1072's endpoint signs coincide with the orientation signs stored by
the same faithful null-face geometry. -/
theorem programPT06PhysicalGHYJointEndpointDensity_eq_faithfulOrientation
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    {geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input}
    {density : CandidateANormalBoundaryScalarField period hPeriod}
    (data : ProgramPT06PhysicalGHYJointDensityTransgression period hPeriod
      geometry density)
    (face : NullFace) (endpoint : ProgramPT05NullJointEndpoint)
    (point : JointPoint) :
    programPT06LocalGHYJointEndpointDensity data.toLocalData face endpoint
        point =
      (match endpoint with
        | .initial =>
            faithful.realization.geometry.initialJointOrientationSign face
        | .final =>
            faithful.realization.geometry.finalJointOrientationSign face) *
    data.primitive face point
          (programPT06PhysicalGHYJointEndpointParameter
            (faithful := faithful) face endpoint) := by
  cases endpoint <;>
    simp [programPT06LocalGHYJointEndpointDensity,
      ProgramPT06PhysicalGHYJointDensityTransgression.toLocalData,
      programPT06PhysicalGHYJointEndpointParameter,
      geometry.initial_orientation_compatible,
      geometry.final_orientation_compatible]

/-- Gate 1072 plus the structural coarea formula derive the integrated
physical GHY-to-joint trace for this density. -/
theorem programPT06PhysicalGHYJointCoefficient_integration
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    {geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input}
    {density : CandidateANormalBoundaryScalarField period hPeriod}
    (data : ProgramPT06PhysicalGHYJointDensityTransgression period hPeriod
      geometry density)
    (hProduct : ∀ face, Integrable
      (fun pair : JointPoint × Real ↦
        geometry.fiberWeight face pair.1 pair.2 *
          density (geometry.collarMap face pair.1 pair.2))
      (geometry.carrier.measure.prod
        (volume.restrict
          (uIoc
            (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter)))) :
    programPT05GeometricJointDensityIntegral
        (programPT06PhysicalGHYJointCoefficient period hPeriod data) =
      programPT05GeometricGHYDensityIntegral period hPeriod density := by
  have hLocal :=
    programPT06LocalGHYJointTotalProductIntegral_eq_geometricJoint
      data.toLocalData geometry.interval_order hProduct
      data.initial_integrable data.final_integrable
  change programPT05GeometricJointDensityIntegral
      (programPT06LocalGHYJointCoefficient data.toLocalData) = _
  rw [← hLocal]
  simpa [programPT06LocalGHYJointTotalProductIntegral,
    programPT06LocalGHYJointProductIntegral,
    programPT06LocalGHYWeightedDensity,
    ProgramPT06PhysicalGHYJointDensityTransgression.toLocalData,
    programPT06PhysicalGHYLocalDensity] using
      (geometry.firstSheet_coarea density).symm

/-- A primitive depending linearly on the completed boundary density.  This
extra structure is exactly what promotes the preceding single-density trace
to Gate 854's linear trace operator. -/
structure ProgramPT06PhysicalGHYJointLinearTransgression
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input) where
  primitive : CandidateANormalBoundaryScalarField period hPeriod →ₗ[Real]
    (NullFace → JointPoint → Real → Real)
  primitive_hasDerivAt :
    ∀ density face point parameter,
      HasDerivAt (primitive density face point)
        (geometry.fiberWeight face point parameter *
          programPT06PhysicalGHYLocalDensity period hPeriod geometry density
            face point parameter) parameter
  weightedDensity_intervalIntegrable :
    ∀ density face point,
      IntervalIntegrable
        (fun parameter ↦
          geometry.fiberWeight face point parameter *
            programPT06PhysicalGHYLocalDensity period hPeriod geometry density
              face point parameter)
        volume
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter
  initial_integrable : ∀ density face,
    Integrable
      (fun point ↦ primitive density face point
        (faithful.realization.geometry.interval face).initialParameter)
      geometry.carrier.measure
  final_integrable : ∀ density face,
    Integrable
      (fun point ↦ primitive density face point
        (faithful.realization.geometry.interval face).finalParameter)
      geometry.carrier.measure

/-- Specialize a linear primitive family to one completed boundary density. -/
def ProgramPT06PhysicalGHYJointLinearTransgression.toDensityTransgression
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    {geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input}
    (family : ProgramPT06PhysicalGHYJointLinearTransgression period hPeriod
      geometry)
    (density : CandidateANormalBoundaryScalarField period hPeriod) :
    ProgramPT06PhysicalGHYJointDensityTransgression period hPeriod geometry
      density where
  primitive := family.primitive density
  primitive_hasDerivAt := family.primitive_hasDerivAt density
  weightedDensity_intervalIntegrable :=
    family.weightedDensity_intervalIntegrable density
  initial_integrable := family.initial_integrable density
  final_integrable := family.final_integrable density

/-- The linearly varying endpoint primitive defines Gate 854's actual
reduced trace operator. -/
def ProgramPT06PhysicalGHYJointLinearTransgression.toTraceOperator
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    {geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input}
    (family : ProgramPT06PhysicalGHYJointLinearTransgression period hPeriod
      geometry) :
    ProgramPT05GHYToJointTraceOperator period hPeriod NullFace where
  toLinearMap :=
    { toFun := fun density face endpoint ↦
        match endpoint with
        | .initial =>
            ∫ point,
              -family.primitive density face point
                (faithful.realization.geometry.interval face).initialParameter
              ∂geometry.carrier.measure
        | .final =>
            ∫ point,
              family.primitive density face point
                (faithful.realization.geometry.interval face).finalParameter
              ∂geometry.carrier.measure
      map_add' := by
        intro first second
        funext face endpoint
        cases endpoint with
        | initial =>
            simp only [map_add, Pi.add_apply]
            rw [show
              (fun point ↦
                -(family.primitive first face point
                    (faithful.realization.geometry.interval face).initialParameter +
                  family.primitive second face point
                    (faithful.realization.geometry.interval face).initialParameter)) =
                (fun point ↦
                  -family.primitive first face point
                    (faithful.realization.geometry.interval face).initialParameter +
                  -family.primitive second face point
                    (faithful.realization.geometry.interval face).initialParameter) by
                funext point
                ring]
            exact integral_add
              (family.initial_integrable first face).neg
              (family.initial_integrable second face).neg
        | final =>
            simp only [map_add, Pi.add_apply]
            exact integral_add
              (family.final_integrable first face)
              (family.final_integrable second face)
      map_smul' := by
        intro scalar density
        funext face endpoint
        cases endpoint with
        | initial =>
            simp only [map_smul, Pi.smul_apply, smul_eq_mul]
            rw [show
              (fun point ↦
                -(scalar * family.primitive density face point
                  (faithful.realization.geometry.interval face).initialParameter)) =
                (fun point ↦
                  scalar *
                    (-family.primitive density face point
                      (faithful.realization.geometry.interval face).initialParameter)) by
                funext point
                ring,
              integral_const_mul]
            simp
        | final =>
            simp only [map_smul, Pi.smul_apply, smul_eq_mul]
            rw [integral_const_mul]
            simp }

/-- The trace operator agrees definitionally with the endpoint coefficient
obtained by applying Gate 1072 to each density. -/
theorem programPT06PhysicalGHYJointLinearTrace_apply
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    {geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input}
    (family : ProgramPT06PhysicalGHYJointLinearTransgression period hPeriod
      geometry)
    (density : CandidateANormalBoundaryScalarField period hPeriod) :
    programPT05GHYToJointTracedDensity period hPeriod
        (ProgramPT06PhysicalGHYJointLinearTransgression.toTraceOperator
          period hPeriod family) density =
      programPT06PhysicalGHYJointCoefficient period hPeriod
        (ProgramPT06PhysicalGHYJointLinearTransgression.toDensityTransgression
          period hPeriod family density) := by
  funext face endpoint
  cases endpoint <;> rfl

/-- The physical linear trace commutes with integration for every completed
boundary density whose weighted collar pullback is product-integrable. -/
theorem programPT06PhysicalGHYJointLinearTrace_integration
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    {geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input}
    (family : ProgramPT06PhysicalGHYJointLinearTransgression period hPeriod
      geometry)
    (density : CandidateANormalBoundaryScalarField period hPeriod)
    (hProduct : ∀ face, Integrable
      (fun pair : JointPoint × Real ↦
        geometry.fiberWeight face pair.1 pair.2 *
          density (geometry.collarMap face pair.1 pair.2))
      (geometry.carrier.measure.prod
        (volume.restrict
          (uIoc
            (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter)))) :
    programPT05GeometricJointDensityIntegral
        (programPT05GHYToJointTracedDensity period hPeriod
          (ProgramPT06PhysicalGHYJointLinearTransgression.toTraceOperator
            period hPeriod family) density) =
      programPT05GeometricGHYDensityIntegral period hPeriod density := by
  rw [programPT06PhysicalGHYJointLinearTrace_apply period hPeriod family]
  exact programPT06PhysicalGHYJointCoefficient_integration period hPeriod
    (ProgramPT06PhysicalGHYJointLinearTransgression.toDensityTransgression
      period hPeriod family density) hProduct

/-- For the actual GHY integrand built from `plusBase`, the physical linear
transgression supplies Gate 854's trace support. -/
theorem programPT06PhysicalGHYJointLinearTrace_support
    {NullFace JointPoint : Type*} [Fintype NullFace]
    [MeasurableSpace JointPoint]
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    {geometry : ProgramPT06PhysicalGHYJointCollarDatum period hPeriod
      NullFace JointPoint plusBase faithful input}
    (family : ProgramPT06PhysicalGHYJointLinearTransgression period hPeriod
      geometry)
    (einsteinScale : Real)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod
      plusBase × Real)
    (hProduct : ∀ face, Integrable
      (fun pair : JointPoint × Real ↦
        geometry.fiberWeight face pair.1 pair.2 *
          (programPT05CanonicalGHYLocalDensityCochain period hPeriod
            einsteinScale plusBase current).nonNullBoundaryDensity
            (geometry.collarMap face pair.1 pair.2))
      (geometry.carrier.measure.prod
        (volume.restrict
          (uIoc
            (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter)))) :
    ProgramPT05CanonicalGHYToJointTraceSupport period hPeriod einsteinScale
      plusBase current
        (ProgramPT06PhysicalGHYJointLinearTransgression.toTraceOperator
          period hPeriod family) := by
  constructor
  exact programPT06PhysicalGHYJointLinearTrace_integration period hPeriod
    family
    (programPT05CanonicalGHYLocalDensityCochain period hPeriod
      einsteinScale plusBase current).nonNullBoundaryDensity hProduct

end
end P0EFTJanusProgramPT06PhysicalGHYJointTransgressionBridge4D
end JanusFormal
