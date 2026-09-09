import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03FaithfulNullGeometricDominatedJetBridge4D

/-!
# Geometric endpoint jets for the faithful null action

This support gate derives the two endpoint-joint differentiability obligations
of Gate 843.  Coefficientwise `C²` regularity of the screen metric, positivity
of its determinant, and Gate 838's `C²` endpoint-angle fields give genuine
second jets of both joint actions.

Combining these results with Gate 844 turns its geometric dominated contract
directly into Gate 843's complete face-action contract.  Thus the remaining
analytic inputs are measurability and a state-uniform integrable derivative
majorant.  No residual factorization or terminal T04 claim is made.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03FaithfulNullGeometricEndpointJetBridge4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

open Set MeasureTheory
open scoped Interval Topology
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusFiniteNullFacePhysicalActionRealization4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPT04T03FaithfulNullDensitySecondJetFactorization4D
open P0EFTJanusProgramPT04T03FaithfulNullDominatedIntegralVariation4D
open P0EFTJanusProgramPT04T03FaithfulNullGeometricDominatedJetBridge4D

attribute [local instance 10000]
  Real.normedAddCommGroup NormedField.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe uNull

section

variable {NullFace : Type uNull} [Fintype NullFace]

local notation "NullPhysical" => FiniteNullFacePhysicalHilbert NullFace

private theorem endpointScreenMetricCoefficient_contDiffAt_two
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (state : NullPhysical) (hState : state ∈ geometry.domain)
    (face : NullFace) (parameter : Real) (row column : Fin 2) :
    ContDiffAt Real 2
      (fun current : NullPhysical =>
        geometry.screenMetric current face parameter row column)
      state := by
  have hJoint :=
    show ContDiffAt Real 2
        (fun joint : NullPhysical × Real =>
          geometry.screenMetric joint.1 face joint.2 row column)
        (state, parameter) from
      (geometry.screenMetric_contDiffOn_two face row column).contDiffAt
        ((geometry.domain_isOpen.prod isOpen_univ).mem_nhds
          ⟨hState, Set.mem_univ parameter⟩)
  exact hJoint.comp state (contDiffAt_id.prodMk contDiffAt_const)

private theorem endpointScreenMetricDeterminant_contDiffAt_two
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (state : NullPhysical) (hState : state ∈ geometry.domain)
    (face : NullFace) (parameter : Real) :
    ContDiffAt Real 2
      (fun current : NullPhysical =>
        Matrix.det (geometry.screenMetric current face parameter))
      state := by
  have h00 := endpointScreenMetricCoefficient_contDiffAt_two
    (geometry := geometry) (state := state) (hState := hState) (face := face)
    (parameter := parameter) (row := (0 : Fin 2)) (column := (0 : Fin 2))
  have h01 := endpointScreenMetricCoefficient_contDiffAt_two
    (geometry := geometry) (state := state) (hState := hState) (face := face)
    (parameter := parameter) (row := (0 : Fin 2)) (column := (1 : Fin 2))
  have h10 := endpointScreenMetricCoefficient_contDiffAt_two
    (geometry := geometry) (state := state) (hState := hState) (face := face)
    (parameter := parameter) (row := (1 : Fin 2)) (column := (0 : Fin 2))
  have h11 := endpointScreenMetricCoefficient_contDiffAt_two
    (geometry := geometry) (state := state) (hState := hState) (face := face)
    (parameter := parameter) (row := (1 : Fin 2)) (column := (1 : Fin 2))
  simpa only [Matrix.det_fin_two] using (h00.mul h11).sub (h01.mul h10)

private theorem endpointScreenArea_contDiffAt_two
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (state : NullPhysical) (hState : state ∈ geometry.domain)
    (face : NullFace) (parameter : Real) :
    ContDiffAt Real 2
      (fun current : NullPhysical =>
        finiteNullFaceHomogeneousScreenArea
          (geometry.screenMetric current face) parameter)
      state := by
  have hDet := endpointScreenMetricDeterminant_contDiffAt_two
    (geometry := geometry) (state := state) (hState := hState) (face := face)
    (parameter := parameter)
  have hDetNe :
      Matrix.det (geometry.screenMetric state face parameter) ≠ 0 :=
    (geometry.screenMetricDeterminantPositive state face parameter).ne'
  convert (hDet.abs hDetNe).sqrt (abs_ne_zero.mpr hDetNe) using 1 <;>
    norm_num [finiteNullFaceHomogeneousScreenArea]

variable
  (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)

/-- The initial joint action is `C²` at every point of the mobile geometric
domain. -/
theorem programPT04T03FaithfulInitialJointAction_contDiffAt_two
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    ContDiffAt Real 2
      (fun current : NullPhysical =>
        (faithful.realization.geometry.toFiniteNullFaceActionDatum current
          face).initialJointAction)
      state := by
  let geometry := faithful.realization.geometry
  have hArea := endpointScreenArea_contDiffAt_two
    (geometry := geometry) (state := state) (hState := hState) (face := face)
    (parameter := (geometry.interval face).initialParameter)
  have hAngle :=
    (regularity.initialJointAngle_contDiffOn_two face).contDiffAt
      (geometry.domain_isOpen.mem_nhds hState)
  have hCoefficient : ContDiffAt Real 2
      (fun _ : NullPhysical =>
        geometry.einsteinScale face *
          geometry.initialJointOrientationSign face)
      state :=
    contDiffAt_const
  have hJoint := (hCoefficient.mul hArea).mul hAngle
  change ContDiffAt Real 2
    (fun current : NullPhysical =>
      geometry.einsteinScale face *
          geometry.initialJointOrientationSign face *
          finiteNullFaceHomogeneousScreenArea
            (geometry.screenMetric current face)
            (geometry.interval face).initialParameter *
          geometry.initialJointAngle current face)
    state
  exact hJoint

/-- The final joint action has the same geometric `C²` construction. -/
theorem programPT04T03FaithfulFinalJointAction_contDiffAt_two
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    ContDiffAt Real 2
      (fun current : NullPhysical =>
        (faithful.realization.geometry.toFiniteNullFaceActionDatum current
          face).finalJointAction)
      state := by
  let geometry := faithful.realization.geometry
  have hArea := endpointScreenArea_contDiffAt_two
    (geometry := geometry) (state := state) (hState := hState) (face := face)
    (parameter := (geometry.interval face).finalParameter)
  have hAngle :=
    (regularity.finalJointAngle_contDiffOn_two face).contDiffAt
      (geometry.domain_isOpen.mem_nhds hState)
  have hCoefficient : ContDiffAt Real 2
      (fun _ : NullPhysical =>
        geometry.einsteinScale face * geometry.finalJointOrientationSign face)
      state :=
    contDiffAt_const
  have hJoint := (hCoefficient.mul hArea).mul hAngle
  change ContDiffAt Real 2
    (fun current : NullPhysical =>
      geometry.einsteinScale face * geometry.finalJointOrientationSign face *
          finiteNullFaceHomogeneousScreenArea
            (geometry.screenMetric current face)
            (geometry.interval face).finalParameter *
          geometry.finalJointAngle current face)
    state
  exact hJoint

/-- Genuine physical-state second jet of the complete initial joint action. -/
def programPT04T03FaithfulInitialJointActionSecondJetAt
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) : FramedSecondOrderJet NullPhysical Real :=
  chartwiseSecondOrderJetAt
    (fun current : NullPhysical =>
      (faithful.realization.geometry.toFiniteNullFaceActionDatum current
        face).initialJointAction)
    state
    (programPT04T03FaithfulInitialJointAction_contDiffAt_two
      (faithful := faithful) (regularity := regularity) (state := state)
      (hState := hState) (face := face))

/-- Genuine physical-state second jet of the complete final joint action. -/
def programPT04T03FaithfulFinalJointActionSecondJetAt
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) : FramedSecondOrderJet NullPhysical Real :=
  chartwiseSecondOrderJetAt
    (fun current : NullPhysical =>
      (faithful.realization.geometry.toFiniteNullFaceActionDatum current
        face).finalJointAction)
    state
    (programPT04T03FaithfulFinalJointAction_contDiffAt_two
      (faithful := faithful) (regularity := regularity) (state := state)
      (hState := hState) (face := face))

@[simp] theorem programPT04T03FaithfulInitialJointActionSecondJetAt_value
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    (programPT04T03FaithfulInitialJointActionSecondJetAt
      (faithful := faithful) (regularity := regularity) (state := state)
      (hState := hState) (face := face)).value =
      (faithful.realization.geometry.toFiniteNullFaceActionDatum state
        face).initialJointAction :=
  rfl

@[simp] theorem programPT04T03FaithfulFinalJointActionSecondJetAt_value
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    (programPT04T03FaithfulFinalJointActionSecondJetAt
      (faithful := faithful) (regularity := regularity) (state := state)
      (hState := hState) (face := face)).value =
      (faithful.realization.geometry.toFiniteNullFaceActionDatum state
        face).finalJointAction :=
  rfl

@[simp] theorem
    programPT04T03FaithfulInitialJointActionSecondJetAt_firstDerivative
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    (programPT04T03FaithfulInitialJointActionSecondJetAt
      (faithful := faithful) (regularity := regularity) (state := state)
      (hState := hState) (face := face)).firstDerivative =
      fderiv Real
        (fun current : NullPhysical =>
          (faithful.realization.geometry.toFiniteNullFaceActionDatum current
            face).initialJointAction)
        state :=
  rfl

@[simp] theorem
    programPT04T03FaithfulFinalJointActionSecondJetAt_firstDerivative
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    (programPT04T03FaithfulFinalJointActionSecondJetAt
      (faithful := faithful) (regularity := regularity) (state := state)
      (hState := hState) (face := face)).firstDerivative =
      fderiv Real
        (fun current : NullPhysical =>
          (faithful.realization.geometry.toFiniteNullFaceActionDatum current
            face).finalJointAction)
        state :=
  rfl

/-- Gate 843's initial endpoint differentiability field follows from the
geometric endpoint jet. -/
theorem programPT04T03FaithfulInitialJointAction_differentiableAt
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    DifferentiableAt Real
      (fun current : NullPhysical =>
        (faithful.realization.geometry.toFiniteNullFaceActionDatum current
          face).initialJointAction)
      state :=
  (programPT04T03FaithfulInitialJointAction_contDiffAt_two
    (faithful := faithful) (regularity := regularity) (state := state)
    (hState := hState) (face := face)).differentiableAt (by norm_num)

/-- Gate 843's final endpoint differentiability field follows from the same
geometric input. -/
theorem programPT04T03FaithfulFinalJointAction_differentiableAt
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    DifferentiableAt Real
      (fun current : NullPhysical =>
        (faithful.realization.geometry.toFiniteNullFaceActionDatum current
          face).finalJointAction)
      state :=
  (programPT04T03FaithfulFinalJointAction_contDiffAt_two
    (faithful := faithful) (regularity := regularity) (state := state)
    (hState := hState) (face := face)).differentiableAt (by norm_num)

/-- Gate 844's contract now supplies Gate 843's complete face-action contract;
the endpoint fields are theorems rather than additional assumptions. -/
def ProgramPT04T03FaithfulNullFaceGeometricDominatedFDerivContract.toAction
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    {face : NullFace} {base : NullPhysical}
    (contract :
      ProgramPT04T03FaithfulNullFaceGeometricDominatedFDerivContract faithful
        face base) :
    ProgramPT04T03FaithfulNullFaceActionFDerivContract faithful face base := by
  have hBase : base ∈ faithful.realization.geometry.domain :=
    contract.neighborhood_subset_geometryDomain
      (mem_of_mem_nhds contract.neighborhood_mem_nhds)
  exact
    { toProgramPT04T03FaithfulNullFaceDominatedFDerivContract :=
        contract.toDominated
      initialJoint_differentiableAt :=
        programPT04T03FaithfulInitialJointAction_differentiableAt
          (faithful := faithful) (regularity := regularity) (state := base)
          (hState := hBase) (face := face)
      finalJoint_differentiableAt :=
        programPT04T03FaithfulFinalJointAction_differentiableAt
          (faithful := faithful) (regularity := regularity) (state := base)
          (hState := hBase) (face := face) }

end

end
end P0EFTJanusProgramPT04T03FaithfulNullGeometricEndpointJetBridge4D
end JanusFormal
