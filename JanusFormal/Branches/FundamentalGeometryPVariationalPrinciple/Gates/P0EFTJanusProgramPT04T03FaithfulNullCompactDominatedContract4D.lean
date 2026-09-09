import Mathlib.Analysis.Normed.Module.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03FaithfulNullGeometricEndpointJetBridge4D

/-!
# Compact dominated contract for the faithful null density

This support gate discharges the two measurability fields and the uniform
majorant field left in Gate 844.  Around every point of the open geometric
domain, a smaller closed ball is compact because the finite null physical
carrier is finite-dimensional.  Joint `C²` regularity of the density makes its
physical derivative continuous on that ball times the compact oriented
parameter interval, hence uniformly bounded there.

The resulting constant bound is interval-integrable.  Together with Gate 848,
this constructs Gate 843's full face-action differentiation contract from the
geometric-domain condition and the existing endpoint scalar `C²` data.  No
residual factorization or terminal T04 statement is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03FaithfulNullCompactDominatedContract4D

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

open Set MeasureTheory
open scoped Interval Topology
open P0EFTJanusFiniteNullFacePhysicalActionRealization4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusProgramPT04T03FaithfulNullDensitySecondJetFactorization4D
open P0EFTJanusProgramPT04T03FaithfulNullDominatedIntegralVariation4D
open P0EFTJanusProgramPT04T03FaithfulNullGeometricDominatedJetBridge4D
open P0EFTJanusProgramPT04T03FaithfulNullGeometricEndpointJetBridge4D

attribute [local instance 10000]
  Real.normedAddCommGroup NormedField.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe uNull

section

variable {NullFace : Type uNull} [Fintype NullFace]

local notation "NullPhysical" => FiniteNullFacePhysicalHilbert NullFace
local notation "JointDomain" => NullPhysical × Real

local instance : ProperSpace NullPhysical :=
  FiniteDimensional.proper_real NullPhysical

variable
  (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)

private theorem faithfulNullFaceDensity_continuousOn_uIcc
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    ContinuousOn
      (programPT04T03FaithfulNullFaceDensityFamily faithful face state)
      (Set.uIcc
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) := by
  intro parameter hParameter
  exact
    ((programPT04T03FaithfulNullFaceDensityJoint_contDiffAt_two faithful state
      hState face parameter hParameter).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt

private theorem faithfulNullFaceDensityFDeriv_continuousOn
    (states : Set NullPhysical)
    (hStates : states ⊆ faithful.realization.geometry.domain)
    (face : NullFace) :
    ContinuousOn
      (fun joint : JointDomain =>
        programPT04T03FaithfulNullFaceDensityFDeriv faithful face joint.1
          joint.2)
      (states ×ˢ
        Set.uIcc
          (faithful.realization.geometry.interval face).initialParameter
          (faithful.realization.geometry.interval face).finalParameter) := by
  let densityJoint : JointDomain → Real := fun joint =>
    programPT04T03FaithfulNullFaceDensityFamily faithful face joint.1 joint.2
  have hJointFDeriv :
      ContinuousOn (fderiv Real densityJoint)
        (states ×ˢ
          Set.uIcc
            (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter) := by
    intro joint hJoint
    simpa only [densityJoint] using
      (programPT04T03FaithfulNullFaceDensityJoint_contDiffAt_two faithful
        joint.1 (hStates hJoint.1) face joint.2 hJoint.2).continuousAt_fderiv
          (by norm_num) |>.continuousWithinAt
  have hRestricted :
      ContinuousOn
        (fun joint : JointDomain =>
          (fderiv Real densityJoint joint).comp
            (ContinuousLinearMap.inl Real NullPhysical Real))
        (states ×ˢ
          Set.uIcc
            (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter) :=
    hJointFDeriv.clm_comp continuousOn_const
  refine hRestricted.congr ?_
  intro joint hJoint
  simpa only [densityJoint,
    programPT04T03FaithfulNullFaceDensityJointSecondJetAt_firstDerivative] using
      (programPT04T03FaithfulNullFaceDensityFDeriv_eq_jointJet_inl faithful
        joint.1 (hStates hJoint.1) face joint.2 hJoint.2)

private theorem faithfulNullFaceDensityFDeriv_continuousOn_uIcc
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    ContinuousOn
      (programPT04T03FaithfulNullFaceDensityFDeriv faithful face state)
      (Set.uIcc
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) := by
  have hJointContinuous :
      ContinuousOn
        (fun joint : JointDomain =>
          programPT04T03FaithfulNullFaceDensityFDeriv faithful face joint.1
            joint.2)
        (faithful.realization.geometry.domain ×ˢ
          Set.uIcc
            (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter) :=
    faithfulNullFaceDensityFDeriv_continuousOn faithful
      faithful.realization.geometry.domain (fun _ h => h) face
  change ContinuousOn
    ((fun joint : JointDomain =>
      programPT04T03FaithfulNullFaceDensityFDeriv faithful face joint.1
        joint.2) ∘ (fun parameter : Real => (state, parameter)))
    (Set.uIcc
      (faithful.realization.geometry.interval face).initialParameter
      (faithful.realization.geometry.interval face).finalParameter)
  intro parameter hParameter
  exact ContinuousWithinAt.comp
    (hJointContinuous (state, parameter) ⟨hState, hParameter⟩)
    ((continuousAt_const.prodMk continuousAt_id).continuousWithinAt)
    (fun _ h => ⟨hState, h⟩)

/-- Every geometric-domain base point has a compact state neighborhood on
which Gate 844's complete dominated-differentiation contract is automatic. -/
def programPT04T03FaithfulNullFaceCompactGeometricDominatedFDerivContract
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    ProgramPT04T03FaithfulNullFaceGeometricDominatedFDerivContract faithful
      face base := by
  let radius : Real := Classical.choose <| Metric.mem_nhds_iff.mp
    (faithful.realization.geometry.domain_isOpen.mem_nhds hBase)
  have hRadiusData :
      0 < radius ∧ Metric.ball base radius ⊆
        faithful.realization.geometry.domain := by
    simpa only [radius] using Classical.choose_spec (Metric.mem_nhds_iff.mp
      (faithful.realization.geometry.domain_isOpen.mem_nhds hBase))
  have hRadius : 0 < radius := hRadiusData.1
  have hBallDomain :
      Metric.ball base radius ⊆ faithful.realization.geometry.domain :=
    hRadiusData.2
  have hHalfRadius : 0 < radius / 2 := half_pos hRadius
  have hNeighborhoodDomain :
      Metric.closedBall base (radius / 2) ⊆
        faithful.realization.geometry.domain :=
    (Metric.closedBall_subset_ball (half_lt_self hRadius)).trans hBallDomain
  have hNeighborhoodNhds :
      Metric.closedBall base (radius / 2) ∈ 𝓝 base :=
    Metric.closedBall_mem_nhds base hHalfRadius
  have hDerivativeContinuous :
      ContinuousOn
        (fun joint : JointDomain =>
          programPT04T03FaithfulNullFaceDensityFDeriv faithful face joint.1
            joint.2)
        (Metric.closedBall base (radius / 2) ×ˢ
          Set.uIcc
            (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter) :=
    faithfulNullFaceDensityFDeriv_continuousOn faithful
      (Metric.closedBall base (radius / 2)) hNeighborhoodDomain face
  have hCompact :
      IsCompact
        (Metric.closedBall base (radius / 2) ×ˢ
          Set.uIcc
            (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter) :=
    (isCompact_closedBall base (radius / 2)).prod isCompact_uIcc
  let hBoundExists :
      ∃ boundConstant : Real,
        ∀ joint ∈
          Metric.closedBall base (radius / 2) ×ˢ
            Set.uIcc
              (faithful.realization.geometry.interval face).initialParameter
              (faithful.realization.geometry.interval face).finalParameter,
          ‖programPT04T03FaithfulNullFaceDensityFDeriv faithful face joint.1
            joint.2‖ ≤ boundConstant :=
    hCompact.exists_bound_of_continuousOn hDerivativeContinuous
  let boundConstant : Real := Classical.choose hBoundExists
  have hBoundConstant :
      ∀ joint ∈
        Metric.closedBall base (radius / 2) ×ˢ
          Set.uIcc
            (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter,
        ‖programPT04T03FaithfulNullFaceDensityFDeriv faithful face joint.1
          joint.2‖ ≤ boundConstant :=
    Classical.choose_spec hBoundExists
  refine
    { neighborhood := Metric.closedBall base (radius / 2)
      neighborhood_mem_nhds := hNeighborhoodNhds
      neighborhood_subset_geometryDomain := hNeighborhoodDomain
      density_eventually_aeStronglyMeasurable := ?_
      density_fderiv_aeStronglyMeasurable := ?_
      bound := fun _ => boundConstant
      density_fderiv_norm_le := ?_
      bound_intervalIntegrable := intervalIntegrable_const }
  · filter_upwards [hNeighborhoodNhds] with state hState
    exact
      ((faithfulNullFaceDensity_continuousOn_uIcc faithful state
        (hNeighborhoodDomain hState) face).mono Set.uIoc_subset_uIcc)
        |>.aestronglyMeasurable measurableSet_uIoc
  · exact
      ((faithfulNullFaceDensityFDeriv_continuousOn_uIcc faithful base hBase
        face).mono Set.uIoc_subset_uIcc)
      |>.aestronglyMeasurable measurableSet_uIoc
  · refine Filter.Eventually.of_forall ?_
    intro parameter hParameter state hState
    exact hBoundConstant (state, parameter)
      ⟨hState, Set.uIoc_subset_uIcc hParameter⟩

/-- With Gate 848's endpoint scalar regularity, the compact geometric
contract supplies Gate 843's complete action differentiation contract. -/
def programPT04T03FaithfulNullFaceActionFDerivContractOfCompactGeometry
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    ProgramPT04T03FaithfulNullFaceActionFDerivContract faithful face base :=
  ProgramPT04T03FaithfulNullFaceGeometricDominatedFDerivContract.toAction
    (faithful := faithful) regularity
    (programPT04T03FaithfulNullFaceCompactGeometricDominatedFDerivContract
      faithful base hBase face)

end

end
end P0EFTJanusProgramPT04T03FaithfulNullCompactDominatedContract4D
end JanusFormal
