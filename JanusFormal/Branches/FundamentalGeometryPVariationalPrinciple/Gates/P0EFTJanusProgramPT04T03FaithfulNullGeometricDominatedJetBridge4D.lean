import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03FaithfulNullDominatedIntegralVariation4D

/-!
# Geometric second-jet input for dominated null-face differentiation

This support gate removes the pointwise differentiability field from Gate 843's
dominated-differentiation contract.  On the mobile geometric domain and on the
oriented parameter interval, positivity of the screen determinant and
nonvanishing of the expansion turn the supplied coefficientwise `C²` data into
a genuine joint second jet of the faithful null density.

The physical-state derivative used by Gate 843 is exactly the first slot of
this joint jet composed with the inclusion `state ↦ (state, parameter)`.
Measurability and a state-uniform integrable majorant remain explicit analytic
hypotheses.  Endpoint-joint differentiability and residual factorization are
not asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03FaithfulNullGeometricDominatedJetBridge4D

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
open P0EFTJanusNullExpansionCountertermVariation
open P0EFTJanusNullExpansionCountertermNonDifferentiable
open P0EFTJanusProgramPT04T03FaithfulNullDominatedIntegralVariation4D

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

private theorem screenMetricCoefficient_contDiffAt_two
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (state : NullPhysical) (hState : state ∈ geometry.domain)
    (face : NullFace) (parameter : Real) (row column : Fin 2) :
    ContDiffAt Real 2
      (fun joint : JointDomain =>
        geometry.screenMetric joint.1 face joint.2 row column)
      (state, parameter) :=
  (geometry.screenMetric_contDiffOn_two face row column).contDiffAt
    ((geometry.domain_isOpen.prod isOpen_univ).mem_nhds
      ⟨hState, Set.mem_univ _⟩)

private theorem screenMetricDeterminant_contDiffAt_two
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (state : NullPhysical) (hState : state ∈ geometry.domain)
    (face : NullFace) (parameter : Real) :
    ContDiffAt Real 2
      (fun joint : JointDomain =>
        Matrix.det (geometry.screenMetric joint.1 face joint.2))
      (state, parameter) := by
  have h00 := screenMetricCoefficient_contDiffAt_two geometry state hState
    face parameter (0 : Fin 2) (0 : Fin 2)
  have h01 := screenMetricCoefficient_contDiffAt_two geometry state hState
    face parameter (0 : Fin 2) (1 : Fin 2)
  have h10 := screenMetricCoefficient_contDiffAt_two geometry state hState
    face parameter (1 : Fin 2) (0 : Fin 2)
  have h11 := screenMetricCoefficient_contDiffAt_two geometry state hState
    face parameter (1 : Fin 2) (1 : Fin 2)
  simpa only [Matrix.det_fin_two] using (h00.mul h11).sub (h01.mul h10)

private theorem screenArea_contDiffAt_two
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (state : NullPhysical) (hState : state ∈ geometry.domain)
    (face : NullFace) (parameter : Real) :
    ContDiffAt Real 2
      (fun joint : JointDomain =>
        finiteNullFaceHomogeneousScreenArea
          (geometry.screenMetric joint.1 face) joint.2)
      (state, parameter) := by
  have hDet := screenMetricDeterminant_contDiffAt_two geometry state hState
    face parameter
  have hDetNe :
      Matrix.det (geometry.screenMetric state face parameter) ≠ 0 :=
    (geometry.screenMetricDeterminantPositive state face parameter).ne'
  convert (hDet.abs hDetNe).sqrt (abs_ne_zero.mpr hDetNe) using 1 <;>
    norm_num [finiteNullFaceHomogeneousScreenArea]

private theorem expansion_contDiffAt_two
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (state : NullPhysical) (hState : state ∈ geometry.domain)
    (face : NullFace) (parameter : Real) :
    ContDiffAt Real 2
      (fun joint : JointDomain =>
        geometry.expansion joint.1 face joint.2)
      (state, parameter) :=
  (geometry.expansion_contDiffOn_two face).contDiffAt
    ((geometry.domain_isOpen.prod isOpen_univ).mem_nhds
      ⟨hState, Set.mem_univ _⟩)

private theorem inaffinity_contDiffAt_two
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (state : NullPhysical) (hState : state ∈ geometry.domain)
    (face : NullFace) (parameter : Real) :
    ContDiffAt Real 2
      (fun joint : JointDomain =>
        geometry.inaffinity joint.1 face joint.2)
      (state, parameter) :=
  (geometry.inaffinity_contDiffOn_two face).contDiffAt
    ((geometry.domain_isOpen.prod isOpen_univ).mem_nhds
      ⟨hState, Set.mem_univ _⟩)

private theorem expansionCounterterm_contDiffAt_two
    (geometry : FiniteNullFaceMobileGeometricDatum NullFace)
    (state : NullPhysical) (hState : state ∈ geometry.domain)
    (face : NullFace) (parameter : Real)
    (hExpansion : geometry.expansion state face parameter ≠ 0) :
    ContDiffAt Real 2
      (fun joint : JointDomain =>
        zeroExtendedExpansionCountertermFactor
          (geometry.renormalizationLengthScale face)
          (geometry.expansion joint.1 face joint.2))
      (state, parameter) := by
  have hTheta := expansion_contDiffAt_two geometry state hState face parameter
  have hAbs := hTheta.abs hExpansion
  have hLength : ContDiffAt Real 2
      (fun _ : JointDomain => geometry.renormalizationLengthScale face)
      (state, parameter) :=
    contDiffAt_const
  have hArgument := hLength.mul hAbs
  have hArgumentNe :
      geometry.renormalizationLengthScale face *
          |geometry.expansion state face parameter| ≠ 0 :=
    mul_ne_zero (geometry.renormalizationLengthScalePositive face).ne'
      (abs_ne_zero.mpr hExpansion)
  have hRaw := hTheta.mul (hArgument.log hArgumentNe)
  simpa only [zeroExtendedExpansionCountertermFactor_eq,
    expansionCountertermFactor] using hRaw

variable
  (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)

/-- The exact faithful density is jointly `C²` in physical state and generator
parameter at every geometric-domain point with nonzero expansion. -/
theorem programPT04T03FaithfulNullFaceDensityJoint_contDiffAt_two
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real)
    (hParameter : parameter ∈
      Set.uIcc
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) :
    ContDiffAt Real 2
      (fun joint : JointDomain =>
        programPT04T03FaithfulNullFaceDensityFamily faithful face joint.1
          joint.2)
      (state, parameter) := by
  let geometry := faithful.realization.geometry
  have hArea := screenArea_contDiffAt_two geometry state hState face parameter
  have hInaffinity := inaffinity_contDiffAt_two geometry state hState face
    parameter
  have hExpansion : geometry.expansion state face parameter ≠ 0 :=
    geometry.expansion_ne_zero_on_domain state hState face parameter hParameter
  have hCounterterm := expansionCounterterm_contDiffAt_two geometry state hState
    face parameter hExpansion
  have hCoefficient : ContDiffAt Real 2
      (fun _ : JointDomain =>
        geometry.einsteinScale face * geometry.faceOrientationSign face)
      (state, parameter) :=
    contDiffAt_const
  have hDensity :=
    ((hCoefficient.mul hArea).mul hInaffinity).add
      ((hCoefficient.mul hArea).mul hCounterterm)
  change ContDiffAt Real 2
    (fun joint : JointDomain =>
      (geometry.einsteinScale face * geometry.faceOrientationSign face) *
            finiteNullFaceHomogeneousScreenArea
              (geometry.screenMetric joint.1 face) joint.2 *
            geometry.inaffinity joint.1 face joint.2 +
        (geometry.einsteinScale face * geometry.faceOrientationSign face) *
            finiteNullFaceHomogeneousScreenArea
              (geometry.screenMetric joint.1 face) joint.2 *
            zeroExtendedExpansionCountertermFactor
              (geometry.renormalizationLengthScale face)
              (geometry.expansion joint.1 face joint.2))
    (state, parameter)
  exact hDensity

/-- Genuine joint second jet of the exact density, derived from the mobile
geometric fields rather than assumed density regularity. -/
def programPT04T03FaithfulNullFaceDensityJointSecondJetAt
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real)
    (hParameter : parameter ∈
      Set.uIcc
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) :
    FramedSecondOrderJet JointDomain Real :=
  chartwiseSecondOrderJetAt
    (fun joint : JointDomain =>
      programPT04T03FaithfulNullFaceDensityFamily faithful face joint.1
        joint.2)
    (state, parameter)
    (programPT04T03FaithfulNullFaceDensityJoint_contDiffAt_two faithful state
      hState face parameter hParameter)

@[simp] theorem programPT04T03FaithfulNullFaceDensityJointSecondJetAt_value
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real)
    (hParameter : parameter ∈
      Set.uIcc
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) :
    (programPT04T03FaithfulNullFaceDensityJointSecondJetAt faithful state hState
      face parameter hParameter).value =
      programPT04T03FaithfulNullFaceDensityFamily faithful face state
        parameter :=
  rfl

@[simp] theorem
    programPT04T03FaithfulNullFaceDensityJointSecondJetAt_firstDerivative
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real)
    (hParameter : parameter ∈
      Set.uIcc
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) :
    (programPT04T03FaithfulNullFaceDensityJointSecondJetAt faithful state hState
      face parameter hParameter).firstDerivative =
      fderiv Real
        (fun joint : JointDomain =>
          programPT04T03FaithfulNullFaceDensityFamily faithful face joint.1
            joint.2)
        (state, parameter) :=
  rfl

/-- Gate 843's physical-state derivative is the horizontal restriction of the
first slot of the genuine joint density jet. -/
theorem programPT04T03FaithfulNullFaceDensityFDeriv_eq_jointJet_inl
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real)
    (hParameter : parameter ∈
      Set.uIcc
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) :
    programPT04T03FaithfulNullFaceDensityFDeriv faithful face state parameter =
      (programPT04T03FaithfulNullFaceDensityJointSecondJetAt faithful state
        hState face parameter hParameter).firstDerivative.comp
          (ContinuousLinearMap.inl Real NullPhysical Real) := by
  unfold programPT04T03FaithfulNullFaceDensityFDeriv
  rw [show
      (fun current : NullPhysical =>
        programPT04T03FaithfulNullFaceDensityFamily faithful face current
          parameter) =
        (fun joint : JointDomain =>
          programPT04T03FaithfulNullFaceDensityFamily faithful face joint.1
            joint.2) ∘ (fun current : NullPhysical => (current, parameter)) by
      rfl]
  rw [fderiv_comp state
    ((programPT04T03FaithfulNullFaceDensityJoint_contDiffAt_two faithful state
      hState face parameter hParameter).differentiableAt (by norm_num))
    (hasFDerivAt_prodMk_left (𝕜 := Real) state parameter).differentiableAt]
  rw [(hasFDerivAt_prodMk_left (𝕜 := Real) state parameter).fderiv]
  rfl

/-- The geometric domain and oriented interval already imply the pointwise
differentiability obligation appearing in Gate 843. -/
theorem programPT04T03FaithfulNullFaceDensity_differentiableAt
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real)
    (hParameter : parameter ∈
      Set.uIcc
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) :
    DifferentiableAt Real
      (fun current : NullPhysical =>
        programPT04T03FaithfulNullFaceDensityFamily faithful face current
          parameter)
      state := by
  exact
    (programPT04T03FaithfulNullFaceDensityJoint_contDiffAt_two faithful state
      hState face parameter hParameter).differentiableAt (by norm_num) |>.comp state
        (hasFDerivAt_prodMk_left (𝕜 := Real) state parameter).differentiableAt

/-- Gate 843's dominated contract with its pointwise differentiability field
replaced by the geometric requirement that the chosen neighborhood stay in the
mobile realization domain. -/
structure ProgramPT04T03FaithfulNullFaceGeometricDominatedFDerivContract
    (face : NullFace) (base : NullPhysical) where
  neighborhood : Set NullPhysical
  neighborhood_mem_nhds : neighborhood ∈ 𝓝 base
  neighborhood_subset_geometryDomain :
    neighborhood ⊆ faithful.realization.geometry.domain
  density_eventually_aeStronglyMeasurable :
    ∀ᶠ state in 𝓝 base,
      AEStronglyMeasurable
        (programPT04T03FaithfulNullFaceDensityFamily faithful face state)
        (MeasureTheory.volume.restrict
          (Ι (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter))
  density_fderiv_aeStronglyMeasurable :
    AEStronglyMeasurable
      (programPT04T03FaithfulNullFaceDensityFDeriv faithful face base)
      (MeasureTheory.volume.restrict
        (Ι (faithful.realization.geometry.interval face).initialParameter
          (faithful.realization.geometry.interval face).finalParameter))
  bound : Real → Real
  density_fderiv_norm_le :
    ∀ᵐ parameter ∂MeasureTheory.volume,
      parameter ∈
          Ι (faithful.realization.geometry.interval face).initialParameter
            (faithful.realization.geometry.interval face).finalParameter →
        ∀ state ∈ neighborhood,
          ‖programPT04T03FaithfulNullFaceDensityFDeriv faithful face state
            parameter‖ ≤ bound parameter
  bound_intervalIntegrable :
    IntervalIntegrable bound MeasureTheory.volume
      (faithful.realization.geometry.interval face).initialParameter
      (faithful.realization.geometry.interval face).finalParameter

/-- Forgetting the geometric proof data produces exactly Gate 843's dominated
contract; its differentiability field is discharged by the joint density jet. -/
def ProgramPT04T03FaithfulNullFaceGeometricDominatedFDerivContract.toDominated
    {face : NullFace} {base : NullPhysical}
    (contract :
      ProgramPT04T03FaithfulNullFaceGeometricDominatedFDerivContract faithful
        face base) :
    ProgramPT04T03FaithfulNullFaceDominatedFDerivContract faithful face base where
  neighborhood := contract.neighborhood
  neighborhood_mem_nhds := contract.neighborhood_mem_nhds
  density_eventually_aeStronglyMeasurable :=
    contract.density_eventually_aeStronglyMeasurable
  density_fderiv_aeStronglyMeasurable :=
    contract.density_fderiv_aeStronglyMeasurable
  bound := contract.bound
  density_fderiv_norm_le := contract.density_fderiv_norm_le
  bound_intervalIntegrable := contract.bound_intervalIntegrable
  density_differentiableAt := by
    intro parameter hParameter state hState
    exact programPT04T03FaithfulNullFaceDensity_differentiableAt faithful state
      (contract.neighborhood_subset_geometryDomain hState) face parameter
      (Set.uIoc_subset_uIcc hParameter)

end

end
end P0EFTJanusProgramPT04T03FaithfulNullGeometricDominatedJetBridge4D
end JanusFormal
