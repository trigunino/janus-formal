import Mathlib.Analysis.Calculus.FDeriv.Mul
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03FaithfulNullCompactDominatedContract4D

/-!
# Product and chain rules for the faithful null-density jets

This support gate factors the genuine joint density derivative into the
screen-area, inaffinity and expansion second jets.  The expansion term uses
the actual derivative of `θ log (ℓ |θ|)` on the nonzero-expansion geometric
domain.  Gate 851 supplies domination, and Gate 843's rule then transports
this pointwise formula under the oriented interval integral.

After the endpoint derivatives are retained explicitly, the finite face sum
pairs with the primal null Riesz residuals carried by Gate 825's zero-jet.
This is a local finite-dimensional factorization only; no metric/GHY residual
identity or terminal T04 statement is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT04T03FaithfulNullDensityJetProductRule4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

open Set MeasureTheory
open scoped BigOperators InnerProductSpace Interval Topology
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteNullFacePhysicalActionRealization4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusNullExpansionCountertermVariation
open P0EFTJanusNullExpansionCountertermNonDifferentiable
open P0EFTJanusProgramPT04T03NullFaceRieszLocalResidual4D
open P0EFTJanusProgramPT04T03NullZeroJetRieszFactorization4D
open P0EFTJanusProgramPT04T03FaithfulNullGeometricSecondJet4D
open P0EFTJanusProgramPT04T03FaithfulNullDensitySecondJetFactorization4D
open P0EFTJanusProgramPT04T03FaithfulNullDominatedIntegralVariation4D
open P0EFTJanusProgramPT04T03FaithfulNullGeometricDominatedJetBridge4D
open P0EFTJanusProgramPT04T03FaithfulNullGeometricEndpointJetBridge4D
open P0EFTJanusProgramPT04T03FaithfulNullCompactDominatedContract4D

attribute [local instance 10000]
  Real.normedAddCommGroup NormedField.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe uNull

section

variable {NullFace : Type uNull} [Fintype NullFace]

local notation "NullPosition" => FiniteNullFacePositionHilbert NullFace
local notation "NullIntrinsic" =>
  FiniteNullFaceIntrinsicMetricHilbert NullFace
local notation "NullPhysical" => FiniteNullFacePhysicalHilbert NullFace
local notation "JointDomain" => NullPhysical × Real

variable
  (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)

local notation "Model" =>
  faithful.toPhysicalActionRealization.toActionModel

/-- Joint screen-area scalar whose determinant is built coefficientwise from
the screen metric. -/
def programPT04T03FaithfulNullScreenAreaFamily
    (face : NullFace) (joint : JointDomain) : Real :=
  finiteNullFaceHomogeneousScreenArea
    (faithful.realization.geometry.screenMetric joint.1 face) joint.2

/-- Joint expansion scalar on the same carrier as Gate 838's expansion jet. -/
def programPT04T03FaithfulNullExpansionFamily
    (face : NullFace) (joint : JointDomain) : Real :=
  faithful.realization.geometry.expansion joint.1 face joint.2

/-- Joint inaffinity scalar on the same carrier as Gate 838's inaffinity jet. -/
def programPT04T03FaithfulNullInaffinityFamily
    (face : NullFace) (joint : JointDomain) : Real :=
  faithful.realization.geometry.inaffinity joint.1 face joint.2

/-- Scalar factor multiplying the screen area in the faithful face density. -/
def programPT04T03FaithfulNullCombinedScalarFamily
    (face : NullFace) (joint : JointDomain) : Real :=
  programPT04T03FaithfulNullInaffinityFamily faithful face joint +
    zeroExtendedExpansionCountertermFactor
      (faithful.realization.geometry.renormalizationLengthScale face)
      (programPT04T03FaithfulNullExpansionFamily faithful face joint)

/-- Algebraically factorized form of the exact faithful face density. -/
def programPT04T03FaithfulNullFactorizedDensityFamily
    (face : NullFace) (joint : JointDomain) : Real :=
  (faithful.realization.geometry.einsteinScale face *
      faithful.realization.geometry.faceOrientationSign face) *
    programPT04T03FaithfulNullScreenAreaFamily faithful face joint *
    programPT04T03FaithfulNullCombinedScalarFamily faithful face joint

private theorem screenMetricCoefficient_contDiffAt_two
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) (row column : Fin 2) :
    ContDiffAt Real 2
      (fun joint : JointDomain =>
        faithful.realization.geometry.screenMetric joint.1 face joint.2 row
          column)
      (state, parameter) :=
  (faithful.realization.geometry.screenMetric_contDiffOn_two face row column)
    |>.contDiffAt
      ((faithful.realization.geometry.domain_isOpen.prod isOpen_univ).mem_nhds
        ⟨hState, Set.mem_univ _⟩)

private theorem screenMetricDeterminant_contDiffAt_two
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    ContDiffAt Real 2
      (fun joint : JointDomain =>
        Matrix.det
          (faithful.realization.geometry.screenMetric joint.1 face joint.2))
      (state, parameter) := by
  have h00 := screenMetricCoefficient_contDiffAt_two faithful state hState face
    parameter (0 : Fin 2) (0 : Fin 2)
  have h01 := screenMetricCoefficient_contDiffAt_two faithful state hState face
    parameter (0 : Fin 2) (1 : Fin 2)
  have h10 := screenMetricCoefficient_contDiffAt_two faithful state hState face
    parameter (1 : Fin 2) (0 : Fin 2)
  have h11 := screenMetricCoefficient_contDiffAt_two faithful state hState face
    parameter (1 : Fin 2) (1 : Fin 2)
  simpa only [Matrix.det_fin_two] using (h00.mul h11).sub (h01.mul h10)

private theorem screenArea_contDiffAt_two
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    ContDiffAt Real 2
      (programPT04T03FaithfulNullScreenAreaFamily faithful face)
      (state, parameter) := by
  have hDet := screenMetricDeterminant_contDiffAt_two faithful state hState face
    parameter
  have hDetNe :
      Matrix.det
          (faithful.realization.geometry.screenMetric state face parameter) ≠
        0 :=
    (faithful.realization.geometry.screenMetricDeterminantPositive state face
      parameter).ne'
  change ContDiffAt Real 2
    (fun joint : JointDomain =>
      Real.sqrt |Matrix.det
        (faithful.realization.geometry.screenMetric joint.1 face joint.2)|)
    (state, parameter)
  exact (hDet.abs hDetNe).sqrt (abs_ne_zero.mpr hDetNe)

private theorem expansion_contDiffAt_two
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    ContDiffAt Real 2
      (programPT04T03FaithfulNullExpansionFamily faithful face)
      (state, parameter) :=
  (faithful.realization.geometry.expansion_contDiffOn_two face).contDiffAt
    ((faithful.realization.geometry.domain_isOpen.prod isOpen_univ).mem_nhds
      ⟨hState, Set.mem_univ _⟩)

private theorem inaffinity_contDiffAt_two
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    ContDiffAt Real 2
      (programPT04T03FaithfulNullInaffinityFamily faithful face)
      (state, parameter) :=
  (faithful.realization.geometry.inaffinity_contDiffOn_two face).contDiffAt
    ((faithful.realization.geometry.domain_isOpen.prod isOpen_univ).mem_nhds
      ⟨hState, Set.mem_univ _⟩)

/-- Genuine joint second jet of the homogeneous screen area. -/
def programPT04T03FaithfulNullScreenAreaSecondJetAt
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    FramedSecondOrderJet JointDomain Real :=
  chartwiseSecondOrderJetAt
    (programPT04T03FaithfulNullScreenAreaFamily faithful face)
    (state, parameter)
    (screenArea_contDiffAt_two faithful state hState face parameter)

/-- Genuine joint second jet of the expansion on Gate 838's carrier. -/
def programPT04T03FaithfulNullExpansionLocalSecondJetAt
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    FramedSecondOrderJet JointDomain Real :=
  chartwiseSecondOrderJetAt
    (programPT04T03FaithfulNullExpansionFamily faithful face)
    (state, parameter)
    (expansion_contDiffAt_two faithful state hState face parameter)

/-- Genuine joint second jet of the inaffinity on Gate 838's carrier. -/
def programPT04T03FaithfulNullInaffinityLocalSecondJetAt
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    FramedSecondOrderJet JointDomain Real :=
  chartwiseSecondOrderJetAt
    (programPT04T03FaithfulNullInaffinityFamily faithful face)
    (state, parameter)
    (inaffinity_contDiffAt_two faithful state hState face parameter)

@[simp] theorem programPT04T03FaithfulNullScreenAreaSecondJetAt_value
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullScreenAreaSecondJetAt faithful state hState face
      parameter).value =
      programPT04T03FaithfulNullScreenAreaFamily faithful face
        (state, parameter) :=
  rfl

@[simp] theorem programPT04T03FaithfulNullExpansionLocalSecondJetAt_value
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullExpansionLocalSecondJetAt faithful state hState
      face parameter).value =
      programPT04T03FaithfulNullExpansionFamily faithful face
        (state, parameter) :=
  rfl

@[simp] theorem programPT04T03FaithfulNullInaffinityLocalSecondJetAt_value
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullInaffinityLocalSecondJetAt faithful state hState
      face parameter).value =
      programPT04T03FaithfulNullInaffinityFamily faithful face
        (state, parameter) :=
  rfl

@[simp] theorem
    programPT04T03FaithfulNullScreenAreaSecondJetAt_firstDerivative
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullScreenAreaSecondJetAt faithful state hState face
      parameter).firstDerivative =
      fderiv Real (programPT04T03FaithfulNullScreenAreaFamily faithful face)
        (state, parameter) :=
  rfl

@[simp] theorem
    programPT04T03FaithfulNullExpansionLocalSecondJetAt_firstDerivative
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullExpansionLocalSecondJetAt faithful state hState
      face parameter).firstDerivative =
      fderiv Real (programPT04T03FaithfulNullExpansionFamily faithful face)
        (state, parameter) :=
  rfl

@[simp] theorem
    programPT04T03FaithfulNullInaffinityLocalSecondJetAt_firstDerivative
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    (programPT04T03FaithfulNullInaffinityLocalSecondJetAt faithful state hState
      face parameter).firstDerivative =
      fderiv Real (programPT04T03FaithfulNullInaffinityFamily faithful face)
        (state, parameter) :=
  rfl

/-- Product/chain-rule candidate written only with values and first slots of
genuine joint second jets. -/
def programPT04T03FaithfulNullFactorizedDensityJointFDerivAt
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) : JointDomain →L[Real] Real :=
  let areaJet :=
    programPT04T03FaithfulNullScreenAreaSecondJetAt faithful state hState face
      parameter
  let expansionJet :=
    programPT04T03FaithfulNullExpansionLocalSecondJetAt faithful state hState
      face parameter
  let inaffinityJet :=
    programPT04T03FaithfulNullInaffinityLocalSecondJetAt faithful state hState
      face parameter
  (faithful.realization.geometry.einsteinScale face *
      faithful.realization.geometry.faceOrientationSign face) •
    (areaJet.value •
        (inaffinityJet.firstDerivative +
          expansionCountertermDerivativeCoefficient
              (faithful.realization.geometry.renormalizationLengthScale face)
              expansionJet.value •
            expansionJet.firstDerivative) +
      (inaffinityJet.value +
          zeroExtendedExpansionCountertermFactor
            (faithful.realization.geometry.renormalizationLengthScale face)
            expansionJet.value) •
        areaJet.firstDerivative)

/-- Horizontal restriction of the factorized joint derivative to physical
state directions. -/
def programPT04T03FaithfulNullFactorizedDensityPhysicalFDerivAt
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) : NullPhysical →L[Real] Real :=
  (programPT04T03FaithfulNullFactorizedDensityJointFDerivAt faithful state
    hState face parameter).comp
      (ContinuousLinearMap.inl Real NullPhysical Real)

private theorem screenAreaSecondJet_hasFDerivAt
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    HasFDerivAt
      (programPT04T03FaithfulNullScreenAreaFamily faithful face)
      (programPT04T03FaithfulNullScreenAreaSecondJetAt faithful state hState
        face parameter).firstDerivative
      (state, parameter) := by
  rw [programPT04T03FaithfulNullScreenAreaSecondJetAt_firstDerivative]
  exact (screenArea_contDiffAt_two faithful state hState face parameter)
    |>.differentiableAt (by norm_num) |>.hasFDerivAt

private theorem expansionSecondJet_hasFDerivAt
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    HasFDerivAt
      (programPT04T03FaithfulNullExpansionFamily faithful face)
      (programPT04T03FaithfulNullExpansionLocalSecondJetAt faithful state
        hState face parameter).firstDerivative
      (state, parameter) := by
  rw [programPT04T03FaithfulNullExpansionLocalSecondJetAt_firstDerivative]
  exact (expansion_contDiffAt_two faithful state hState face parameter)
    |>.differentiableAt (by norm_num) |>.hasFDerivAt

private theorem inaffinitySecondJet_hasFDerivAt
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real) :
    HasFDerivAt
      (programPT04T03FaithfulNullInaffinityFamily faithful face)
      (programPT04T03FaithfulNullInaffinityLocalSecondJetAt faithful state
        hState face parameter).firstDerivative
      (state, parameter) := by
  rw [programPT04T03FaithfulNullInaffinityLocalSecondJetAt_firstDerivative]
  exact (inaffinity_contDiffAt_two faithful state hState face parameter)
    |>.differentiableAt (by norm_num) |>.hasFDerivAt

/-- Exact chain rule for `inaffinity + θ log (ℓ |θ|)` through the expansion
and inaffinity jet first slots. -/
theorem programPT04T03FaithfulNullCombinedScalar_hasFDerivAt
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real)
    (hParameter : parameter ∈
      Set.uIcc
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) :
    HasFDerivAt
      (programPT04T03FaithfulNullCombinedScalarFamily faithful face)
      ((programPT04T03FaithfulNullInaffinityLocalSecondJetAt faithful state
          hState face parameter).firstDerivative +
        expansionCountertermDerivativeCoefficient
            (faithful.realization.geometry.renormalizationLengthScale face)
            (programPT04T03FaithfulNullExpansionLocalSecondJetAt faithful state
              hState face parameter).value •
          (programPT04T03FaithfulNullExpansionLocalSecondJetAt faithful state
            hState face parameter).firstDerivative)
      (state, parameter) := by
  have hExpansionNe :
      programPT04T03FaithfulNullExpansionFamily faithful face
          (state, parameter) ≠ 0 :=
    faithful.realization.geometry.expansion_ne_zero_on_domain state hState face
      parameter hParameter
  have hExpansion := expansionSecondJet_hasFDerivAt faithful state hState face
    parameter
  have hCountertermRaw :=
    (expansionCountertermFactor_hasDerivAt
      (faithful.realization.geometry.renormalizationLengthScale face)
      (programPT04T03FaithfulNullExpansionFamily faithful face
        (state, parameter))
      (faithful.realization.geometry.renormalizationLengthScalePositive face)
      hExpansionNe).comp_hasFDerivAt (state, parameter) hExpansion
  have hInaffinity := inaffinitySecondJet_hasFDerivAt faithful state hState face
    parameter
  change HasFDerivAt
    (fun joint : JointDomain =>
      programPT04T03FaithfulNullInaffinityFamily faithful face joint +
        zeroExtendedExpansionCountertermFactor
          (faithful.realization.geometry.renormalizationLengthScale face)
          (programPT04T03FaithfulNullExpansionFamily faithful face joint))
    _ (state, parameter)
  rw [zeroExtendedExpansionCountertermFactor_eq,
    programPT04T03FaithfulNullExpansionLocalSecondJetAt_value]
  exact hInaffinity.add hCountertermRaw

/-- Product rule for the algebraically factorized faithful density. -/
theorem programPT04T03FaithfulNullFactorizedDensity_hasFDerivAt
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real)
    (hParameter : parameter ∈
      Set.uIcc
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) :
    HasFDerivAt
      (programPT04T03FaithfulNullFactorizedDensityFamily faithful face)
      (programPT04T03FaithfulNullFactorizedDensityJointFDerivAt faithful state
        hState face parameter)
      (state, parameter) := by
  have hArea := screenAreaSecondJet_hasFDerivAt faithful state hState face
    parameter
  have hCombined :=
    programPT04T03FaithfulNullCombinedScalar_hasFDerivAt faithful state hState
      face parameter hParameter
  have hProduct := hArea.mul hCombined
  have hScaled := hProduct.const_mul
    (faithful.realization.geometry.einsteinScale face *
      faithful.realization.geometry.faceOrientationSign face)
  have hFunction :
      programPT04T03FaithfulNullFactorizedDensityFamily faithful face =
        fun joint : JointDomain =>
          (faithful.realization.geometry.einsteinScale face *
              faithful.realization.geometry.faceOrientationSign face) *
            (programPT04T03FaithfulNullScreenAreaFamily faithful face joint *
              programPT04T03FaithfulNullCombinedScalarFamily faithful face
                joint) := by
    funext joint
    simp only [programPT04T03FaithfulNullFactorizedDensityFamily, mul_assoc]
  rw [hFunction]
  dsimp only [programPT04T03FaithfulNullFactorizedDensityJointFDerivAt]
  rw [programPT04T03FaithfulNullScreenAreaSecondJetAt_value,
    programPT04T03FaithfulNullExpansionLocalSecondJetAt_value,
    programPT04T03FaithfulNullInaffinityLocalSecondJetAt_value]
  exact hScaled

/-- The exact density is the area times the combined inaffinity/expansion
factor, with the common gravitational coefficient. -/
theorem programPT04T03FaithfulNullFaceDensityFamily_eq_factorized
    (state : NullPhysical) (face : NullFace) (parameter : Real) :
    programPT04T03FaithfulNullFaceDensityFamily faithful face state parameter =
      programPT04T03FaithfulNullFactorizedDensityFamily faithful face
        (state, parameter) := by
  simp only [programPT04T03FaithfulNullFaceDensityFamily,
    programPT04T03FaithfulNullFactorizedDensityFamily,
    programPT04T03FaithfulNullScreenAreaFamily,
    programPT04T03FaithfulNullCombinedScalarFamily,
    programPT04T03FaithfulNullExpansionFamily,
    programPT04T03FaithfulNullInaffinityFamily, nullFaceDensity,
    inaffinityFaceDensity, expansionCountertermFaceDensity,
    nullFaceCoefficient,
    FiniteNullFaceMobileGeometricDatum.toFiniteNullFaceActionDatum,
    finiteNullFaceHomogeneousScreenArea]
  ring

/-- Gate 844's genuine density-jet derivative is exactly the product/chain
rule expression in the three component second jets. -/
theorem programPT04T03FaithfulNullFaceDensityJointJet_firstDerivative_eq_factorized
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real)
    (hParameter : parameter ∈
      Set.uIcc
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) :
    (programPT04T03FaithfulNullFaceDensityJointSecondJetAt faithful state hState
      face parameter hParameter).firstDerivative =
      programPT04T03FaithfulNullFactorizedDensityJointFDerivAt faithful state
        hState face parameter := by
  rw [programPT04T03FaithfulNullFaceDensityJointSecondJetAt_firstDerivative]
  have hFunction :
      (fun joint : JointDomain =>
        programPT04T03FaithfulNullFaceDensityFamily faithful face joint.1
          joint.2) =
        programPT04T03FaithfulNullFactorizedDensityFamily faithful face := by
    funext joint
    exact programPT04T03FaithfulNullFaceDensityFamily_eq_factorized faithful
      joint.1 face joint.2
  rw [hFunction]
  exact (programPT04T03FaithfulNullFactorizedDensity_hasFDerivAt faithful state
    hState face parameter hParameter).fderiv

/-- The physical pointwise derivative is the horizontal restriction of the
factorized joint jet formula. -/
theorem programPT04T03FaithfulNullFaceDensityFDeriv_eq_factorized
    (state : NullPhysical)
    (hState : state ∈ faithful.realization.geometry.domain)
    (face : NullFace) (parameter : Real)
    (hParameter : parameter ∈
      Set.uIcc
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter) :
    programPT04T03FaithfulNullFaceDensityFDeriv faithful face state parameter =
      programPT04T03FaithfulNullFactorizedDensityPhysicalFDerivAt faithful
        state hState face parameter := by
  rw [programPT04T03FaithfulNullFaceDensityFDeriv_eq_jointJet_inl faithful state
    hState face parameter hParameter]
  rw [programPT04T03FaithfulNullFaceDensityJointJet_firstDerivative_eq_factorized
    faithful state hState face parameter hParameter]
  rfl

/-- Gate 851 supplies the domination needed to place the factorized jet
formula under the oriented face integral. -/
theorem programPT04T03FaithfulIntegratedNullFaceAction_hasFDerivAt_factorized
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    HasFDerivAt
      (fun state : NullPhysical =>
        integratedNullFaceAction
          (faithful.realization.geometry.toFiniteNullFaceActionDatum state face))
      (∫ parameter in
          (faithful.realization.geometry.interval face).initialParameter..
          (faithful.realization.geometry.interval face).finalParameter,
        programPT04T03FaithfulNullFactorizedDensityPhysicalFDerivAt faithful
          base hBase face parameter)
      base := by
  let contract :
      ProgramPT04T03FaithfulNullFaceDominatedFDerivContract faithful face base :=
    (programPT04T03FaithfulNullFaceCompactGeometricDominatedFDerivContract
      faithful base hBase face).toDominated
  have hDatumIntegrability :=
    faithful.realization.intervalIntegrability base hBase face
  have hDensityIntegrable :
      IntervalIntegrable
        (programPT04T03FaithfulNullFaceDensityFamily faithful face base)
        MeasureTheory.volume
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter := by
    change IntervalIntegrable
      (fun parameter =>
        inaffinityFaceDensity
            (faithful.realization.geometry.toFiniteNullFaceActionDatum base face)
            parameter +
          expansionCountertermFaceDensity
            (faithful.realization.geometry.toFiniteNullFaceActionDatum base face)
            parameter)
      MeasureTheory.volume
      (faithful.realization.geometry.interval face).initialParameter
      (faithful.realization.geometry.interval face).finalParameter
    exact hDatumIntegrability.inaffinity.add
      hDatumIntegrability.expansionCounterterm
  have hIntegral :=
    intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := programPT04T03FaithfulNullFaceDensityFamily faithful face)
      (F' := fun state parameter =>
        programPT04T03FaithfulNullFaceDensityFDeriv faithful face state
          parameter)
      (s := contract.neighborhood)
      (x₀ := base)
      (a := (faithful.realization.geometry.interval face).initialParameter)
      (b := (faithful.realization.geometry.interval face).finalParameter)
      (bound := contract.bound)
      (μ := MeasureTheory.volume)
      contract.neighborhood_mem_nhds
      contract.density_eventually_aeStronglyMeasurable
      hDensityIntegrable
      contract.density_fderiv_aeStronglyMeasurable
      contract.density_fderiv_norm_le
      contract.bound_intervalIntegrable
      (Filter.Eventually.of_forall fun parameter hParameter state hState =>
        (contract.density_differentiableAt parameter hParameter state hState)
          |>.hasFDerivAt)
  have hActual :
      HasFDerivAt
        (fun state : NullPhysical =>
          integratedNullFaceAction
            (faithful.realization.geometry.toFiniteNullFaceActionDatum state
              face))
        (∫ parameter in
            (faithful.realization.geometry.interval face).initialParameter..
            (faithful.realization.geometry.interval face).finalParameter,
          programPT04T03FaithfulNullFaceDensityFDeriv faithful face base
            parameter)
        base :=
    hIntegral.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hIntegralEquality :
      (∫ parameter in
          (faithful.realization.geometry.interval face).initialParameter..
          (faithful.realization.geometry.interval face).finalParameter,
        programPT04T03FaithfulNullFaceDensityFDeriv faithful face base
          parameter) =
        ∫ parameter in
          (faithful.realization.geometry.interval face).initialParameter..
          (faithful.realization.geometry.interval face).finalParameter,
        programPT04T03FaithfulNullFactorizedDensityPhysicalFDerivAt faithful
          base hBase face parameter := by
    apply intervalIntegral.integral_congr
    intro parameter hParameter
    exact programPT04T03FaithfulNullFaceDensityFDeriv_eq_factorized faithful
      base hBase face parameter hParameter
  rw [hIntegralEquality] at hActual
  exact hActual

/-- Exact `fderiv` formula under the integral, now expressed by component
second jets. -/
theorem programPT04T03FaithfulIntegratedNullFaceAction_fderiv_eq_factorized
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    fderiv Real
        (fun state : NullPhysical =>
          integratedNullFaceAction
            (faithful.realization.geometry.toFiniteNullFaceActionDatum state
              face))
        base =
      ∫ parameter in
          (faithful.realization.geometry.interval face).initialParameter..
          (faithful.realization.geometry.interval face).finalParameter,
        programPT04T03FaithfulNullFactorizedDensityPhysicalFDerivAt faithful
          base hBase face parameter :=
  (programPT04T03FaithfulIntegratedNullFaceAction_hasFDerivAt_factorized
    faithful base hBase face).fderiv

/-- Complete face derivative: factorized integral plus the two actual endpoint
derivatives. -/
def programPT04T03FaithfulNullFactorizedFaceActionDerivative
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (face : NullFace) : NullPhysical →L[Real] Real :=
  (∫ parameter in
      (faithful.realization.geometry.interval face).initialParameter..
      (faithful.realization.geometry.interval face).finalParameter,
    programPT04T03FaithfulNullFactorizedDensityPhysicalFDerivAt faithful base
      hBase face parameter) +
  (fderiv Real
      (fun state : NullPhysical =>
        (faithful.realization.geometry.toFiniteNullFaceActionDatum state
          face).initialJointAction)
      base +
    fderiv Real
      (fun state : NullPhysical =>
        (faithful.realization.geometry.toFiniteNullFaceActionDatum state
          face).finalJointAction)
      base)

theorem programPT04T03FaithfulNullFaceAction_hasFDerivAt_factorized
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    HasFDerivAt
      (fun state : NullPhysical =>
        finiteNullFaceAction
          (faithful.realization.geometry.toFiniteNullFaceActionDatum state face))
      (programPT04T03FaithfulNullFactorizedFaceActionDerivative faithful base
        hBase face)
      base := by
  have hIntegrated :=
    programPT04T03FaithfulIntegratedNullFaceAction_hasFDerivAt_factorized
      faithful base hBase face
  have hInitial :=
    (programPT04T03FaithfulInitialJointAction_differentiableAt
      (faithful := faithful) (regularity := regularity) (state := base)
      (hState := hBase) (face := face)).hasFDerivAt
  have hFinal :=
    (programPT04T03FaithfulFinalJointAction_differentiableAt
      (faithful := faithful) (regularity := regularity) (state := base)
      (hState := hBase) (face := face)).hasFDerivAt
  have hSum := hIntegrated.add (hInitial.add hFinal)
  exact (hSum.congr_fderiv rfl).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- The complete finite null action differentiates to the sum of the
factorized face derivatives. -/
theorem programPT04T03FaithfulNullTotalAction_fderiv_eq_factorizedSum
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain) :
    fderiv Real
        (finiteNullFaceMobileGeometricTotalAction
          faithful.realization.geometry)
        base =
      ∑ face : NullFace,
        programPT04T03FaithfulNullFactorizedFaceActionDerivative faithful base
          hBase face := by
  apply HasFDerivAt.fderiv
  change HasFDerivAt
    (fun state : NullPhysical =>
      ∑ face : NullFace,
        finiteNullFaceAction
          (faithful.realization.geometry.toFiniteNullFaceActionDatum state face))
    _ base
  exact HasFDerivAt.fun_sum (u := Finset.univ) fun face _ =>
    programPT04T03FaithfulNullFaceAction_hasFDerivAt_factorized faithful
      regularity base hBase face

/-- Gate 825's position component pairs with the factorized local face sum. -/
theorem programPT04T03FaithfulNullPositionRieszZeroJetPairing_eq_factorizedSum
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullPosition) :
    inner Real
        (finiteOrderZeroJetValue4D
          (finiteNullFacePhysicalRieszZeroJet4D Model base)).1 direction =
      (∑ face : NullFace,
        programPT04T03FaithfulNullFactorizedFaceActionDerivative faithful base
          hBase face) (direction, 0) := by
  calc
    inner Real
        (finiteOrderZeroJetValue4D
          (finiteNullFacePhysicalRieszZeroJet4D Model base)).1 direction =
      finiteNullFacePhysicalPositionEuler Model base direction :=
        (finiteEuclideanRieszResidual_pairing
          (finiteNullFacePhysicalPositionEuler Model base) direction).symm
    _ = finiteNullFacePhysicalEuler Model base (direction, 0) := rfl
    _ = (∑ face : NullFace,
          programPT04T03FaithfulNullFactorizedFaceActionDerivative faithful base
            hBase face) (direction, 0) := by
      rw [FiniteNullFaceMobileCanonicalFaithfulActionRealization.euler_eq_fderiv
        faithful base hBase,
        programPT04T03FaithfulNullTotalAction_fderiv_eq_factorizedSum faithful
          regularity base hBase]

/-- Gate 825's intrinsic-screen component has the analogous pairing. -/
theorem programPT04T03FaithfulNullIntrinsicRieszZeroJetPairing_eq_factorizedSum
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullIntrinsic) :
    inner Real
        (finiteOrderZeroJetValue4D
          (finiteNullFacePhysicalRieszZeroJet4D Model base)).2 direction =
      (∑ face : NullFace,
        programPT04T03FaithfulNullFactorizedFaceActionDerivative faithful base
          hBase face) (0, direction) := by
  calc
    inner Real
        (finiteOrderZeroJetValue4D
          (finiteNullFacePhysicalRieszZeroJet4D Model base)).2 direction =
      finiteNullFacePhysicalIntrinsicEuler Model base direction :=
        (finiteEuclideanRieszResidual_pairing
          (finiteNullFacePhysicalIntrinsicEuler Model base) direction).symm
    _ = finiteNullFacePhysicalEuler Model base (0, direction) := rfl
    _ = (∑ face : NullFace,
          programPT04T03FaithfulNullFactorizedFaceActionDerivative faithful base
            hBase face) (0, direction) := by
      rw [FiniteNullFaceMobileCanonicalFaithfulActionRealization.euler_eq_fderiv
        faithful base hBase,
        programPT04T03FaithfulNullTotalAction_fderiv_eq_factorizedSum faithful
          regularity base hBase]

end

end
end P0EFTJanusProgramPT04T03FaithfulNullDensityJetProductRule4D
end JanusFormal
