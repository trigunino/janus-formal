import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT04T03FaithfulNullDensityJetProductRule4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05SpinCMatterL1StratifiedVerticalBridge4D

/-!
# T05 faithful-null stratified vertical bridge

Gate 855 supplies the genuine pointwise derivative of every faithful null-face
density, the two endpoint derivatives and their finite integrated sum.  This
module installs precisely those derivatives in the null and joint slots of
Gate 861's enriched stratified vertical carrier.  Projection to Gate 854 is
componentwise exact, and null-plus-joint integration recovers the Frechet
derivative of the faithful mobile geometric total action.

All other vertical slots are zero.  No complete physical vertical
differential, horizontal incidence, or terminal T05 claim is made here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05FaithfulNullStratifiedVerticalBridge4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

open Set MeasureTheory
open scoped BigOperators InnerProductSpace Interval Topology
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteNullFacePhysicalActionRealization4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPT04T03FaithfulNullDensitySecondJetFactorization4D
open P0EFTJanusProgramPT04T03FaithfulNullDominatedIntegralVariation4D
open P0EFTJanusProgramPT04T03FaithfulNullGeometricDominatedJetBridge4D
open P0EFTJanusProgramPT04T03FaithfulNullCompactDominatedContract4D
open P0EFTJanusProgramPT04T03FaithfulNullDensityJetProductRule4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05FixedCarrierStratifiedVerticalDifferential4D
open P0EFTJanusProgramPT05SpinCMatterL1StratifiedVerticalBridge4D

attribute [local instance 10000]
  Real.normedAddCommGroup NormedField.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe uNull

section

variable {NullFace : Type uNull} [Fintype NullFace]

variable (period : Real) (hPeriod : period ≠ 0)

local notation "NullPhysical" => FiniteNullFacePhysicalHilbert NullFace

variable
  (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)

/-- The physical faithful-null part of the local vertical differential.
The face slot contains the Gate-855 factorized density derivative and the
joint slot contains the actual derivatives of both endpoint actions. -/
def programPT05FaithfulNullPhysicalLocalDV
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullPhysical) :
    ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity
      period hPeriod NullFace
        faithful.realization.geometry.interval where
  bulkVerticalDensity := 0
  spinCVerticalDensityL1 := 0
  llVerticalDensity := 0
  nonNullBoundaryVerticalDensity := 0
  nullBoundaryVerticalDensity := fun face parameter ↦
    programPT04T03FaithfulNullFactorizedDensityPhysicalFDerivAt faithful base
      hBase face parameter direction
  jointVerticalDensity := fun face endpoint ↦
    match endpoint with
    | .initial =>
        fderiv Real
          (fun state : NullPhysical ↦
            (faithful.realization.geometry.toFiniteNullFaceActionDatum state
              face).initialJointAction)
          base direction
    | .final =>
        fderiv Real
          (fun state : NullPhysical ↦
            (faithful.realization.geometry.toFiniteNullFaceActionDatum state
              face).finalJointAction)
          base direction

@[simp]
theorem programPT05FaithfulNullPhysicalLocalDV_toGate854_bulk
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullPhysical) :
    (ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity.toGate854 period
      hPeriod
        (programPT05FaithfulNullPhysicalLocalDV period hPeriod faithful base hBase
          direction)).bulkVerticalDensity = 0 := by
  rfl

@[simp]
theorem programPT05FaithfulNullPhysicalLocalDV_toGate854_spinC
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullPhysical) :
    (ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity.toGate854 period
      hPeriod
        (programPT05FaithfulNullPhysicalLocalDV period hPeriod faithful base hBase
          direction)).spinCVerticalCoefficient = 0 := by
  simp [ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity.toGate854,
    programPT05FaithfulNullPhysicalLocalDV]

@[simp]
theorem programPT05FaithfulNullPhysicalLocalDV_toGate854_ll
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullPhysical) :
    (ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity.toGate854 period
      hPeriod
        (programPT05FaithfulNullPhysicalLocalDV period hPeriod faithful base hBase
          direction)).llVerticalDensity = 0 := by
  rfl

@[simp]
theorem programPT05FaithfulNullPhysicalLocalDV_toGate854_nonNull
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullPhysical) :
    (ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity.toGate854 period
      hPeriod
        (programPT05FaithfulNullPhysicalLocalDV period hPeriod faithful base hBase
          direction)).nonNullBoundaryVerticalDensity = 0 := by
  rfl

@[simp]
theorem programPT05FaithfulNullPhysicalLocalDV_toGate854_null
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullPhysical)
    (face : NullFace) (parameter : Real) :
    (ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity.toGate854 period
      hPeriod
        (programPT05FaithfulNullPhysicalLocalDV period hPeriod faithful base hBase
          direction)).nullBoundaryVerticalDensity face parameter =
      programPT04T03FaithfulNullFactorizedDensityPhysicalFDerivAt faithful
        base hBase face parameter direction := by
  rfl

@[simp]
theorem programPT05FaithfulNullPhysicalLocalDV_toGate854_joint_initial
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullPhysical) (face : NullFace) :
    (ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity.toGate854 period
      hPeriod
        (programPT05FaithfulNullPhysicalLocalDV period hPeriod faithful base hBase
          direction)).jointVerticalDensity face .initial =
      fderiv Real
        (fun state : NullPhysical ↦
          (faithful.realization.geometry.toFiniteNullFaceActionDatum state
            face).initialJointAction)
        base direction := by
  rfl

@[simp]
theorem programPT05FaithfulNullPhysicalLocalDV_toGate854_joint_final
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullPhysical) (face : NullFace) :
    (ProgramPT05SpinCMatterL1FixedCarrierVerticalDensity.toGate854 period
      hPeriod
        (programPT05FaithfulNullPhysicalLocalDV period hPeriod faithful base hBase
          direction)).jointVerticalDensity face .final =
      fderiv Real
        (fun state : NullPhysical ↦
          (faithful.realization.geometry.toFiniteNullFaceActionDatum state
            face).finalJointAction)
        base direction := by
  rfl

/-- The Gate-855 factorized derivative is interval-integrable as a
continuous-linear-map-valued function. -/
private theorem faithfulNullFactorizedDensity_intervalIntegrable
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (face : NullFace) :
    IntervalIntegrable
      (fun parameter ↦
        programPT04T03FaithfulNullFactorizedDensityPhysicalFDerivAt faithful
          base hBase face parameter)
      MeasureTheory.volume
      (faithful.realization.geometry.interval face).initialParameter
      (faithful.realization.geometry.interval face).finalParameter := by
  let contract :
      ProgramPT04T03FaithfulNullFaceDominatedFDerivContract faithful face
        base :=
    (programPT04T03FaithfulNullFaceCompactGeometricDominatedFDerivContract
      faithful base hBase face).toDominated
  have hActual :
      IntervalIntegrable
        (programPT04T03FaithfulNullFaceDensityFDeriv faithful face base)
        MeasureTheory.volume
        (faithful.realization.geometry.interval face).initialParameter
        (faithful.realization.geometry.interval face).finalParameter := by
    refine contract.bound_intervalIntegrable.mono_fun'
      contract.density_fderiv_aeStronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae contract.density_fderiv_norm_le] with parameter
        hParameter hBound
    exact hBound hParameter base
      (mem_of_mem_nhds contract.neighborhood_mem_nhds)
  exact hActual.congr fun parameter hParameter ↦
    programPT04T03FaithfulNullFaceDensityFDeriv_eq_factorized faithful base
      hBase face parameter (Set.uIoc_subset_uIcc hParameter)

/-- The integrated null-boundary coordinate is the finite sum of the actual
pointwise faithful face derivatives. -/
theorem programPT05FaithfulNullPhysicalLocalDV_integration_nullBoundary
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullPhysical) :
    (programPT05IntegrateSpinCMatterL1FixedCarrierVerticalDensity period
      hPeriod faithful.realization.geometry.interval
        (programPT05FaithfulNullPhysicalLocalDV period hPeriod faithful base
          hBase direction)
      .nullBoundary).2 =
      ∑ face : NullFace,
        ∫ parameter in
            (faithful.realization.geometry.interval face).initialParameter..
            (faithful.realization.geometry.interval face).finalParameter,
          programPT04T03FaithfulNullFactorizedDensityPhysicalFDerivAt faithful
            base hBase face parameter direction := by
  rfl

/-- The integrated joint coordinate is the finite sum of the actual initial
and final endpoint derivatives. -/
theorem programPT05FaithfulNullPhysicalLocalDV_integration_joint
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullPhysical) :
    (programPT05IntegrateSpinCMatterL1FixedCarrierVerticalDensity period
      hPeriod faithful.realization.geometry.interval
        (programPT05FaithfulNullPhysicalLocalDV period hPeriod faithful base
          hBase direction)
      .joint).2 =
      ∑ face : NullFace,
        (fderiv Real
            (fun state : NullPhysical ↦
              (faithful.realization.geometry.toFiniteNullFaceActionDatum state
                face).initialJointAction)
            base direction +
          fderiv Real
            (fun state : NullPhysical ↦
              (faithful.realization.geometry.toFiniteNullFaceActionDatum state
                face).finalJointAction)
            base direction) := by
  rfl

/-- Null-boundary plus joint integration is exactly the directional Frechet
derivative of the faithful mobile geometric total action. -/
theorem programPT05FaithfulNullPhysicalLocalDV_integration_null_add_joint_eq_fderiv
    (regularity : ProgramPT04T03FaithfulNullMissingScalarC2 faithful)
    (base : NullPhysical)
    (hBase : base ∈ faithful.realization.geometry.domain)
    (direction : NullPhysical) :
    (programPT05IntegrateSpinCMatterL1FixedCarrierVerticalDensity period
        hPeriod faithful.realization.geometry.interval
          (programPT05FaithfulNullPhysicalLocalDV period hPeriod faithful base
            hBase direction)
        .nullBoundary).2 +
      (programPT05IntegrateSpinCMatterL1FixedCarrierVerticalDensity period
        hPeriod faithful.realization.geometry.interval
          (programPT05FaithfulNullPhysicalLocalDV period hPeriod faithful base
            hBase direction)
        .joint).2 =
      fderiv Real
        (finiteNullFaceMobileGeometricTotalAction faithful.realization.geometry)
        base direction := by
  rw [programPT05FaithfulNullPhysicalLocalDV_integration_nullBoundary period
      hPeriod faithful,
    programPT05FaithfulNullPhysicalLocalDV_integration_joint period hPeriod
      faithful,
    programPT04T03FaithfulNullTotalAction_fderiv_eq_factorizedSum faithful
      regularity base hBase]
  rw [sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro face _
  rw [programPT04T03FaithfulNullFactorizedFaceActionDerivative,
    add_apply,
    ContinuousLinearMap.intervalIntegral_apply
      (faithfulNullFactorizedDensity_intervalIntegrable faithful base hBase
        face),
    add_apply]

end

end
end P0EFTJanusProgramPT05FaithfulNullStratifiedVerticalBridge4D
end JanusFormal
