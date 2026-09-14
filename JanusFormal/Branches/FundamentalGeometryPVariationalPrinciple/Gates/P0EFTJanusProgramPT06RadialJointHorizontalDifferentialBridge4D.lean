import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetJointHorizontalDifferential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityJointRegularity4D

/-!
# Radial joint horizontal-differential bridge

The proof-free radial joint pullback is read on formal physical J3 through the
exact continuous linear bridge.  Gate 1025 then supplies the joint smoothness
required by Gate 1024, so the joint Cartan differential agrees with the
base-dependent chartwise differential without an additional regularity
hypothesis.  This statement is local; it asserts no Piola, Stokes, or terminal
claim.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06RadialJointHorizontalDifferentialBridge4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityHorizontalDifferential4D
open P0EFTJanusProgramPT06BaseDependentPhysicalHorizontalDifferential4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanFrameTransport4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetTotalTangentTransition4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetJointHorizontalDifferential4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityJointRegularity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Base :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (Base period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (Base period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev Chart :=
  ActualPhysicalThirdOrderJetProductBundleIndex period hPeriod

private abbrev PhysicalThirdJetCore :=
  actualPhysicalThirdOrderJetProductVectorBundleCore
    period hPeriod .positiveQuarter

/-- The proof-free radial joint pullback, expressed as a base-dependent
formal-physical-J3 vector density. -/
def programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter : Base period hPeriod)
    (reference chart : Chart period hPeriod) :
    ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D :=
  fun coordinate formalJet ↦
    programPT06ActualPhysicalThirdJetVectorDensityJointPullback period hPeriod
      chartCenter referenceCenter chart reference
      (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional)
      (coordinate,
        programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv
          formalJet)

/-- Reading a component through Gate 1024 cancels the formal/physical J3
bridge and gives exactly that component of the Gate-1025 joint pullback. -/
theorem programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity_component
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter : Base period hPeriod)
    (reference chart : Chart period hPeriod)
    (direction : Fin 3)
    (point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D) :
    programPT06ActualPhysicalThirdJetJointComponent
        (programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity
          period hPeriod functional referenceCenter chartCenter reference chart)
        direction point =
      programPT06ThroatSpatialBasis.equivFun
        (programPT06ActualPhysicalThirdJetVectorDensityJointPullback
          period hPeriod chartCenter referenceCenter chart reference
          (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
            period hPeriod functional) point)
        direction := by
  simp [programPT06ActualPhysicalThirdJetJointComponent,
    programPT06BaseDependentPhysicalVectorDensityComponent,
    programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity,
    programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv]

/-- Gate 1025 discharges the joint differentiability required for every
radial component. -/
theorem
    programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity_component_differentiableAt
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter base : Base period hPeriod)
    (hReferenceCenter : base ∈
      (extChartAt throatCoverModelWithCorners referenceCenter).source)
    (hChartCenter : base ∈
      (extChartAt throatCoverModelWithCorners chartCenter).source)
    (reference chart : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet chart ∩
        (PhysicalThirdJetCore period hPeriod).baseSet reference)
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D)
    (direction : Fin 3) :
    DifferentiableAt Real
      (programPT06ActualPhysicalThirdJetJointComponent
        (programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity
          period hPeriod functional referenceCenter chartCenter reference chart)
        direction)
      (extChartAt throatCoverModelWithCorners chartCenter base,
        programPT06ActualPhysicalFormalFourthJetBaseThirdJet jet) := by
  rw [show
    programPT06ActualPhysicalThirdJetJointComponent
        (programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity
          period hPeriod functional referenceCenter chartCenter reference chart)
        direction =
      fun point ↦ programPT06ThroatSpatialBasis.equivFun
        (programPT06ActualPhysicalThirdJetVectorDensityJointPullback
          period hPeriod chartCenter referenceCenter chart reference
          (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
            period hPeriod functional) point)
        direction by
      funext point
      exact
        programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity_component
          period hPeriod functional referenceCenter chartCenter reference chart
          direction point]
  have hJoint :=
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityJointPullback_contDiffAt
      period hPeriod functional chartCenter referenceCenter base
      hChartCenter hReferenceCenter chart reference hBase
      (programPT06ActualPhysicalFormalFourthJetBaseThirdJet jet)
  have hComponent : ContDiff Real ∞
      (fun value : ThroatCoverCoordinates ↦
        programPT06ThroatSpatialBasis.equivFun value direction) :=
    (contDiff_apply Real Real direction).comp
      programPT06ThroatSpatialBasis.equivFun.toContinuousLinearEquiv.contDiff
  simpa only [Function.comp_def] using
    (hComponent.contDiffAt.comp _ hJoint).differentiableAt (by simp)

/-- On the formal-J4 Cartan state, the radial joint differential is exactly
Gate 1020 applied to the transported base-dependent density. -/
theorem
    programPT06T02DegreeFourRadialCartanJointHorizontalDifferential_eq_baseDependent
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter base : Base period hPeriod)
    (hReferenceCenter : base ∈
      (extChartAt throatCoverModelWithCorners referenceCenter).source)
    (hChartCenter : base ∈
      (extChartAt throatCoverModelWithCorners chartCenter).source)
    (reference chart : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet chart ∩
        (PhysicalThirdJetCore period hPeriod).baseSet reference)
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D) :
    programPT06ActualPhysicalThirdJetJointHorizontalDifferential
        (programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity
          period hPeriod functional referenceCenter chartCenter reference chart)
        (extChartAt throatCoverModelWithCorners chartCenter base)
        (programPT06ActualPhysicalFormalFourthJetBaseThirdJet jet)
        (programPT06ActualPhysicalFormalFourthJetCartanFrame jet) =
      programPT06BaseDependentPhysicalHorizontalDifferential
        (programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity
          period hPeriod functional referenceCenter chartCenter reference chart)
        (extChartAt throatCoverModelWithCorners chartCenter base) jet := by
  apply
    programPT06ActualPhysicalThirdJetJointHorizontalDifferential_formalFourthJet
  intro direction
  exact
    programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity_component_differentiableAt
      period hPeriod functional referenceCenter chartCenter base
      hReferenceCenter hChartCenter reference chart hBase jet direction

/-- At the represented base point, the formal density value is the Gate-1017
radial chart representative evaluated on the corresponding physical J3 jet. -/
theorem programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity_at
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter base : Base period hPeriod)
    (hReferenceCenter : base ∈
      (extChartAt throatCoverModelWithCorners referenceCenter).source)
    (hChartCenter : base ∈
      (extChartAt throatCoverModelWithCorners chartCenter).source)
    (reference chart : Chart period hPeriod)
    (formalJet : ProgramPT06ActualPhysicalFormalThirdJet4D) :
    programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity
        period hPeriod functional referenceCenter chartCenter reference chart
        (extChartAt throatCoverModelWithCorners chartCenter base) formalJet =
      programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityChartRepresentative
        period hPeriod functional referenceCenter chartCenter base
        hReferenceCenter hChartCenter reference chart
        (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv
          formalJet) := by
  exact
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityJointPullback_at
      period hPeriod functional referenceCenter chartCenter base
      hReferenceCenter hChartCenter reference chart
      (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv
        formalJet)

end

end P0EFTJanusProgramPT06RadialJointHorizontalDifferentialBridge4D
end JanusFormal
