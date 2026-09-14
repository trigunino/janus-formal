import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D

/-!
# Smoothness of the physical third-jet vector density

The radial Cartan current remains smooth after transport to the actual
eleven-field J3 carrier and after assembly in the throat spatial basis.
Fixed-base chart representatives are smooth functions of the J3 fiber.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityRegularity4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetCurrentDescent4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D
open P0EFTJanusProgramPT06ActualThroatBaseChartJacobianDensityCocycle4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D

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

/-- Every component of the radial current is smooth on the actual physical
J3 carrier. -/
theorem
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetCurrent_component_contDiff
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (direction : Fin 3) :
    ContDiff Real ∞
      (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetCurrent
        period hPeriod functional direction) := by
  unfold programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetCurrent
  exact
    (programPT06T02DegreeFourRadialCartanCurrent_component_contDiff
      period hPeriod functional direction).comp
      programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm.contDiff

/-- The radial current assembled in the throat spatial basis is a smooth
vector-density-valued function of the actual physical J3 fiber. -/
theorem
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_contDiff
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    ContDiff Real ∞
      (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional) := by
  have hComponents : ContDiff Real ∞
      (fun jet : ActualPhysicalThirdOrderJetProductFiber =>
        fun direction : Fin 3 =>
          programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetCurrent
            period hPeriod functional direction jet) := by
    apply contDiff_pi.mpr
    intro direction
    exact
      programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetCurrent_component_contDiff
        period hPeriod functional direction
  unfold
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
    programPT06ActualPhysicalThirdJetCurrentToVectorDensity
  exact
    programPT06ThroatSpatialBasis.equivFun.symm.toContinuousLinearEquiv.contDiff.comp
      hComponents

/-- A fixed-base vector-density pullback preserves smoothness in the J3 fiber. -/
theorem programPT06ActualPhysicalThirdJetVectorDensityPullback_contDiff
    (firstCenter secondCenter : Base period hPeriod)
    (base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : Chart period hPeriod)
    (current : ProgramPT06ActualPhysicalThirdJetVectorDensity4D)
    (hCurrent : ContDiff Real ∞ current) :
    ContDiff Real ∞
      (programPT06ActualPhysicalThirdJetVectorDensityPullback period hPeriod
        firstCenter secondCenter base hFirst hSecond first second current) := by
  unfold programPT06ActualPhysicalThirdJetVectorDensityPullback
  have hFiber : ContDiff Real ∞
      (fun jet : ActualPhysicalThirdOrderJetProductFiber =>
        current ((PhysicalThirdJetCore period hPeriod).coordChange
          first second base jet)) :=
    hCurrent.comp
      ((PhysicalThirdJetCore period hPeriod).coordChange
        first second base).contDiff
  exact
    ((throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
      firstCenter secondCenter base hFirst hSecond).symm.toContinuousLinearEquiv.contDiff.comp
        hFiber).const_smul
      (programPT06ActualThroatBaseChartJacobianDensityAt period hPeriod
        firstCenter secondCenter base hFirst hSecond)

/-- With all chart and base data fixed, the radial chart representative is
smooth in the actual physical J3 fiber. -/
theorem
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityChartRepresentative_contDiff
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter base : Base period hPeriod)
    (hReferenceCenter : base ∈
      (extChartAt throatCoverModelWithCorners referenceCenter).source)
    (hChartCenter : base ∈
      (extChartAt throatCoverModelWithCorners chartCenter).source)
    (reference chart : Chart period hPeriod) :
    ContDiff Real ∞
      (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityChartRepresentative
        period hPeriod functional referenceCenter chartCenter base
        hReferenceCenter hChartCenter reference chart) := by
  apply programPT06ActualPhysicalThirdJetVectorDensityPullback_contDiff
  exact
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_contDiff
      period hPeriod functional

end
end P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityRegularity4D
end JanusFormal
