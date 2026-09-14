import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetTotalTangentTransition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityRegularity4D

/-!
# Joint regularity of the physical third-jet vector density

The varying base Jacobian, its inverse, and the physical J3 coordinate
change define a proof-free local representative on the product of one base
chart with the physical J3 fiber.  This gate is local and makes no Piola,
Stokes, or terminal classification claim.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityJointRegularity4D

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
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetCurrentDescent4D
open P0EFTJanusProgramPT06ActualThroatBaseChartJacobianDensityCocycle4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityRegularity4D
open P0EFTJanusProgramPT06BaseDependentPhysicalHorizontalDifferential4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetTotalTangentTransition4D

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

private abbrev PhysicalThirdJet :=
  ActualPhysicalThirdOrderJetProductFiber

private abbrev PhysicalThirdJetCore :=
  actualPhysicalThirdOrderJetProductVectorBundleCore
    period hPeriod .positiveQuarter

/-- The forward base Jacobian as a proof-free function of source coordinates. -/
def programPT06ActualThroatBaseJacobianInCoordinates
    (firstCenter secondCenter : Base period hPeriod) :
    ThroatCoverCoordinates →
      ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates :=
  fderiv Real
    (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)

/-- The inverse base Jacobian, evaluated at the corresponding target
coordinate. -/
def programPT06ActualThroatBaseInverseJacobianInCoordinates
    (firstCenter secondCenter : Base period hPeriod) :
    ThroatCoverCoordinates →
      ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates :=
  fun coordinate ↦
    fderiv Real
      (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
      (throatGaugeBaseChartTransition period hPeriod
        firstCenter secondCenter coordinate)

/-- Absolute determinant of the proof-free forward Jacobian field. -/
def programPT06ActualThroatBaseJacobianDensityInCoordinates
    (firstCenter secondCenter : Base period hPeriod) :
    ThroatCoverCoordinates → Real :=
  fun coordinate ↦
    |LinearMap.det
      (programPT06ActualThroatBaseJacobianInCoordinates period hPeriod
        firstCenter secondCenter coordinate).toLinearMap|

/-- Joint local pullback of a physical J3 vector density. -/
def programPT06ActualPhysicalThirdJetVectorDensityJointPullback
    (firstCenter secondCenter : Base period hPeriod)
    (first second : Chart period hPeriod)
    (current : ProgramPT06ActualPhysicalThirdJetVectorDensity4D) :
    ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
      ThroatCoverCoordinates :=
  fun point ↦
    programPT06ActualThroatBaseJacobianDensityInCoordinates period hPeriod
        firstCenter secondCenter point.1 •
      programPT06ActualThroatBaseInverseJacobianInCoordinates period hPeriod
        firstCenter secondCenter point.1
        (current
          (programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
            period hPeriod firstCenter first second point.1 point.2))

/-- The proof-free pullback agrees pointwise with the Gate-1017 pullback. -/
theorem programPT06ActualPhysicalThirdJetVectorDensityJointPullback_at
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : Chart period hPeriod)
    (current : ProgramPT06ActualPhysicalThirdJetVectorDensity4D)
    (jet : PhysicalThirdJet) :
    programPT06ActualPhysicalThirdJetVectorDensityJointPullback period hPeriod
        firstCenter secondCenter first second current
        (extChartAt throatCoverModelWithCorners firstCenter base, jet) =
      programPT06ActualPhysicalThirdJetVectorDensityPullback period hPeriod
        firstCenter secondCenter base hFirst hSecond first second current jet := by
  unfold programPT06ActualPhysicalThirdJetVectorDensityJointPullback
    programPT06ActualPhysicalThirdJetVectorDensityPullback
    programPT06ActualThroatBaseJacobianDensityInCoordinates
    programPT06ActualThroatBaseJacobianInCoordinates
    programPT06ActualThroatBaseInverseJacobianInCoordinates
  rw [programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart_at
    period hPeriod firstCenter base hFirst first second]
  rw [throatGaugeBaseChartTransition_apply_current period hPeriod
    firstCenter secondCenter base hFirst]
  rw [← throatGaugeBaseChartTransitionJacobianEquivAt_toLinearMap
    period hPeriod firstCenter secondCenter base hFirst hSecond]
  rw [← LinearEquiv.coe_det]
  rfl

private def programPT06ThroatEndomorphismMatrixEntryContinuousLinearMap
    (row column : Fin 3) :
    (ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun operator ↦
        LinearMap.toMatrix programPT06ThroatSpatialBasis
          programPT06ThroatSpatialBasis operator.toLinearMap row column
      map_add' := by
        intro first second
        simp
      map_smul' := by
        intro scalar operator
        simp }

private theorem programPT06ThroatEndomorphismMatrixEntry_contDiff
    (row column : Fin 3) :
    ContDiff Real ∞
      (fun operator : ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates ↦
        LinearMap.toMatrix programPT06ThroatSpatialBasis
          programPT06ThroatSpatialBasis operator.toLinearMap row column) := by
  change ContDiff Real ∞
    (programPT06ThroatEndomorphismMatrixEntryContinuousLinearMap row column)
  exact
    (programPT06ThroatEndomorphismMatrixEntryContinuousLinearMap row column).contDiff

/-- Determinant is smooth on the finite-dimensional throat endomorphism
space. -/
theorem programPT06ThroatEndomorphismDeterminant_contDiff :
    ContDiff Real ∞
      (fun operator : ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates ↦
        LinearMap.det operator.toLinearMap) := by
  rw [show
    (fun operator : ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates ↦
      LinearMap.det operator.toLinearMap) =
      fun operator ↦ Matrix.det
        (LinearMap.toMatrix programPT06ThroatSpatialBasis
          programPT06ThroatSpatialBasis operator.toLinearMap) by
    funext operator
    exact (LinearMap.det_toMatrix programPT06ThroatSpatialBasis
      operator.toLinearMap).symm]
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro permutation _
  apply contDiff_const.mul
  apply contDiff_prod
  intro index _
  exact programPT06ThroatEndomorphismMatrixEntry_contDiff
    (permutation index) index

/-- The absolute Jacobian density is smooth at every valid overlap point. -/
theorem programPT06ActualThroatBaseJacobianDensityInCoordinates_contDiffAt
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    ContDiffAt Real ∞
      (programPT06ActualThroatBaseJacobianDensityInCoordinates period hPeriod
        firstCenter secondCenter)
      (extChartAt throatCoverModelWithCorners firstCenter base) := by
  let coordinate := extChartAt throatCoverModelWithCorners firstCenter base
  have hJacobian : ContDiffAt Real ∞
      (programPT06ActualThroatBaseJacobianInCoordinates period hPeriod
        firstCenter secondCenter) coordinate :=
    throatGaugeBaseChartTransition_fderiv_contDiffAt_infty period hPeriod
      firstCenter secondCenter base hFirst hSecond
  have hDet : ContDiffAt Real ∞
      (fun x ↦ LinearMap.det
        (programPT06ActualThroatBaseJacobianInCoordinates period hPeriod
          firstCenter secondCenter x).toLinearMap) coordinate :=
    programPT06ThroatEndomorphismDeterminant_contDiff.contDiffAt.comp
      coordinate hJacobian
  have hDetNe : LinearMap.det
      (programPT06ActualThroatBaseJacobianInCoordinates period hPeriod
        firstCenter secondCenter coordinate).toLinearMap ≠ 0 := by
    unfold programPT06ActualThroatBaseJacobianInCoordinates
    rw [← throatGaugeBaseChartTransitionJacobianEquivAt_toLinearMap
      period hPeriod firstCenter secondCenter base hFirst hSecond]
    rw [← LinearEquiv.coe_det]
    exact Units.ne_zero _
  exact hDet.abs hDetNe

/-- The proof-free inverse Jacobian field is smooth at every valid overlap
point. -/
theorem programPT06ActualThroatBaseInverseJacobianInCoordinates_contDiffAt
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    ContDiffAt Real ∞
      (programPT06ActualThroatBaseInverseJacobianInCoordinates period hPeriod
        firstCenter secondCenter)
      (extChartAt throatCoverModelWithCorners firstCenter base) := by
  let coordinate := extChartAt throatCoverModelWithCorners firstCenter base
  have hForward : ContDiffAt Real ∞
      (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
      coordinate :=
    throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter base hFirst hSecond
  have hReverseJacobian : ContDiffAt Real ∞
      (fderiv Real
        (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter))
      (throatGaugeBaseChartTransition period hPeriod
        firstCenter secondCenter coordinate) := by
    dsimp only [coordinate]
    rw [throatGaugeBaseChartTransition_apply_current period hPeriod
      firstCenter secondCenter base hFirst]
    exact throatGaugeBaseChartTransition_fderiv_contDiffAt_infty period hPeriod
      secondCenter firstCenter base hSecond hFirst
  exact hReverseJacobian.comp coordinate hForward

/-- Joint smoothness of a transported density follows from smoothness of the
untransported physical J3 density. -/
theorem programPT06ActualPhysicalThirdJetVectorDensityJointPullback_contDiffAt
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second)
    (current : ProgramPT06ActualPhysicalThirdJetVectorDensity4D)
    (hCurrent : ContDiff Real ∞ current)
    (jet : PhysicalThirdJet) :
    ContDiffAt Real ∞
      (programPT06ActualPhysicalThirdJetVectorDensityJointPullback period hPeriod
        firstCenter secondCenter first second current)
      (extChartAt throatCoverModelWithCorners firstCenter base, jet) := by
  let coordinate := extChartAt throatCoverModelWithCorners firstCenter base
  let point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D :=
    (coordinate, jet)
  have hFst : ContDiffAt Real ∞
      (Prod.fst : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
        ThroatCoverCoordinates) point := contDiffAt_fst
  have hSnd : ContDiffAt Real ∞
      (Prod.snd : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
        PhysicalThirdJet) point := contDiffAt_snd
  have hFiberField : ContDiffAt Real ∞
      (programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
        period hPeriod firstCenter first second) coordinate :=
    programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart_contDiffAt
      period hPeriod firstCenter base hFirst first second hBase
  have hFiberOnProduct : ContDiffAt Real ∞
      (fun p : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D ↦
        programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
          period hPeriod firstCenter first second p.1) point :=
    ContDiffAt.fun_comp
      (f := (Prod.fst :
        ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
          ThroatCoverCoordinates))
      (g := programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
        period hPeriod firstCenter first second)
      point hFiberField hFst
  have hFiberEvaluation : ContDiffAt Real ∞
      (fun p : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D ↦
        programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
          period hPeriod firstCenter first second p.1 p.2) point :=
    hFiberOnProduct.clm_apply hSnd
  have hCurrentEvaluation : ContDiffAt Real ∞
      (fun p : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D ↦
        current
          (programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
            period hPeriod firstCenter first second p.1 p.2)) point :=
    ContDiffAt.fun_comp
      (f := fun p : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D ↦
        programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
          period hPeriod firstCenter first second p.1 p.2)
      (g := current) point hCurrent.contDiffAt hFiberEvaluation
  have hInverseField : ContDiffAt Real ∞
      (programPT06ActualThroatBaseInverseJacobianInCoordinates period hPeriod
        firstCenter secondCenter) coordinate :=
    programPT06ActualThroatBaseInverseJacobianInCoordinates_contDiffAt
      period hPeriod firstCenter secondCenter base hFirst hSecond
  have hInverseOnProduct : ContDiffAt Real ∞
      (fun p : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D ↦
        programPT06ActualThroatBaseInverseJacobianInCoordinates period hPeriod
          firstCenter secondCenter p.1) point :=
    ContDiffAt.fun_comp
      (f := (Prod.fst :
        ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
          ThroatCoverCoordinates))
      (g := programPT06ActualThroatBaseInverseJacobianInCoordinates
        period hPeriod firstCenter secondCenter)
      point hInverseField hFst
  have hInverseEvaluation : ContDiffAt Real ∞
      (fun p : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D ↦
        programPT06ActualThroatBaseInverseJacobianInCoordinates period hPeriod
          firstCenter secondCenter p.1
          (current
            (programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
              period hPeriod firstCenter first second p.1 p.2))) point :=
    hInverseOnProduct.clm_apply hCurrentEvaluation
  have hDensity :=
    programPT06ActualThroatBaseJacobianDensityInCoordinates_contDiffAt
      period hPeriod firstCenter secondCenter base hFirst hSecond
  have hDensityOnProduct : ContDiffAt Real ∞
      (fun p : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D ↦
        programPT06ActualThroatBaseJacobianDensityInCoordinates period hPeriod
          firstCenter secondCenter p.1) point :=
    ContDiffAt.fun_comp
      (f := (Prod.fst :
        ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
          ThroatCoverCoordinates))
      (g := programPT06ActualThroatBaseJacobianDensityInCoordinates
        period hPeriod firstCenter secondCenter)
      point hDensity hFst
  exact hDensityOnProduct.smul hInverseEvaluation

/-- The radial density has the required joint local regularity. -/
theorem
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityJointPullback_contDiffAt
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second)
    (jet : PhysicalThirdJet) :
    ContDiffAt Real ∞
      (programPT06ActualPhysicalThirdJetVectorDensityJointPullback period hPeriod
        firstCenter secondCenter first second
        (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
          period hPeriod functional))
      (extChartAt throatCoverModelWithCorners firstCenter base, jet) := by
  apply programPT06ActualPhysicalThirdJetVectorDensityJointPullback_contDiffAt
    period hPeriod firstCenter secondCenter base hFirst hSecond first second
      hBase
  exact
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_contDiff
      period hPeriod functional

/-- At a common base-chart point the joint radial representative is exactly
the Gate-1017 radial chart representative. -/
theorem
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityJointPullback_at
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter base : Base period hPeriod)
    (hReferenceCenter : base ∈
      (extChartAt throatCoverModelWithCorners referenceCenter).source)
    (hChartCenter : base ∈
      (extChartAt throatCoverModelWithCorners chartCenter).source)
    (reference chart : Chart period hPeriod)
    (jet : PhysicalThirdJet) :
    programPT06ActualPhysicalThirdJetVectorDensityJointPullback period hPeriod
        chartCenter referenceCenter chart reference
        (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
          period hPeriod functional)
        (extChartAt throatCoverModelWithCorners chartCenter base, jet) =
      programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityChartRepresentative
        period hPeriod functional referenceCenter chartCenter base
        hReferenceCenter hChartCenter reference chart jet := by
  exact programPT06ActualPhysicalThirdJetVectorDensityJointPullback_at
    period hPeriod chartCenter referenceCenter base hChartCenter
      hReferenceCenter chart reference
      (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional) jet

end

end P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityJointRegularity4D
end JanusFormal
