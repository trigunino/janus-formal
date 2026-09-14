import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06BaseDependentPhysicalHorizontalDifferential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06FrozenCompatibleFourthJetHorizontalDifferentialNaturality4D

/-!
# Actual physical third-jet total-space tangent transition

The genuine physical J3 bundle core gives a local transition on the product
of throat coordinates and the physical J3 fiber.  Its tangent map contains
both the vertical linear transition and the derivative of that transition in
the base direction.

This is the tangent transition of the local J3 total-space coordinate formula.
It does not yet construct a non-holonomic Cartan prolongation, a holonomic
physical J4 atlas, a Piola identity, an integrated Stokes map, or a terminal
T06 classification.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalThirdJetTotalTangentTransition4D

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
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductFiniteDimensional

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

local instance physicalThirdJetCoreIsContMDiff :
    (PhysicalThirdJetCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ :=
  actualPhysicalThirdOrderJetProductVectorBundleCore_isContMDiff
    period hPeriod .positiveQuarter

/-- Local total-space coordinates for the physical J3 bundle.  Its tangent
space is represented by the same product of normed vector spaces. -/
abbrev ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D :=
  ThroatCoverCoordinates × PhysicalThirdJet

/-- The genuine physical J3 fiber transition, read in one base chart. -/
def programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
    (firstCenter : Base period hPeriod)
    (first second : Chart period hPeriod) :
    ThroatCoverCoordinates → PhysicalThirdJet →L[Real] PhysicalThirdJet :=
  fun coordinate =>
    (PhysicalThirdJetCore period hPeriod).coordChange first second
      ((extChartAt throatCoverModelWithCorners firstCenter).symm coordinate)

/-- At a represented base point, the centered fiber transition is the core
transition at that base point. -/
@[simp]
theorem programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart_at
    (firstCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (first second : Chart period hPeriod) :
    programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
        period hPeriod firstCenter first second
        (extChartAt throatCoverModelWithCorners firstCenter base) =
      (PhysicalThirdJetCore period hPeriod).coordChange first second base := by
  change (PhysicalThirdJetCore period hPeriod).coordChange first second
      ((extChartAt throatCoverModelWithCorners firstCenter).symm
        (extChartAt throatCoverModelWithCorners firstCenter base)) = _
  rw [(extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst]

/-- Smoothness of the centered physical J3 fiber transition follows from the
smooth bundle core and openness of the common trivialization domain. -/
theorem
    programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart_contDiffAt
    (firstCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (first second : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second) :
    ContDiffAt Real ∞
      (programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
        period hPeriod firstCenter first second)
      (extChartAt throatCoverModelWithCorners firstCenter base) := by
  let coordinate :=
    extChartAt throatCoverModelWithCorners firstCenter base
  have hTarget : coordinate ∈
      (extChartAt throatCoverModelWithCorners firstCenter).target :=
    (extChartAt throatCoverModelWithCorners firstCenter).map_source hFirst
  have hInverse :
      ContMDiffAt (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners ∞
        (extChartAt throatCoverModelWithCorners firstCenter).symm coordinate :=
    (contMDiffOn_extChartAt_symm
      (I := throatCoverModelWithCorners) (n := ∞) firstCenter).contMDiffAt
        (extChartAt_target_mem_nhds' hTarget)
  have hTransitionOn :
      ContMDiffOn throatCoverModelWithCorners
        𝓘(Real, PhysicalThirdJet →L[Real] PhysicalThirdJet) ∞
        ((PhysicalThirdJetCore period hPeriod).coordChange first second)
        ((PhysicalThirdJetCore period hPeriod).baseSet first ∩
          (PhysicalThirdJetCore period hPeriod).baseSet second) :=
    (PhysicalThirdJetCore period hPeriod).contMDiffOn_coordChange
      throatCoverModelWithCorners first second
  have hTransition := hTransitionOn.contMDiffAt
    ((((PhysicalThirdJetCore period hPeriod).isOpen_baseSet first).inter
      ((PhysicalThirdJetCore period hPeriod).isOpen_baseSet second)).mem_nhds
        hBase)
  have hComposition := hTransition.comp_of_eq hInverse
    ((extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst)
  change ContDiffAt Real ∞
    (((PhysicalThirdJetCore period hPeriod).coordChange first second) ∘
      (extChartAt throatCoverModelWithCorners firstCenter).symm) coordinate
  exact hComposition.contDiffAt

/-- The local total-space coordinate formula built from the genuine base
change and the varying physical J3 core transition. -/
def programPT06ActualPhysicalThirdJetTotalCoordChange
    (firstCenter secondCenter : Base period hPeriod)
    (first second : Chart period hPeriod) :
    ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
      ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D :=
  fun point =>
    (throatGaugeBaseChartTransition period hPeriod
      firstCenter secondCenter point.1,
    programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
      period hPeriod firstCenter first second point.1 point.2)

/-- This total-space coordinate formula is differentiable at every point of a
simultaneous base-chart and physical J3-core overlap. -/
theorem programPT06ActualPhysicalThirdJetTotalCoordChange_differentiableAt
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
    DifferentiableAt Real
      (programPT06ActualPhysicalThirdJetTotalCoordChange period hPeriod
        firstCenter secondCenter first second)
      (extChartAt throatCoverModelWithCorners firstCenter base, jet) := by
  have hBaseTransition :=
    (throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
      firstCenter secondCenter base hFirst hSecond).differentiableAt
        (by norm_num)
  have hFiberTransition :=
    (programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart_contDiffAt
      period hPeriod firstCenter base hFirst first second hBase).differentiableAt
        (by simp)
  have hFst : DifferentiableAt Real
      (Prod.fst : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
        ThroatCoverCoordinates)
      (extChartAt throatCoverModelWithCorners firstCenter base, jet) :=
    differentiableAt_fst
  have hSnd : DifferentiableAt Real
      (Prod.snd : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
        PhysicalThirdJet)
      (extChartAt throatCoverModelWithCorners firstCenter base, jet) :=
    differentiableAt_snd
  exact
    (hBaseTransition.comp
      (extChartAt throatCoverModelWithCorners firstCenter base, jet)
      hFst).prodMk
      ((hFiberTransition.comp
        (extChartAt throatCoverModelWithCorners firstCenter base, jet)
        hFst).clm_apply hSnd)

/-- Exact tangent transition formula.  Besides the base Jacobian and the
vertical action `C w`, it contains the indispensable base-dependence term
`(dC v) j`. -/
theorem programPT06ActualPhysicalThirdJetTotalCoordChange_fderiv_apply
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second)
    (jet fiberDirection : PhysicalThirdJet)
    (baseDirection : ThroatCoverCoordinates) :
    fderiv Real
        (programPT06ActualPhysicalThirdJetTotalCoordChange period hPeriod
          firstCenter secondCenter first second)
        (extChartAt throatCoverModelWithCorners firstCenter base, jet)
        (baseDirection, fiberDirection) =
      (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
          firstCenter secondCenter base hFirst hSecond baseDirection,
        (PhysicalThirdJetCore period hPeriod).coordChange first second base
            fiberDirection +
          fderiv Real
              (programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
                period hPeriod firstCenter first second)
              (extChartAt throatCoverModelWithCorners firstCenter base)
              baseDirection jet) := by
  rw [← programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart_at
    period hPeriod firstCenter base hFirst first second]
  let coordinate :=
    extChartAt throatCoverModelWithCorners firstCenter base
  let baseTransition :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let fiberTransition :=
    programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
      period hPeriod firstCenter first second
  have hBaseTransition : DifferentiableAt Real baseTransition coordinate :=
    (throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
      firstCenter secondCenter base hFirst hSecond).differentiableAt
        (by norm_num)
  have hFiberTransition : DifferentiableAt Real fiberTransition coordinate :=
    (programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart_contDiffAt
      period hPeriod firstCenter base hFirst first second hBase).differentiableAt
        (by simp)
  have hFst : DifferentiableAt Real
      (Prod.fst : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
        ThroatCoverCoordinates) (coordinate, jet) :=
    differentiableAt_fst
  have hSnd : DifferentiableAt Real
      (Prod.snd : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
        PhysicalThirdJet) (coordinate, jet) :=
    differentiableAt_snd
  have hBaseOnProduct : DifferentiableAt Real
      (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        baseTransition point.1) (coordinate, jet) :=
    DifferentiableAt.fun_comp'
      (coordinate, jet)
      (f := (Prod.fst :
        ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
          ThroatCoverCoordinates))
      (g := baseTransition) hBaseTransition hFst
  have hFiberOnProduct : DifferentiableAt Real
      (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        fiberTransition point.1) (coordinate, jet) :=
    DifferentiableAt.fun_comp'
      (coordinate, jet)
      (f := (Prod.fst :
        ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
          ThroatCoverCoordinates))
      (g := fiberTransition) hFiberTransition hFst
  have hFiberEvaluation : DifferentiableAt Real
      (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        fiberTransition point.1 point.2) (coordinate, jet) :=
    hFiberOnProduct.clm_apply hSnd
  have hBaseFormula :
      fderiv Real
          (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
            baseTransition point.1)
          (coordinate, jet) (baseDirection, fiberDirection) =
        throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
          firstCenter secondCenter base hFirst hSecond baseDirection := by
    have hComposition := fderiv_comp (𝕜 := Real) (x := (coordinate, jet))
      (f := (Prod.fst :
        ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
          ThroatCoverCoordinates))
      (g := baseTransition) hBaseTransition hFst
    have hApplied := congrArg
      (fun derivative :
          ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →L[Real]
            ThroatCoverCoordinates =>
        derivative (baseDirection, fiberDirection)) hComposition
    simpa [Function.comp_def, fderiv_fst, coordinate, baseTransition,
      throatGaugeBaseChartTransitionJacobianEquivAt_apply] using hApplied
  have hFiberBaseFormula :
      fderiv Real
          (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
            fiberTransition point.1)
          (coordinate, jet) (baseDirection, fiberDirection) =
        fderiv Real fiberTransition coordinate baseDirection := by
    have hComposition := fderiv_comp (𝕜 := Real) (x := (coordinate, jet))
      (f := (Prod.fst :
        ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
          ThroatCoverCoordinates))
      (g := fiberTransition) hFiberTransition hFst
    have hApplied := congrArg
      (fun derivative :
          ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →L[Real]
            (PhysicalThirdJet →L[Real] PhysicalThirdJet) =>
        derivative (baseDirection, fiberDirection)) hComposition
    simpa [Function.comp_def, fderiv_fst] using hApplied
  have hFiberFormula :
      fderiv Real
          (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
            fiberTransition point.1 point.2)
          (coordinate, jet) (baseDirection, fiberDirection) =
        fiberTransition coordinate fiberDirection +
          fderiv Real fiberTransition coordinate baseDirection jet := by
    have hProduct := fderiv_clm_apply hFiberOnProduct hSnd
    have hApplied := congrArg
      (fun derivative :
          ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →L[Real]
            PhysicalThirdJet =>
        derivative (baseDirection, fiberDirection)) hProduct
    simp only [add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      fderiv_snd, ContinuousLinearMap.coe_snd'] at hApplied
    rw [hFiberBaseFormula] at hApplied
    exact hApplied
  change fderiv Real
      (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        (baseTransition point.1,
          fiberTransition point.1 point.2))
      (coordinate, jet) (baseDirection, fiberDirection) = _
  have hPair := hBaseOnProduct.fderiv_prodMk hFiberEvaluation
  have hApplied := congrArg
    (fun derivative :
        ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →L[Real]
          ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
      derivative (baseDirection, fiberDirection)) hPair
  simp only [ContinuousLinearMap.prod_apply] at hApplied
  rw [hBaseFormula, hFiberFormula] at hApplied
  simpa [fiberTransition, coordinate] using hApplied

end
end P0EFTJanusProgramPT06ActualPhysicalThirdJetTotalTangentTransition4D
end JanusFormal
