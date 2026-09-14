import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalFramedThirdJetTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates4D

/-!
# Pointwise descent of the actual physical third-jet current

The radial current is transferred to the eleven-component physical third-jet
carrier and transported by the genuine physical bundle coordinate changes.
The result is only a pointwise chart law in the fixed spatial basis; no
vector-density covariance or Stokes statement is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalThirdJetCurrentDescent4D

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
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanClassification4D
open P0EFTJanusProgramPT06ActualPhysicalFramedThirdJetTransport4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D

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

/-- Horizontal-current components on the actual eleven-field J3 carrier. -/
abbrev ProgramPT06ActualPhysicalThirdJetCurrent4D :=
  Fin 3 → ActualPhysicalThirdOrderJetProductFiber → Real

/-- Contravariant pullback of a current by an actual physical J3 coordinate
change. -/
def programPT06ActualPhysicalThirdJetCurrentPullback
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (current : ProgramPT06ActualPhysicalThirdJetCurrent4D) :
    ProgramPT06ActualPhysicalThirdJetCurrent4D :=
  fun direction jet ↦ current direction
    ((PhysicalThirdJetCore period hPeriod).coordChange
      first second base jet)

/-- An identity chart change acts trivially on physical J3 currents. -/
@[simp]
theorem programPT06ActualPhysicalThirdJetCurrentPullback_self
    (chart : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈ (PhysicalThirdJetCore period hPeriod).baseSet chart)
    (current : ProgramPT06ActualPhysicalThirdJetCurrent4D) :
    programPT06ActualPhysicalThirdJetCurrentPullback
        period hPeriod chart chart base current = current := by
  funext direction jet
  unfold programPT06ActualPhysicalThirdJetCurrentPullback
  rw [(PhysicalThirdJetCore period hPeriod).coordChange_self
    chart base hBase jet]

/-- Pullback of physical J3 currents respects composition on triple
overlaps. -/
theorem programPT06ActualPhysicalThirdJetCurrentPullback_comp
    (first second third : Chart period hPeriod)
    (base : Base period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second ∩
        (PhysicalThirdJetCore period hPeriod).baseSet third)
    (current : ProgramPT06ActualPhysicalThirdJetCurrent4D) :
    programPT06ActualPhysicalThirdJetCurrentPullback
        period hPeriod first second base
        (programPT06ActualPhysicalThirdJetCurrentPullback
          period hPeriod second third base current) =
      programPT06ActualPhysicalThirdJetCurrentPullback
        period hPeriod first third base current := by
  funext direction jet
  exact congrArg (current direction)
    ((PhysicalThirdJetCore period hPeriod).coordChange_comp
      first second third base hBase jet)

/-! ## Radial current in the actual J3 carrier -/

/-- Gate925's radial current transferred through the exact eleven-field J3
carrier bridge. -/
def programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetCurrent
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    ProgramPT06ActualPhysicalThirdJetCurrent4D :=
  fun direction jet ↦
    programPT06T02DegreeFourRadialCartanCurrent
      period hPeriod functional direction
      (programPT06ActualPhysicalValueProductThirdJetLinearEquiv.symm jet)

/-- Representative obtained by transporting the radial current from a
reference physical J3 chart. -/
def programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetChartRepresentative
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (reference chart : Chart period hPeriod) (base : Base period hPeriod) :
    ProgramPT06ActualPhysicalThirdJetCurrent4D :=
  programPT06ActualPhysicalThirdJetCurrentPullback period hPeriod
    chart reference base
    (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetCurrent
      period hPeriod functional)

/-- The actual physical radial-current representatives obey the J3 chart
change law on a triple overlap. -/
theorem
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJet_chartChange
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (reference first second : Chart period hPeriod)
    (base : Base period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second ∩
        (PhysicalThirdJetCore period hPeriod).baseSet reference)
    (direction : Fin 3) (jet : ActualPhysicalThirdOrderJetProductFiber) :
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetChartRepresentative
        period hPeriod functional reference second base direction
        ((PhysicalThirdJetCore period hPeriod).coordChange
          first second base jet) =
      programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetChartRepresentative
        period hPeriod functional reference first base direction jet := by
  unfold
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetChartRepresentative
    programPT06ActualPhysicalThirdJetCurrentPullback
  exact congrArg
    ((programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetCurrent
      period hPeriod functional) direction)
    ((PhysicalThirdJetCore period hPeriod).coordChange_comp
      first second reference base hBase jet)

/-! ## Evaluation on the physical J3 section -/

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-- The assembled physical local extractors themselves obey the product-core
coordinate change. -/
theorem globalCandidateAActualPhysicalThirdOrderJetExtractor_coordChange
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second) :
    (PhysicalThirdJetCore period hPeriod).coordChange first second base
        ((globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
          period hPeriod data).extractor first base) =
      (globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
        period hPeriod data).extractor second base := by
  let coordinates :=
    globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
      period hPeriod data
  have hComp :=
    (PhysicalThirdJetCore period hPeriod).coordChange_comp
      ((PhysicalThirdJetCore period hPeriod).indexAt base) first second base
      ⟨⟨(PhysicalThirdJetCore period hPeriod).mem_baseSet_at base,
          hBase.1⟩, hBase.2⟩
      (coordinates.value base)
  rw [coordinates.coordinate_eq first base hBase.1,
    coordinates.coordinate_eq second base hBase.2] at hComp
  exact hComp

/-- Evaluation of one radial-current representative on the actual physical
J3 local extractor. -/
def globalCandidateAActualPhysicalThirdOrderJetRadialCurrentChartEvaluation
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (reference chart : Chart period hPeriod) (base : Base period hPeriod)
    (direction : Fin 3) : Real :=
  programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetChartRepresentative
    period hPeriod functional reference chart base direction
    ((globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
      period hPeriod data).extractor chart base)

/-- Evaluation on the assembled physical J3 section is independent of the
chosen valid chart inside a fixed reference-chart star. -/
theorem
    globalCandidateAActualPhysicalThirdOrderJetRadialCurrentChartEvaluation_eq
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (reference first second : Chart period hPeriod)
    (base : Base period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second ∩
        (PhysicalThirdJetCore period hPeriod).baseSet reference)
    (direction : Fin 3) :
    globalCandidateAActualPhysicalThirdOrderJetRadialCurrentChartEvaluation
        period hPeriod data functional reference second base direction =
      globalCandidateAActualPhysicalThirdOrderJetRadialCurrentChartEvaluation
        period hPeriod data functional reference first base direction := by
  unfold
    globalCandidateAActualPhysicalThirdOrderJetRadialCurrentChartEvaluation
  rw [← globalCandidateAActualPhysicalThirdOrderJetExtractor_coordChange
    period hPeriod data first second base ⟨hBase.1.1, hBase.1.2⟩]
  exact
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJet_chartChange
      period hPeriod functional reference first second base hBase direction
      ((globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
        period hPeriod data).extractor first base)

end
end P0EFTJanusProgramPT06ActualPhysicalThirdJetCurrentDescent4D
end JanusFormal
