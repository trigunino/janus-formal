import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetCurrentDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualThroatBaseChartJacobianDensityCocycle4D

/-!
# Covariant physical third-jet vector densities

The three components of the physical J3 current are assembled in the spatial
basis of the jet complex.  An explicit base-chart center supplies the unique
Jacobian needed to combine its vector-density pullback with the genuine
eleven-field J3 coordinate change.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D

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
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetCurrentDescent4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D
open P0EFTJanusProgramPT06ActualThroatBaseChartJacobianDensityCocycle4D

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

/-- A horizontal vector density depending on the genuine physical J3 fiber. -/
abbrev ProgramPT06ActualPhysicalThirdJetVectorDensity4D :=
  ActualPhysicalThirdOrderJetProductFiber → ThroatCoverCoordinates

/-- Assemble the three current components in the same spatial basis used by
the multi-index jet complex. -/
def programPT06ActualPhysicalThirdJetCurrentToVectorDensity
    (current : ProgramPT06ActualPhysicalThirdJetCurrent4D) :
    ProgramPT06ActualPhysicalThirdJetVectorDensity4D :=
  fun jet => programPT06ThroatSpatialBasis.equivFun.symm
    (fun direction => current direction jet)

/-- Vectorization preserves every current component in the spatial basis. -/
@[simp]
theorem programPT06ActualPhysicalThirdJetCurrentToVectorDensity_equivFun_apply
    (current : ProgramPT06ActualPhysicalThirdJetCurrent4D)
    (jet : ActualPhysicalThirdOrderJetProductFiber) (direction : Fin 3) :
    programPT06ThroatSpatialBasis.equivFun
        (programPT06ActualPhysicalThirdJetCurrentToVectorDensity current jet)
        direction =
      current direction jet := by
  change (programPT06ThroatSpatialBasis.equivFun
    (programPT06ThroatSpatialBasis.equivFun.symm
      (fun index => current index jet))) direction = _
  rw [LinearEquiv.apply_symm_apply]

/-- Pull a weight-one contravariant vector density back through a linear
coordinate equivalence. -/
def programPT06ThroatVectorDensityPullback
    (transition : ThroatCoverCoordinates ≃ₗ[Real] ThroatCoverCoordinates)
    (density : ThroatCoverCoordinates) : ThroatCoverCoordinates :=
  |((LinearEquiv.det transition : Realˣ) : Real)| • transition.symm density

@[simp]
theorem programPT06ThroatVectorDensityPullback_refl
    (density : ThroatCoverCoordinates) :
    programPT06ThroatVectorDensityPullback
        (LinearEquiv.refl Real ThroatCoverCoordinates) density = density := by
  simp [programPT06ThroatVectorDensityPullback]

/-- Vector-density pullback is contravariantly functorial. -/
theorem programPT06ThroatVectorDensityPullback_trans
    (first second :
      ThroatCoverCoordinates ≃ₗ[Real] ThroatCoverCoordinates)
    (density : ThroatCoverCoordinates) :
    programPT06ThroatVectorDensityPullback first
        (programPT06ThroatVectorDensityPullback second density) =
      programPT06ThroatVectorDensityPullback (first.trans second) density := by
  simp [programPT06ThroatVectorDensityPullback, abs_mul, mul_smul,
    mul_comm]

/-- Combined pullback by the physical J3 fiber transition and by the unique
explicitly supplied base-coordinate transition. -/
def programPT06ActualPhysicalThirdJetVectorDensityPullback
    (firstCenter secondCenter : Base period hPeriod)
    (base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : Chart period hPeriod)
    (current : ProgramPT06ActualPhysicalThirdJetVectorDensity4D) :
    ProgramPT06ActualPhysicalThirdJetVectorDensity4D :=
  fun jet =>
    programPT06ActualThroatBaseChartJacobianDensityAt period hPeriod
        firstCenter secondCenter base hFirst hSecond •
      (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
        firstCenter secondCenter base hFirst hSecond).symm
        (current ((PhysicalThirdJetCore period hPeriod).coordChange
          first second base jet))

/-- Identity fiber and base charts act trivially on physical J3 vector
densities. -/
@[simp]
theorem programPT06ActualPhysicalThirdJetVectorDensityPullback_self
    (center base : Base period hPeriod)
    (hCenter : base ∈
      (extChartAt throatCoverModelWithCorners center).source)
    (chart : Chart period hPeriod)
    (hBase : base ∈ (PhysicalThirdJetCore period hPeriod).baseSet chart)
    (current : ProgramPT06ActualPhysicalThirdJetVectorDensity4D) :
    programPT06ActualPhysicalThirdJetVectorDensityPullback period hPeriod
        center center base hCenter hCenter chart chart current = current := by
  funext jet
  simp [programPT06ActualPhysicalThirdJetVectorDensityPullback,
    (PhysicalThirdJetCore period hPeriod).coordChange_self chart base hBase jet]

/-- The combined physical J3 vector-density pullback composes on simultaneous
fiber-chart and base-chart triple overlaps. -/
theorem programPT06ActualPhysicalThirdJetVectorDensityPullback_comp
    (firstCenter secondCenter thirdCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (hThird : base ∈
      (extChartAt throatCoverModelWithCorners thirdCenter).source)
    (first second third : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second ∩
        (PhysicalThirdJetCore period hPeriod).baseSet third)
    (current : ProgramPT06ActualPhysicalThirdJetVectorDensity4D) :
    programPT06ActualPhysicalThirdJetVectorDensityPullback period hPeriod
        firstCenter secondCenter base hFirst hSecond first second
        (programPT06ActualPhysicalThirdJetVectorDensityPullback period hPeriod
          secondCenter thirdCenter base hSecond hThird second third current) =
      programPT06ActualPhysicalThirdJetVectorDensityPullback period hPeriod
        firstCenter thirdCenter base hFirst hThird first third current := by
  funext jet
  unfold programPT06ActualPhysicalThirdJetVectorDensityPullback
  rw [(PhysicalThirdJetCore period hPeriod).coordChange_comp
    first second third base hBase jet]
  rw [programPT06ActualThroatBaseChartJacobianDensityAt_comp period hPeriod
    firstCenter secondCenter thirdCenter base hFirst hSecond hThird]
  rw [programPT06ActualThroatBaseChartJacobianEquivAt_trans period hPeriod
    firstCenter secondCenter thirdCenter base hFirst hSecond hThird]
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.map_smul, mul_smul]

/-! ## Radial Cartan vector density -/

/-- Gate925's radial Cartan current as a vector density in the physical J3
fiber. -/
def programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    ProgramPT06ActualPhysicalThirdJetVectorDensity4D :=
  programPT06ActualPhysicalThirdJetCurrentToVectorDensity
    (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetCurrent
      period hPeriod functional)

/-- Radial vector-density representative pulled from a reference fiber chart
and an independently supplied reference base chart. -/
def programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityChartRepresentative
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter base : Base period hPeriod)
    (hReferenceCenter : base ∈
      (extChartAt throatCoverModelWithCorners referenceCenter).source)
    (hChartCenter : base ∈
      (extChartAt throatCoverModelWithCorners chartCenter).source)
    (reference chart : Chart period hPeriod) :
    ProgramPT06ActualPhysicalThirdJetVectorDensity4D :=
  programPT06ActualPhysicalThirdJetVectorDensityPullback period hPeriod
    chartCenter referenceCenter base hChartCenter hReferenceCenter chart
    reference
    (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
      period hPeriod functional)

/-- The radial physical J3 vector-density representatives obey the combined
base/fiber chart law. -/
theorem
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_chartChange
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter firstCenter secondCenter base : Base period hPeriod)
    (hReferenceCenter : base ∈
      (extChartAt throatCoverModelWithCorners referenceCenter).source)
    (hFirstCenter : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecondCenter : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (reference first second : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second ∩
        (PhysicalThirdJetCore period hPeriod).baseSet reference) :
    programPT06ActualPhysicalThirdJetVectorDensityPullback period hPeriod
        firstCenter secondCenter base hFirstCenter hSecondCenter first second
        (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityChartRepresentative
          period hPeriod functional referenceCenter secondCenter base
          hReferenceCenter hSecondCenter reference second) =
      programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityChartRepresentative
        period hPeriod functional referenceCenter firstCenter base
        hReferenceCenter hFirstCenter reference first := by
  exact programPT06ActualPhysicalThirdJetVectorDensityPullback_comp
    period hPeriod firstCenter secondCenter referenceCenter base hFirstCenter
    hSecondCenter hReferenceCenter first second reference hBase
    (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
      period hPeriod functional)

/-! ## Evaluation on the physical J3 section -/

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-- Evaluate the covariant radial representative on the assembled physical J3
section. -/
def globalCandidateAActualPhysicalThirdOrderJetRadialVectorDensityChartEvaluation
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter base : Base period hPeriod)
    (hReferenceCenter : base ∈
      (extChartAt throatCoverModelWithCorners referenceCenter).source)
    (hChartCenter : base ∈
      (extChartAt throatCoverModelWithCorners chartCenter).source)
    (reference chart : Chart period hPeriod) : ThroatCoverCoordinates :=
  programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensityChartRepresentative
    period hPeriod functional referenceCenter chartCenter base hReferenceCenter
    hChartCenter reference chart
    ((globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
      period hPeriod data).extractor chart base)

/-- Evaluations in two valid charts are related by the exact weight-one
vector-density transition law. -/
theorem
    globalCandidateAActualPhysicalThirdOrderJetRadialVectorDensityChartEvaluation_transition
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter firstCenter secondCenter base : Base period hPeriod)
    (hReferenceCenter : base ∈
      (extChartAt throatCoverModelWithCorners referenceCenter).source)
    (hFirstCenter : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecondCenter : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (reference first second : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second ∩
        (PhysicalThirdJetCore period hPeriod).baseSet reference) :
    globalCandidateAActualPhysicalThirdOrderJetRadialVectorDensityChartEvaluation
        period hPeriod data functional referenceCenter firstCenter base
        hReferenceCenter hFirstCenter reference first =
      programPT06ThroatVectorDensityPullback
        (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
          firstCenter secondCenter base hFirstCenter hSecondCenter)
        (globalCandidateAActualPhysicalThirdOrderJetRadialVectorDensityChartEvaluation
          period hPeriod data functional referenceCenter secondCenter base
          hReferenceCenter hSecondCenter reference second) := by
  have hLaw := congrFun
    (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_chartChange
      period hPeriod functional referenceCenter firstCenter secondCenter base
      hReferenceCenter hFirstCenter hSecondCenter reference first second hBase)
    ((globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
      period hPeriod data).extractor first base)
  unfold programPT06ActualPhysicalThirdJetVectorDensityPullback at hLaw
  rw [globalCandidateAActualPhysicalThirdOrderJetExtractor_coordChange
    period hPeriod data first second base ⟨hBase.1.1, hBase.1.2⟩] at hLaw
  unfold
    globalCandidateAActualPhysicalThirdOrderJetRadialVectorDensityChartEvaluation
  simpa [programPT06ThroatVectorDensityPullback,
    programPT06ActualThroatBaseChartJacobianDensityAt] using hLaw.symm

end
end P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D
end JanusFormal
