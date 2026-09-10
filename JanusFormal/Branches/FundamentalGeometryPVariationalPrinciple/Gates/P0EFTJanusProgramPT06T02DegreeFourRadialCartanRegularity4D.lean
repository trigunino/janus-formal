import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02DegreeFourRadialCartanClassification4D

/-!
# Regularity of the terminal T02 radial Cartan current

The radial contractions, their first prolongations, and the three-point
quadrature current preserve smoothness of a second-order local function.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators ContDiff

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06SecondOrderEulerHigherFrechetFormula4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetHigherFrechetDerivative4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanClassification4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

universe u v

section Generic

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
variable {Target : Type v} [NormedAddCommGroup Target] [NormedSpace Real Target]

/-- A vertical partial preserves smoothness of infinite order. -/
theorem programPT06ThroatSpatialVerticalPartialDerivative_contDiff_top
    {order : Nat}
    (localFunction :
      TruncatedThroatSpatialMultiindexJet Fiber order → Target)
    (hLocalFunction : ContDiff Real ∞ localFunction)
    (index : ThroatSpatialTruncatedIndex order) :
    ContDiff Real ∞
      (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
        localFunction jet index) := by
  unfold programPT06ThroatSpatialVerticalPartialDerivative
  have hDerivative : ContDiff Real ∞ (fderiv Real localFunction) :=
    hLocalFunction.fderiv_right (m := ∞) (by simp)
  exact hDerivative.clm_comp contDiff_const

/-- One formal total derivative preserves smoothness of infinite order. -/
theorem programPT06ThroatSpatialLocalFunctionTotalDerivative_contDiff_top
    {order : Nat}
    (localFunction :
      TruncatedThroatSpatialMultiindexJet Fiber order → Target)
    (hLocalFunction : ContDiff Real ∞ localFunction)
    (direction : Fin 3) :
    ContDiff Real ∞
      (programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        localFunction) := by
  unfold programPT06ThroatSpatialLocalFunctionTotalDerivative
  have hDerivative : ContDiff Real ∞ (fderiv Real localFunction) :=
    hLocalFunction.fderiv_right (m := ∞) (by simp)
  apply (hDerivative.comp ?_).clm_apply
  · unfold throatSpatialTotalDerivative
    fun_prop
  · unfold truncateThroatSpatialMultiindexJet
    fun_prop

/-- Contracting a smooth covector field with a radial jet coordinate is
smooth. -/
theorem programPT06ThroatSpatialRadialContraction_contDiff_top
    {order : Nat}
    (coefficient : TruncatedThroatSpatialMultiindexJet Fiber order →
      (Fiber →L[Real] Real))
    (hCoefficient : ContDiff Real ∞ coefficient)
    (index : ThroatSpatialTruncatedIndex order) :
    ContDiff Real ∞
      (programPT06ThroatSpatialRadialContraction coefficient index) := by
  change ContDiff Real ∞
    (fun jet => coefficient jet (jet index))
  apply hCoefficient.clm_apply
  fun_prop

private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber

theorem programPT06SecondOrderRadialFirstContraction_contDiff_top
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (direction : Fin 3) :
    ContDiff Real ∞
      (programPT06SecondOrderRadialFirstContraction
        localLagrangian direction) := by
  apply programPT06ThroatSpatialRadialContraction_contDiff_top
  change ContDiff Real ∞
    (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
      localLagrangian jet
      (programPT06SecondOrderFirstMultiIndex direction))
  exact programPT06ThroatSpatialVerticalPartialDerivative_contDiff_top
    localLagrangian hLagrangian
    (programPT06SecondOrderFirstMultiIndex direction)

theorem programPT06SecondOrderRadialSecondContraction_contDiff_top
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (first second : Fin 3) :
    ContDiff Real ∞
      (programPT06SecondOrderRadialSecondContraction
        localLagrangian first second) := by
  apply programPT06ThroatSpatialRadialContraction_contDiff_top
  change ContDiff Real ∞
    (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
      localLagrangian jet
      (programPT06SecondOrderSecondMultiIndex first second))
  exact programPT06ThroatSpatialVerticalPartialDerivative_contDiff_top
    localLagrangian hLagrangian
    (programPT06SecondOrderSecondMultiIndex first second)

theorem
    programPT06SecondOrderRadialProlongedSecondContraction_contDiff_top
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (first second : Fin 3) :
    ContDiff Real ∞
      (programPT06SecondOrderRadialProlongedSecondContraction
        localLagrangian first second) := by
  apply programPT06ThroatSpatialRadialContraction_contDiff_top
  change ContDiff Real ∞
    (programPT06ThroatSpatialLocalFunctionTotalDerivative second
      (fun jet => programPT06ThroatSpatialVerticalPartialDerivative
        localLagrangian jet
        (programPT06SecondOrderSecondMultiIndex first second)))
  apply programPT06ThroatSpatialLocalFunctionTotalDerivative_contDiff_top
  exact programPT06ThroatSpatialVerticalPartialDerivative_contDiff_top
    localLagrangian hLagrangian
    (programPT06SecondOrderSecondMultiIndex first second)

/-- Every component of the unscaled radial Cartan current is smooth when
the local Lagrangian is smooth. -/
theorem programPT06SecondOrderRadialCartanCurrentComponent_contDiff_top
    (localLagrangian : SecondJet (Fiber := Fiber) → Real)
    (hLagrangian : ContDiff Real ∞ localLagrangian)
    (direction : Fin 3) :
    ContDiff Real ∞
      (programPT06SecondOrderRadialCartanCurrentComponent
        localLagrangian direction) := by
  have hTruncate : ContDiff Real ∞
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) :
        ThirdJet (Fiber := Fiber) → SecondJet (Fiber := Fiber)) := by
    unfold truncateThroatSpatialMultiindexJet
    fun_prop
  have hFirst : ContDiff Real ∞
      (fun jet : ThirdJet (Fiber := Fiber) =>
        programPT06SecondOrderRadialFirstContraction
          localLagrangian direction
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) :=
    (programPT06SecondOrderRadialFirstContraction_contDiff_top
      localLagrangian hLagrangian direction).comp hTruncate
  have hFamily (second : Fin 3) : ContDiff Real ∞
      (fun jet : ThirdJet (Fiber := Fiber) =>
        programPT06SecondOrderEulerSymmetryWeight direction second •
          (programPT06SecondOrderRadialSecondContraction
              localLagrangian direction second
              (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) -
            programPT06SecondOrderRadialProlongedSecondContraction
              localLagrangian direction second jet)) := by
    have hSecond : ContDiff Real ∞
        (fun jet : ThirdJet (Fiber := Fiber) =>
          programPT06SecondOrderRadialSecondContraction
            localLagrangian direction second
            (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)) :=
      (programPT06SecondOrderRadialSecondContraction_contDiff_top
        localLagrangian hLagrangian direction second).comp hTruncate
    have hProlonged :=
      programPT06SecondOrderRadialProlongedSecondContraction_contDiff_top
        localLagrangian hLagrangian direction second
    exact (hSecond.sub hProlonged).const_smul
      (programPT06SecondOrderEulerSymmetryWeight direction second : Real)
  change ContDiff Real ∞
    (fun jet : ThirdJet (Fiber := Fiber) =>
      programPT06SecondOrderRadialFirstContraction
          localLagrangian direction
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) +
        ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight direction second •
            (programPT06SecondOrderRadialSecondContraction
                localLagrangian direction second
                (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) -
              programPT06SecondOrderRadialProlongedSecondContraction
                localLagrangian direction second jet))
  exact hFirst.add (ContDiff.sum fun second _ => hFamily second)

/-- Infinite-order regularity is preserved by the three-sample quadrature
operation on currents. -/
theorem programPT06SecondOrderRadialQuadratureCurrent_component_contDiff_top
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber))
    (hCurrent : ∀ direction, ContDiff Real ∞ (current direction))
    (direction : Fin 3) :
    ContDiff Real ∞
      (programPT06SecondOrderRadialQuadratureCurrent current direction) := by
  have hScaled (scalar : Real) : ContDiff Real ∞
      (programPT06SecondOrderHorizontalCurrentPrecomposeScaling
        scalar current direction) := by
    change ContDiff Real ∞
      (current direction ∘
        programPT06ThroatSpatialJetScalingContinuousLinearMap
          (Fiber := Fiber) 3 scalar)
    exact (hCurrent direction).comp
      (programPT06ThroatSpatialJetScalingContinuousLinearMap
        (Fiber := Fiber) 3 scalar).contDiff
  change ContDiff Real ∞
    (fun jet : ThirdJet (Fiber := Fiber) =>
      ((8 / 3 : Real) • current direction ((1 / 4 : Real) • jet) +
        (-2 / 3 : Real) • current direction ((1 / 2 : Real) • jet)) +
        (8 / 9 : Real) • current direction ((3 / 4 : Real) • jet))
  exact (((hScaled (1 / 4 : Real)).const_smul (8 / 3 : Real)).add
    ((hScaled (1 / 2 : Real)).const_smul (-2 / 3 : Real))).add
    ((hScaled (3 / 4 : Real)).const_smul (8 / 9 : Real))

end Generic

private abbrev Fiber := ActualPhysicalValueProductFiber

variable (period : Real) (hPeriod : period ≠ 0)

/-- Every component of the explicit terminal T02 quadrature Cartan current
is smooth to all finite orders. -/
theorem programPT06T02DegreeFourRadialCartanCurrent_component_contDiff
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (direction : Fin 3) :
    ContDiff Real ∞
      (programPT06T02DegreeFourRadialCartanCurrent
        period hPeriod functional direction) := by
  let localLagrangian :=
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
  have hLagrangian : ContDiff Real ∞ localLagrangian :=
    programPT06T02FinsuppSecondJetLocalLagrangian_contDiff
      period hPeriod functional
  change ContDiff Real ∞
    (programPT06SecondOrderRadialQuadratureCurrent
      (programPT06SecondOrderRadialCartanCurrent localLagrangian) direction)
  apply programPT06SecondOrderRadialQuadratureCurrent_component_contDiff_top
  intro component
  exact programPT06SecondOrderRadialCartanCurrentComponent_contDiff_top
    localLagrangian hLagrangian component

/-- Componentwise formulation of smoothness of the complete T02 current. -/
theorem programPT06T02DegreeFourRadialCartanCurrent_contDiff
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    ∀ direction : Fin 3,
      ContDiff Real ∞
        (programPT06T02DegreeFourRadialCartanCurrent
          period hPeriod functional direction) := by
  intro direction
  exact programPT06T02DegreeFourRadialCartanCurrent_component_contDiff
    period hPeriod functional direction

/-- Compact classification with one canonical current that is smooth in
every component. -/
theorem programPT06T02DegreeFour_exists_smooth_current_of_euler_eq_zero
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (hEuler : ∀ jet : ThroatSpatialMultiindexJet4 Fiber,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet = 0) :
    ∃ current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber),
      (∀ direction : Fin 3, ContDiff Real ∞ (current direction)) ∧
        ∀ jet : ThroatSpatialMultiindexJet4 Fiber,
          programPT06T02FinsuppSecondJetLocalLagrangian
              period hPeriod functional
              (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) =
            functional.lower.lower.constant +
              programPT06SecondOrderHorizontalCurrentDH current jet := by
  refine ⟨programPT06T02DegreeFourRadialCartanCurrent
    period hPeriod functional, ?_, ?_⟩
  · exact programPT06T02DegreeFourRadialCartanCurrent_contDiff
      period hPeriod functional
  · intro jet
    exact
      programPT06T02DegreeFourLocalLagrangian_eq_constant_add_currentDH
        period hPeriod functional hEuler jet

end
end P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D
end JanusFormal
