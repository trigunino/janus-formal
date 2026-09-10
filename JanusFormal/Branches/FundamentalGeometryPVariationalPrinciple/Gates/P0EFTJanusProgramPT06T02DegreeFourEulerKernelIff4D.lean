import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderHorizontalDivergenceEulerClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D

/-!
# Bidirectional terminal T02 Euler-kernel classification

The completed horizontal-divergence soundness theorem supplies the reverse
direction of the radial Cartan classification.  Consequently the genuine
Gate880 Euler expression of the terminal degree-four T02 density vanishes
exactly when the density is its prescribed constant plus the horizontal
divergence of a smooth third-jet current.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02DegreeFourEulerKernelIff4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetHigherFrechetDerivative4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
open P0EFTJanusProgramPT06SecondOrderHorizontalDivergenceEulerClosure4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanClassification4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanRegularity4D

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

private abbrev Fiber := ActualPhysicalValueProductFiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

variable (period : Real) (hPeriod : period ≠ 0)

/-- The strongest concrete form: Euler vanishing is equivalent to the exact
representation by the canonical smooth radial Cartan current. -/
theorem programPT06T02DegreeFour_euler_eq_zero_iff_radialCartanCurrent
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    (∀ jet : FourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet = 0) ↔
      ∀ jet : FourthJet,
        programPT06T02FinsuppSecondJetLocalLagrangian
            period hPeriod functional
            (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) =
          functional.lower.lower.constant +
            programPT06SecondOrderHorizontalCurrentDH
              (programPT06T02DegreeFourRadialCartanCurrent
                period hPeriod functional) jet := by
  constructor
  · intro hEuler jet
    exact programPT06T02DegreeFourLocalLagrangian_eq_constant_add_currentDH
      period hPeriod functional hEuler jet
  · intro hFactor jet
    exact
      programPT06SecondOrderHorizontalDivergenceSoundness_of_constant_add
      (programPT06T02FinsuppSecondJetLocalLagrangian
        period hPeriod functional)
      (programPT06T02DegreeFourRadialCartanCurrent
        period hPeriod functional)
      functional.lower.lower.constant
      (programPT06T02FinsuppSecondJetLocalLagrangian_contDiff
        period hPeriod functional)
      (programPT06T02DegreeFourRadialCartanCurrent_contDiff
        period hPeriod functional)
      hFactor jet

/-- Terminal T02 local exactness in both directions, with the genuine Gate880
Euler operator and a smooth third-jet horizontal current. -/
theorem programPT06T02DegreeFour_euler_eq_zero_iff_exists_smooth_current
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    (∀ jet : FourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet = 0) ↔
      ∃ current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber),
        (∀ direction : Fin 3, ContDiff Real ∞ (current direction)) ∧
          ∀ jet : FourthJet,
            programPT06T02FinsuppSecondJetLocalLagrangian
                period hPeriod functional
                (truncateThroatSpatialMultiindexJet
                  (by omega : 2 ≤ 4) jet) =
              functional.lower.lower.constant +
                programPT06SecondOrderHorizontalCurrentDH current jet := by
  constructor
  · intro hEuler
    exact programPT06T02DegreeFour_exists_smooth_current_of_euler_eq_zero
      period hPeriod functional hEuler
  · rintro ⟨current, hCurrent, hFactor⟩
    intro jet
    exact
      programPT06SecondOrderHorizontalDivergenceSoundness_of_constant_add
      (programPT06T02FinsuppSecondJetLocalLagrangian
        period hPeriod functional)
      current functional.lower.lower.constant
      (programPT06T02FinsuppSecondJetLocalLagrangian_contDiff
        period hPeriod functional)
      hCurrent hFactor jet

end
end P0EFTJanusProgramPT06T02DegreeFourEulerKernelIff4D
end JanusFormal
