import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D

/-!
# T02 Frechet derivative on genuine spatial second jets

This gate pulls the terminal T02 local functional back along the continuous
linear identification between the genuine finsupp second jet and the actual
physical second-order jet product, and computes its fiberwise derivative by
the chain rule.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

private abbrev RawActualPhysicalValueProductFiber :=
  ((ActualGaugeValueProductFiber × ActualLLValueProductFiber) ×
      ActualMetricValueProductFiber) × ActualSpinCValueProductFiber

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

private abbrev FinsuppSecondJet :=
  ThroatSpatialMultiindexJet2 ActualPhysicalValueProductFiber

private abbrev PhysicalSecondJet :=
  ActualPhysicalSecondOrderJetProductFiber

variable (period : Real) (hPeriod : period ≠ 0)

/-- Gate881's algebraic bridge, viewed with the analytic structures used by
the T02 derivative. -/
def programPT06T02FinsuppSecondJetBridgeLinearMap :
    FinsuppSecondJet →ₗ[Real] PhysicalSecondJet where
  toFun := programPT06ActualPhysicalValueProductFinsuppSecondJetLinearEquiv
  map_add' first second := by
    exact
      programPT06ActualPhysicalValueProductFinsuppSecondJetLinearEquiv.map_add
        first second
  map_smul' scalar jet := by
    exact
      programPT06ActualPhysicalValueProductFinsuppSecondJetLinearEquiv.map_smul
        scalar jet

/-- Continuous form of the Gate881 bridge in the T02 analytic structure. -/
def programPT06T02FinsuppSecondJetBridge :
    FinsuppSecondJet →L[Real] PhysicalSecondJet :=
  programPT06T02FinsuppSecondJetBridgeLinearMap.toContinuousLinearMap

/-- The terminal T02 local Lagrangian pulled back to the genuine spatial
multi-index second-jet carrier. -/
def programPT06T02FinsuppSecondJetLocalLagrangian
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    FinsuppSecondJet → Real :=
  actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
      functional ∘
    programPT06T02FinsuppSecondJetBridge

@[simp] theorem programPT06T02FinsuppSecondJetLocalLagrangian_apply
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional jet =
      actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        functional
        (programPT06T02FinsuppSecondJetBridge
          jet) := by
  rfl

/-- Explicit derivative of the pulled-back local Lagrangian: compose the T02
derivative from Gate878 with the continuous linear second-jet bridge. -/
def programPT06T02FinsuppSecondJetFrechetDerivative
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) : FinsuppSecondJet →L[Real] Real :=
  (programPT06T02DegreeFourFrechetDerivative period hPeriod functional
      (programPT06T02FinsuppSecondJetBridge
        jet)).comp
    programPT06T02FinsuppSecondJetBridge

@[simp] theorem programPT06T02FinsuppSecondJetFrechetDerivative_apply
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet direction : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetFrechetDerivative period hPeriod functional
        jet direction =
      programPT06T02DegreeFourFrechetDerivative period hPeriod functional
        (programPT06T02FinsuppSecondJetBridge
          jet)
        (programPT06T02FinsuppSecondJetBridge
          direction) := by
  rfl

/-- Chain-rule certificate for the pulled-back T02 local Lagrangian. -/
theorem programPT06T02FinsuppSecondJetLocalLagrangian_hasFDerivAt
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) :
    HasFDerivAt
      (programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional)
      (programPT06T02FinsuppSecondJetFrechetDerivative period hPeriod functional
        jet)
      jet := by
  simpa [programPT06T02FinsuppSecondJetLocalLagrangian,
    programPT06T02FinsuppSecondJetFrechetDerivative] using
    (programPT06T02DegreeFourEvaluation_hasFDerivAt period hPeriod functional
      (programPT06T02FinsuppSecondJetBridge
        jet)).comp jet
      programPT06T02FinsuppSecondJetBridge.hasFDerivAt

/-- `fderiv` of the pulled-back T02 local Lagrangian. -/
theorem programPT06T02FinsuppSecondJetLocalLagrangian_fderiv
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) :
    fderiv Real
        (programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional)
        jet =
      programPT06T02FinsuppSecondJetFrechetDerivative period hPeriod functional
        jet :=
  (programPT06T02FinsuppSecondJetLocalLagrangian_hasFDerivAt
    period hPeriod functional jet).fderiv

end

end P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
end JanusFormal
