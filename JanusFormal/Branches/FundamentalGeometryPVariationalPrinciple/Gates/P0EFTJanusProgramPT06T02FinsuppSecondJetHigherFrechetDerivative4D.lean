import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DiagonalPolynomialHigherFrechetDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D

/-!
# Higher T02 Frechet derivatives on genuine spatial second jets

This support gate pulls Gate919's higher derivatives of the complete T02
degree-at-most-four polynomial through Gate881's continuous linear bridge.
It gives a generic iterated derivative, explicit injection formulas, and
specialized second, third and fourth derivatives on the genuine finsupp
second-jet carrier.

No Euler-kernel classification or horizontal primitive is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02FinsuppSecondJetHigherFrechetDerivative4D

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
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D
open P0EFTJanusProgramPT06DiagonalPolynomialHigherFrechetDerivative4D
open P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

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

/-! ## Smooth physical polynomial and its higher derivatives -/

/-- The original terminal T02 evaluation is smooth on the actual physical
second-jet fiber. -/
theorem programPT06T02DegreeFourEvaluation_contDiff
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    ContDiff Real ∞
      (actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation
        period hPeriod functional) := by
  rw [programPT06T02DegreeFourEvaluation_eq period hPeriod functional]
  exact programPT06DiagonalPolynomialEvaluation_contDiff
    (programPT06T02DegreeFourDiagonalPolynomial period hPeriod functional)

/-- Explicit order-`k` derivative of the terminal T02 evaluation on the
actual physical second-jet fiber. -/
def programPT06T02PhysicalHigherFrechetDerivative
    (order : Nat)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : PhysicalSecondJet) :
    PhysicalSecondJet [×order]→L[Real] Real :=
  programPT06DiagonalPolynomialHigherDerivative order
    (programPT06T02DegreeFourDiagonalPolynomial period hPeriod functional) jet

/-- The explicit physical formula is the actual iterated Frechet derivative. -/
theorem programPT06T02PhysicalHigherFrechetDerivative_eq_iteratedFDeriv
    (order : Nat)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : PhysicalSecondJet) :
    programPT06T02PhysicalHigherFrechetDerivative
        period hPeriod order functional jet =
      iteratedFDeriv Real order
        (actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation
          period hPeriod functional) jet := by
  rw [programPT06T02DegreeFourEvaluation_eq period hPeriod functional]
  exact programPT06DiagonalPolynomialHigherDerivative_eq_iteratedFDeriv
    order
    (programPT06T02DegreeFourDiagonalPolynomial period hPeriod functional) jet

/-! ## Pullback to the genuine finsupp second jet -/

/-- Gate919's order-`k` derivative pulled through every argument of the
continuous linear Gate881 bridge. -/
def programPT06T02FinsuppSecondJetHigherFrechetDerivative
    (order : Nat)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) :
    FinsuppSecondJet [×order]→L[Real] Real :=
  (programPT06T02PhysicalHigherFrechetDerivative period hPeriod order functional
      (programPT06T02FinsuppSecondJetBridge jet)).compContinuousLinearMap
    (fun _ : Fin order => programPT06T02FinsuppSecondJetBridge)

/-- Composition formula: the bridge acts on the base jet and on every
labelled variation. -/
@[simp] theorem programPT06T02FinsuppSecondJetHigherFrechetDerivative_apply
    (order : Nat)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet)
    (variations : Fin order → FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetHigherFrechetDerivative
        period hPeriod order functional jet variations =
      programPT06T02PhysicalHigherFrechetDerivative
        period hPeriod order functional
        (programPT06T02FinsuppSecondJetBridge jet)
        (fun slot => programPT06T02FinsuppSecondJetBridge (variations slot)) := by
  rfl

/-- Fully explicit sum-over-injections formula after transport through the
Gate881 bridge. -/
theorem programPT06T02FinsuppSecondJetHigherFrechetDerivative_injection_formula
    (order : Nat)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet)
    (variations : Fin order → FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetHigherFrechetDerivative
        period hPeriod order functional jet variations =
      (∑ injection : Fin order ↪ Fin 0,
        programPT06DiagonalConstantHomogeneousForm
          (FieldFiber := PhysicalSecondJet) functional.lower.lower.constant
          (programPT06DiagonalInjectedArguments
            (programPT06T02FinsuppSecondJetBridge jet)
            (fun slot =>
              programPT06T02FinsuppSecondJetBridge (variations slot))
            injection)) +
      (∑ injection : Fin order ↪ Fin 1,
        programPT06DiagonalLinearHomogeneousForm
          functional.lower.lower.linear.1
          (programPT06DiagonalInjectedArguments
            (programPT06T02FinsuppSecondJetBridge jet)
            (fun slot =>
              programPT06T02FinsuppSecondJetBridge (variations slot))
            injection)) +
      (∑ injection : Fin order ↪ Fin 2,
        programPT06T02UncurryBilinearForm
          functional.lower.lower.quadratic.1
          (programPT06DiagonalInjectedArguments
            (programPT06T02FinsuppSecondJetBridge jet)
            (fun slot =>
              programPT06T02FinsuppSecondJetBridge (variations slot))
            injection)) +
      (∑ injection : Fin order ↪ Fin 3,
        programPT06T02UncurryTrilinearForm functional.lower.cubic.1
          (programPT06DiagonalInjectedArguments
            (programPT06T02FinsuppSecondJetBridge jet)
            (fun slot =>
              programPT06T02FinsuppSecondJetBridge (variations slot))
            injection)) +
      ∑ injection : Fin order ↪ Fin 4,
        programPT06T02UncurryQuadrilinearForm functional.quartic.1
          (programPT06DiagonalInjectedArguments
            (programPT06T02FinsuppSecondJetBridge jet)
            (fun slot =>
              programPT06T02FinsuppSecondJetBridge (variations slot))
            injection) := by
  simp [programPT06T02FinsuppSecondJetHigherFrechetDerivative,
    programPT06T02PhysicalHigherFrechetDerivative,
    programPT06T02DegreeFourDiagonalPolynomial]

/-- The transported injection formula is the actual iterated derivative of
the genuine finsupp local Lagrangian. -/
theorem programPT06T02FinsuppSecondJetHigherFrechetDerivative_eq_iteratedFDeriv
    (order : Nat)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetHigherFrechetDerivative
        period hPeriod order functional jet =
      iteratedFDeriv Real order
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet := by
  unfold programPT06T02FinsuppSecondJetHigherFrechetDerivative
  change _ = iteratedFDeriv Real order
    ((actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation
        period hPeriod functional) ∘
      programPT06T02FinsuppSecondJetBridge) jet
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right
    programPT06T02FinsuppSecondJetBridge
    (programPT06T02DegreeFourEvaluation_contDiff
      period hPeriod functional) jet
    (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  rw [← programPT06T02PhysicalHigherFrechetDerivative_eq_iteratedFDeriv
    period hPeriod order functional
      (programPT06T02FinsuppSecondJetBridge jet)]

/-- The pulled-back local Lagrangian is smooth to every finite order. -/
theorem programPT06T02FinsuppSecondJetLocalLagrangian_contDiff
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    ContDiff Real ∞
      (programPT06T02FinsuppSecondJetLocalLagrangian
        period hPeriod functional) :=
  (programPT06T02DegreeFourEvaluation_contDiff
      period hPeriod functional).comp
    programPT06T02FinsuppSecondJetBridge.contDiff

/-! ## Orders two, three and four -/

def programPT06T02FinsuppSecondJetSecondFrechetDerivative
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) : FinsuppSecondJet [×2]→L[Real] Real :=
  programPT06T02FinsuppSecondJetHigherFrechetDerivative
    period hPeriod 2 functional jet

@[simp] theorem programPT06T02FinsuppSecondJetSecondFrechetDerivative_apply
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) (variations : Fin 2 → FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetSecondFrechetDerivative
        period hPeriod functional jet variations =
      programPT06T02PhysicalHigherFrechetDerivative
        period hPeriod 2 functional
        (programPT06T02FinsuppSecondJetBridge jet)
        (fun slot => programPT06T02FinsuppSecondJetBridge (variations slot)) := by
  rfl

theorem programPT06T02FinsuppSecondJetSecondFrechetDerivative_eq_iteratedFDeriv
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetSecondFrechetDerivative
        period hPeriod functional jet =
      iteratedFDeriv Real 2
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet :=
  programPT06T02FinsuppSecondJetHigherFrechetDerivative_eq_iteratedFDeriv
    period hPeriod 2 functional jet

def programPT06T02FinsuppSecondJetThirdFrechetDerivative
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) : FinsuppSecondJet [×3]→L[Real] Real :=
  programPT06T02FinsuppSecondJetHigherFrechetDerivative
    period hPeriod 3 functional jet

@[simp] theorem programPT06T02FinsuppSecondJetThirdFrechetDerivative_apply
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) (variations : Fin 3 → FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetThirdFrechetDerivative
        period hPeriod functional jet variations =
      programPT06T02PhysicalHigherFrechetDerivative
        period hPeriod 3 functional
        (programPT06T02FinsuppSecondJetBridge jet)
        (fun slot => programPT06T02FinsuppSecondJetBridge (variations slot)) := by
  rfl

theorem programPT06T02FinsuppSecondJetThirdFrechetDerivative_eq_iteratedFDeriv
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetThirdFrechetDerivative
        period hPeriod functional jet =
      iteratedFDeriv Real 3
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet :=
  programPT06T02FinsuppSecondJetHigherFrechetDerivative_eq_iteratedFDeriv
    period hPeriod 3 functional jet

def programPT06T02FinsuppSecondJetFourthFrechetDerivative
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) : FinsuppSecondJet [×4]→L[Real] Real :=
  programPT06T02FinsuppSecondJetHigherFrechetDerivative
    period hPeriod 4 functional jet

@[simp] theorem programPT06T02FinsuppSecondJetFourthFrechetDerivative_apply
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) (variations : Fin 4 → FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetFourthFrechetDerivative
        period hPeriod functional jet variations =
      programPT06T02PhysicalHigherFrechetDerivative
        period hPeriod 4 functional
        (programPT06T02FinsuppSecondJetBridge jet)
        (fun slot => programPT06T02FinsuppSecondJetBridge (variations slot)) := by
  rfl

theorem programPT06T02FinsuppSecondJetFourthFrechetDerivative_eq_iteratedFDeriv
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetFourthFrechetDerivative
        period hPeriod functional jet =
      iteratedFDeriv Real 4
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet :=
  programPT06T02FinsuppSecondJetHigherFrechetDerivative_eq_iteratedFDeriv
    period hPeriod 4 functional jet

end
end P0EFTJanusProgramPT06T02FinsuppSecondJetHigherFrechetDerivative4D
end JanusFormal
