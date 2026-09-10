import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderEulerHigherFrechetFormula4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02FinsuppSecondJetHigherFrechetDerivative4D

/-!
# Higher Frechet formula for the terminal T02 Euler operator

This support gate specializes Gate922's complete second-order Euler formula
to the terminal T02 local Lagrangian on the genuine finsupp second-jet
carrier.  Its first, second and third Frechet derivatives are the explicit
maps from Gates882 and 921.

No Euler-kernel classification or horizontal primitive is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02SecondOrderEulerHigherFrechetFormula4D

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
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06SecondOrderEulerHigherFrechetFormula4D
open P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetHigherFrechetDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

private abbrev Fiber := ActualPhysicalValueProductFiber
private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

variable (period : Real) (hPeriod : period ≠ 0)

/-- Gate922 specialized to the complete terminal T02 local Lagrangian, with
all derivatives replaced by the explicit maps from Gates882 and 921. -/
theorem programPT06SecondOrderLocalEuler_t02FinsuppDegreeFour_formula
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : FourthJet) (variation : Fiber) :
    programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet variation =
      programPT06T02FinsuppSecondJetFrechetDerivative
          period hPeriod functional
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
          (programPT06ThroatSpatialJetCoordinateInjection
            programPT06SecondOrderZeroMultiIndex variation) -
        (∑ direction : Fin 3,
          programPT06T02FinsuppSecondJetSecondFrechetDerivative
            period hPeriod functional
            (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
            ![throatSpatialTotalDerivative direction
                (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet),
              programPT06ThroatSpatialJetCoordinateInjection
                (programPT06SecondOrderFirstMultiIndex direction) variation]) +
        ∑ first : Fin 3, ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight first second •
            (programPT06T02FinsuppSecondJetThirdFrechetDerivative
                period hPeriod functional
                (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
                ![throatSpatialTotalDerivative first
                    (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet),
                  throatSpatialTotalDerivative second
                    (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet),
                  programPT06ThroatSpatialJetCoordinateInjection
                    (programPT06SecondOrderSecondMultiIndex first second)
                    variation] +
              programPT06T02FinsuppSecondJetSecondFrechetDerivative
                period hPeriod functional
                (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
                ![throatSpatialTotalDerivative second
                    (throatSpatialTotalDerivative first jet),
                  programPT06ThroatSpatialJetCoordinateInjection
                    (programPT06SecondOrderSecondMultiIndex first second)
                    variation]) := by
  have hOne (base direction : SecondJet) :
      programPT06SecondOrderEulerHigherFrechetDerivative 1
          (programPT06T02FinsuppSecondJetLocalLagrangian
            period hPeriod functional) base ![direction] =
        programPT06T02FinsuppSecondJetFrechetDerivative
          period hPeriod functional base direction := by
    simp [programPT06SecondOrderEulerHigherFrechetDerivative,
      programPT06T02FinsuppSecondJetLocalLagrangian_fderiv]
  have hTwo (base : SecondJet) (directions : Fin 2 → SecondJet) :
      programPT06SecondOrderEulerHigherFrechetDerivative 2
          (programPT06T02FinsuppSecondJetLocalLagrangian
            period hPeriod functional) base directions =
        programPT06T02FinsuppSecondJetSecondFrechetDerivative
          period hPeriod functional base directions := by
    change
      iteratedFDeriv Real 2
          (programPT06T02FinsuppSecondJetLocalLagrangian
            period hPeriod functional) base directions = _
    exact congrArg
      (fun derivative : SecondJet [×2]→L[Real] Real =>
        derivative directions)
      (programPT06T02FinsuppSecondJetSecondFrechetDerivative_eq_iteratedFDeriv
        period hPeriod functional base).symm
  have hThree (base : SecondJet) (directions : Fin 3 → SecondJet) :
      programPT06SecondOrderEulerHigherFrechetDerivative 3
          (programPT06T02FinsuppSecondJetLocalLagrangian
            period hPeriod functional) base directions =
        programPT06T02FinsuppSecondJetThirdFrechetDerivative
          period hPeriod functional base directions := by
    change
      iteratedFDeriv Real 3
          (programPT06T02FinsuppSecondJetLocalLagrangian
            period hPeriod functional) base directions = _
    exact congrArg
      (fun derivative : SecondJet [×3]→L[Real] Real =>
        derivative directions)
      (programPT06T02FinsuppSecondJetThirdFrechetDerivative_eq_iteratedFDeriv
        period hPeriod functional base).symm
  have hC3 : ContDiff Real 3
      (programPT06T02FinsuppSecondJetLocalLagrangian
        period hPeriod functional) :=
    (programPT06T02FinsuppSecondJetLocalLagrangian_contDiff
      period hPeriod functional).of_le
        (show (3 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [programPT06SecondOrderLocalEuler_eq_higherFrechet
    (programPT06T02FinsuppSecondJetLocalLagrangian
      period hPeriod functional) hC3 jet variation]
  simp_rw [hOne, hTwo, hThree]

end
end P0EFTJanusProgramPT06T02SecondOrderEulerHigherFrechetFormula4D
end JanusFormal
