import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02DegreeFourEulerKernelIff4D

/-!
# Chartwise horizontal differential of physical third-jet vector densities

The components of a physical J3 vector density in the fixed throat spatial
basis define a formal second-order horizontal current.  Its horizontal
differential is therefore defined on the formal physical J4 carrier.  For the
radial Cartan vector density this recovers exactly Gate925's current and its
Euler-kernel factorization.  This is a chartwise statement; no global Stokes
map is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityHorizontalDifferential4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanClassification4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetCurrentDescent4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

/-- Formal J4 carrier for the actual physical value-product fiber. -/
abbrev ProgramPT06ActualPhysicalFormalFourthJet4D :=
  ThroatSpatialMultiindexJet4 ActualPhysicalValueProductFiber

/-- Read a physical J3 vector density as a three-component current in the
fixed throat spatial basis. -/
def programPT06ActualPhysicalThirdJetVectorDensitySpatialCurrent
    (density : ProgramPT06ActualPhysicalThirdJetVectorDensity4D) :
    ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := ActualPhysicalValueProductFiber) :=
  fun direction jet =>
    programPT06ThroatSpatialBasis.equivFun
      (density (programPT06ActualPhysicalValueProductThirdJetLinearEquiv jet))
      direction

/-- Vectorization followed by component extraction recovers the current
after the exact physical J3 carrier equivalence. -/
@[simp]
theorem
    programPT06ActualPhysicalThirdJetVectorDensitySpatialCurrent_currentToVectorDensity
    (current : ProgramPT06ActualPhysicalThirdJetCurrent4D) :
    programPT06ActualPhysicalThirdJetVectorDensitySpatialCurrent
        (programPT06ActualPhysicalThirdJetCurrentToVectorDensity current) =
      fun direction jet =>
        current direction
          (programPT06ActualPhysicalValueProductThirdJetLinearEquiv jet) := by
  funext direction jet
  simp [programPT06ActualPhysicalThirdJetVectorDensitySpatialCurrent]

/-- Formal horizontal differential in the fixed throat spatial chart. -/
def programPT06ActualPhysicalThirdJetVectorDensityChartwiseDH
    (density : ProgramPT06ActualPhysicalThirdJetVectorDensity4D) :
    ProgramPT06ActualPhysicalFormalFourthJet4D → Real :=
  programPT06SecondOrderHorizontalCurrentDH
    (programPT06ActualPhysicalThirdJetVectorDensitySpatialCurrent density)

/-- Expansion of the chartwise horizontal differential into its three total
derivatives. -/
@[simp]
theorem programPT06ActualPhysicalThirdJetVectorDensityChartwiseDH_apply
    (density : ProgramPT06ActualPhysicalThirdJetVectorDensity4D)
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D) :
    programPT06ActualPhysicalThirdJetVectorDensityChartwiseDH density jet =
      ∑ direction : Fin 3,
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          ((programPT06ActualPhysicalThirdJetVectorDensitySpatialCurrent
            density) direction) jet :=
  rfl

/-- The physical radial vector density gives exactly Gate925's radial Cartan
current on the formal value-product J3 carrier. -/
theorem
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_spatialCurrent
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    programPT06ActualPhysicalThirdJetVectorDensitySpatialCurrent
        (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
          period hPeriod functional) =
      programPT06T02DegreeFourRadialCartanCurrent
        period hPeriod functional := by
  funext direction jet
  simp [programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity,
    programPT06ActualPhysicalThirdJetVectorDensitySpatialCurrent,
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetCurrent]

/-- Consequently the chartwise physical-vector-density differential is
exactly Gate925's horizontal differential. -/
theorem
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_chartwiseDH
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    programPT06ActualPhysicalThirdJetVectorDensityChartwiseDH
        (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
          period hPeriod functional) =
      programPT06SecondOrderHorizontalCurrentDH
        (programPT06T02DegreeFourRadialCartanCurrent
          period hPeriod functional) := by
  unfold programPT06ActualPhysicalThirdJetVectorDensityChartwiseDH
  rw [programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_spatialCurrent]

/-- A terminal T02 density in the Euler kernel is its constant term plus the
chartwise horizontal differential of its actual physical J3 vector density. -/
theorem
    programPT06T02DegreeFourLocalLagrangian_eq_constant_add_actualPhysicalVectorDensityChartwiseDH
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (hEuler : ∀ jet : ProgramPT06ActualPhysicalFormalFourthJet4D,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet = 0)
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D) :
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) =
      functional.lower.lower.constant +
        programPT06ActualPhysicalThirdJetVectorDensityChartwiseDH
          (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
            period hPeriod functional) jet := by
  rw [programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_chartwiseDH]
  exact
    programPT06T02DegreeFourLocalLagrangian_eq_constant_add_currentDH
      period hPeriod functional hEuler jet

end
end P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityHorizontalDifferential4D
end JanusFormal
