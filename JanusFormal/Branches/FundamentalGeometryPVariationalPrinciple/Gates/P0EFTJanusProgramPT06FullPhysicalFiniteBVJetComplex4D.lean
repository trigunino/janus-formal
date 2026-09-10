import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06FiniteMetricBVAffineExactComplex4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D

/-!
# Full physical value carrier with a finite metric-BV jet complex

This gate places the complete eleven-component T02 value fiber and the
nonzero finite metric-BV phase in one normed finite-dimensional local carrier.
The physical fiber embeds as the zero-BV summand, every T02 degree-four local
density pulls back to this enlarged second-jet carrier, and the finite BV
differential prolongs coefficientwise through the jet tower.

The resulting square-zero differential commutes with the affine horizontal
differential and Euler map, and the affine null-density sequence stays exact.
Only the finite metric-BV summand carries a nontrivial differential here; this
does not yet construct the full nonlinear BV action on all physical fields.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06FullPhysicalFiniteBVJetComplex4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06AffineSecondOrderExactness4D
open P0EFTJanusProgramPT06AffineSecondOrderBRSTNaturality4D
open P0EFTJanusProgramPT06FiniteMetricBVAffineExactComplex4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional

private abbrev PhysicalValueFiber := ActualPhysicalValueProductFiber

local instance physicalValueFiberFiniteDimensional :
    FiniteDimensional Real PhysicalValueFiber :=
  FiniteDimensional.of_injective
    (programPT06ThroatSpatialJetCoordinateInjection
      (Fiber := PhysicalValueFiber)
      programPT06SecondOrderZeroMultiIndex).toLinearMap
    (by
      intro first second hEqual
      simpa using congrArg
        (fun jet => jet programPT06SecondOrderZeroMultiIndex) hEqual)

/-- One local fiber containing all eleven physical value components and the
finite metric-BV phase. -/
abbrev ProgramPT06FullPhysicalFiniteBVFiber4D :=
  PhysicalValueFiber × FiniteMetricBVPhase

/-- The complete physical value fiber embeds as the zero-BV summand. -/
def programPT06FullPhysicalFiniteBVPhysicalInclusion :
    PhysicalValueFiber →L[Real] ProgramPT06FullPhysicalFiniteBVFiber4D :=
  (ContinuousLinearMap.id Real PhysicalValueFiber).prod
    (0 : PhysicalValueFiber →L[Real] FiniteMetricBVPhase)

/-- Projection back to the eleven-component physical value fiber. -/
def programPT06FullPhysicalFiniteBVPhysicalProjection :
    ProgramPT06FullPhysicalFiniteBVFiber4D →L[Real] PhysicalValueFiber :=
  ContinuousLinearMap.fst Real PhysicalValueFiber FiniteMetricBVPhase

@[simp] theorem programPT06FullPhysicalFiniteBVPhysicalProjection_inclusion
    (value : PhysicalValueFiber) :
    programPT06FullPhysicalFiniteBVPhysicalProjection
        (programPT06FullPhysicalFiniteBVPhysicalInclusion value) = value :=
  rfl

/-- Coefficientwise inclusion of complete physical jets. -/
def programPT06FullPhysicalFiniteBVPhysicalJetInclusion (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet PhysicalValueFiber order) :
    TruncatedThroatSpatialMultiindexJet
      ProgramPT06FullPhysicalFiniteBVFiber4D order :=
  fun index => (jet index, 0)

/-- Coefficientwise projection from the enlarged jet tower. -/
def programPT06FullPhysicalFiniteBVPhysicalJetProjection (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet
      ProgramPT06FullPhysicalFiniteBVFiber4D order) :
    TruncatedThroatSpatialMultiindexJet PhysicalValueFiber order :=
  fun index => (jet index).1

@[simp] theorem programPT06FullPhysicalFiniteBVPhysicalJetProjection_inclusion
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet PhysicalValueFiber order) :
    programPT06FullPhysicalFiniteBVPhysicalJetProjection order
        (programPT06FullPhysicalFiniteBVPhysicalJetInclusion order jet) = jet := by
  rfl

/-- Every terminal T02 density is a local function on the common enlarged
second-jet carrier by pullback along the physical projection. -/
def programPT06FullPhysicalFiniteBVT02LocalLagrangian
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    ThroatSpatialMultiindexJet2 ProgramPT06FullPhysicalFiniteBVFiber4D → Real :=
  programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional ∘
    programPT06FullPhysicalFiniteBVPhysicalJetProjection 2

/-- Pulling an enlarged T02 density back to the physical summand recovers the
original eleven-component T02 local Lagrangian exactly. -/
@[simp] theorem programPT06FullPhysicalFiniteBVT02LocalLagrangian_inclusion
    (period : Real) (hPeriod : period ≠ 0)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : ThroatSpatialMultiindexJet2 PhysicalValueFiber) :
    programPT06FullPhysicalFiniteBVT02LocalLagrangian period hPeriod functional
        (programPT06FullPhysicalFiniteBVPhysicalJetInclusion 2 jet) =
      programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
        jet := by
  change programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
      (programPT06FullPhysicalFiniteBVPhysicalJetProjection 2
        (programPT06FullPhysicalFiniteBVPhysicalJetInclusion 2 jet)) = _
  rw [programPT06FullPhysicalFiniteBVPhysicalJetProjection_inclusion]

/-- Square-zero BV differential on the common fiber: zero on the complete
physical value summand and the existing nontrivial differential on the finite
metric-BV summand. -/
def programPT06FullPhysicalFiniteBVContinuousBRST :
    ProgramPT06FullPhysicalFiniteBVFiber4D →L[Real]
      ProgramPT06FullPhysicalFiniteBVFiber4D :=
  (0 : ProgramPT06FullPhysicalFiniteBVFiber4D →L[Real] PhysicalValueFiber).prod
    (programPT06FiniteMetricBVContinuousBRST.comp
      (ContinuousLinearMap.snd Real PhysicalValueFiber FiniteMetricBVPhase))

@[simp] theorem programPT06FullPhysicalFiniteBVContinuousBRST_apply
    (state : ProgramPT06FullPhysicalFiniteBVFiber4D) :
    programPT06FullPhysicalFiniteBVContinuousBRST state =
      (0, finiteMetricBVBRST state.2) :=
  rfl

theorem programPT06FullPhysicalFiniteBVContinuousBRST_square_zero
    (state : ProgramPT06FullPhysicalFiniteBVFiber4D) :
    programPT06FullPhysicalFiniteBVContinuousBRST
        (programPT06FullPhysicalFiniteBVContinuousBRST state) = 0 := by
  apply Prod.ext
  · rfl
  · exact finiteMetricBVBRST_square_zero state.2

/-- The common physical/BV fiber supplies the generic square-zero differential
used by the affine variational complex. -/
def programPT06FullPhysicalFiniteBVSquareZeroDifferential :
    ProgramPT06SquareZeroContinuousFiberDifferential4D
      (Fiber := ProgramPT06FullPhysicalFiniteBVFiber4D) where
  differential := programPT06FullPhysicalFiniteBVContinuousBRST
  square_zero := programPT06FullPhysicalFiniteBVContinuousBRST_square_zero

/-- The BV differential annihilates the embedded eleven-component physical
summand. -/
@[simp] theorem programPT06FullPhysicalFiniteBVContinuousBRST_inclusion
    (value : PhysicalValueFiber) :
    programPT06FullPhysicalFiniteBVContinuousBRST
        (programPT06FullPhysicalFiniteBVPhysicalInclusion value) = 0 := by
  simp [programPT06FullPhysicalFiniteBVContinuousBRST,
    programPT06FullPhysicalFiniteBVPhysicalInclusion]

/-- Its jet prolongation annihilates every embedded physical jet. -/
@[simp] theorem programPT06FullPhysicalFiniteBVJetBRST_inclusion
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet PhysicalValueFiber order) :
    programPT06ContinuousFiberDifferentialJetProlongation
        programPT06FullPhysicalFiniteBVSquareZeroDifferential order
        (programPT06FullPhysicalFiniteBVPhysicalJetInclusion order jet) = 0 := by
  funext index
  simp [programPT06FullPhysicalFiniteBVSquareZeroDifferential,
    programPT06FullPhysicalFiniteBVPhysicalJetInclusion]

/-- The affine horizontal differential is natural under the common-carrier
BV differential. -/
theorem programPT06FullPhysicalFiniteBVBRST_commutes_augmentedDH
    (input : Real × ProgramPT06LinearFirstOrderHorizontalCurrent4D
      (Fiber := ProgramPT06FullPhysicalFiniteBVFiber4D)) :
    programPT06AffineSecondOrderDensityBRST
        programPT06FullPhysicalFiniteBVSquareZeroDifferential
        (programPT06AffineSecondOrderAugmentedDH
          (Fiber := ProgramPT06FullPhysicalFiniteBVFiber4D) input) =
      programPT06AffineSecondOrderAugmentedDH
        (Fiber := ProgramPT06FullPhysicalFiniteBVFiber4D)
        (0, programPT06AffineSecondOrderCurrentBRST
          programPT06FullPhysicalFiniteBVSquareZeroDifferential input.2) :=
  programPT06AffineSecondOrderBRST_commutes_augmentedDH
    programPT06FullPhysicalFiniteBVSquareZeroDifferential input

/-- The affine Euler map is natural under the common-carrier BV differential. -/
theorem programPT06FullPhysicalFiniteBVLocalEuler_BRST_natural
    (density : ProgramPT06AffineSecondOrderLocalDensity4D
      (Fiber := ProgramPT06FullPhysicalFiniteBVFiber4D)) :
    programPT06AffineSecondOrderLocalEuler
        (Fiber := ProgramPT06FullPhysicalFiniteBVFiber4D)
        (programPT06AffineSecondOrderDensityBRST
          programPT06FullPhysicalFiniteBVSquareZeroDifferential density) =
      (programPT06AffineSecondOrderLocalEuler
        (Fiber := ProgramPT06FullPhysicalFiniteBVFiber4D) density).comp
          programPT06FullPhysicalFiniteBVContinuousBRST :=
  programPT06AffineSecondOrderLocalEuler_BRST_natural
    programPT06FullPhysicalFiniteBVSquareZeroDifferential density

/-- Exact affine null-density classification on the same carrier containing
all eleven physical values and the finite metric-BV phase. -/
theorem programPT06FullPhysicalFiniteBV_affineEuler_ker_eq_augmentedDH_range :
    LinearMap.ker
        (programPT06AffineSecondOrderLocalEuler
          (Fiber := ProgramPT06FullPhysicalFiniteBVFiber4D)) =
      LinearMap.range
        (programPT06AffineSecondOrderAugmentedDH
          (Fiber := ProgramPT06FullPhysicalFiniteBVFiber4D)) :=
  programPT06_affineSecondOrderLocalEuler_ker_eq_augmentedDH_range
    (Fiber := ProgramPT06FullPhysicalFiniteBVFiber4D)

end
end P0EFTJanusProgramPT06FullPhysicalFiniteBVJetComplex4D
end JanusFormal
