import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalVariationalCohomology4D

/-!
# Invariant second-jet null-density classification for T06

The carrier is the independently defined T02 class of all transition-invariant
polynomial functions of degree at most four on the actual physical second-jet
fiber.  Inside this bounded class, zero vertical Fréchet derivative is
equivalent to the unique constant representative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06InvariantJetNullDensityClassification4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 900000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuadraticFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeTwoFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantCubicFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeThreeFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuarticFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPGlobalVariationalCohomology4D

local instance t06ActualLLNormedAddCommGroup :
    NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  actualLLNormedAddCommGroup

local instance t06ActualLLNormedSpace :
    NormedSpace Real ActualLLSecondOrderJetFiber :=
  actualLLNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber

private abbrev LocalDensity :=
  ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod

private abbrev Chart :=
  ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod

private abbrev Base := MappingTorus (fixedEquatorData period hPeriod)

/-- Evaluation of an admissible local density on the actual physical
second-jet fiber. -/
def programPT06InvariantJetDensityEvaluation
    (density : LocalDensity period hPeriod) : Fiber → Real :=
  actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod density

/-- The canonical constant member of the independently classified T02
admissible class. -/
def programPT06ConstantInvariantJetDensity
    (constant : Real) : LocalDensity period hPeriod where
  lower :=
    { lower :=
        { constant := constant
          linear := 0
          quadratic := 0 }
      cubic := 0 }
  quartic := 0

@[simp] theorem programPT06ConstantInvariantJetDensity_evaluation
    (constant : Real) (jet : Fiber) :
    programPT06InvariantJetDensityEvaluation period hPeriod
        (programPT06ConstantInvariantJetDensity period hPeriod constant) jet =
      constant := by
  simp [programPT06InvariantJetDensityEvaluation,
    programPT06ConstantInvariantJetDensity,
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
    actualPhysicalSecondOrderJetInvariantQuadraticEvaluation,
    actualPhysicalSecondOrderJetInvariantCubicEvaluation,
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation]

/-- Actual vertical nullity of a local density is zero Fréchet derivative of
its polynomial evaluation at every physical second jet. -/
def IsInvariantJetVariationallyNull
    (density : LocalDensity period hPeriod) : Prop :=
  VariationallyNull
    (programPT06InvariantJetDensityEvaluation period hPeriod density)

/-- Every T02 density still descends through all genuine transition maps. -/
theorem programPT06InvariantJetDensity_transitionInvariant
    (density : LocalDensity period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : Fiber) :
    programPT06InvariantJetDensityEvaluation period hPeriod density
        ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).coordChange first second base jet) =
      programPT06InvariantJetDensityEvaluation period hPeriod density jet :=
  actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation_transitionInvariant
    period hPeriod density first second base hBase jet

/-- Complete bounded local null-density classification: the only
transition-invariant degree-at-most-four densities with zero vertical
variation are the unique constant representatives. -/
theorem invariantJetVariationallyNull_iff_existsUnique_constant
    (density : LocalDensity period hPeriod) :
    IsInvariantJetVariationallyNull period hPeriod density ↔
      ∃! constant : Real,
        density =
          programPT06ConstantInvariantJetDensity period hPeriod constant := by
  constructor
  · intro hNull
    obtain ⟨constant, hConstant⟩ :=
      (variationallyNull_iff_exists_constant
        (programPT06InvariantJetDensityEvaluation period hPeriod density)).1
        hNull
    have hDensity : density =
        programPT06ConstantInvariantJetDensity period hPeriod constant := by
      apply actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation_injective
        period hPeriod
      funext jet
      change programPT06InvariantJetDensityEvaluation period hPeriod density jet =
        programPT06InvariantJetDensityEvaluation period hPeriod
          (programPT06ConstantInvariantJetDensity period hPeriod constant) jet
      rw [hConstant jet]
      exact (programPT06ConstantInvariantJetDensity_evaluation
        period hPeriod constant jet).symm
    refine ⟨constant, hDensity, ?_⟩
    intro other hOther
    have hAtZero := congrArg
      (fun candidate : LocalDensity period hPeriod =>
        programPT06InvariantJetDensityEvaluation period hPeriod candidate
          (0 : Fiber))
      (hDensity.symm.trans hOther)
    simpa using hAtZero.symm
  · rintro ⟨constant, hDensity, _⟩
    subst density
    apply (variationallyNull_iff_exists_constant
      (programPT06InvariantJetDensityEvaluation period hPeriod
        (programPT06ConstantInvariantJetDensity period hPeriod constant))).2
    exact ⟨constant,
      programPT06ConstantInvariantJetDensity_evaluation period hPeriod constant⟩

end

end P0EFTJanusProgramPT06InvariantJetNullDensityClassification4D
end JanusFormal
