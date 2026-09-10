import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AffineSecondOrderExactness4D

/-!
# Exactness of the affine T02 subfamily on physical value jets

This gate specializes the affine exactness theorem to the genuine
`ActualPhysicalValueProductFiber`.  It identifies the T02 subfamily whose
quadratic, cubic and quartic coefficients vanish with affine functions on the
genuine Finsupp second jet through the Gate882 continuous linear bridge.

On this explicit T02 subfamily, vanishing of the genuine second-order local
Euler operator is equivalent to being a constant plus the horizontal
divergence of an affine first-order current.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02AffineSecondOrderExactness4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open Set
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
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
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06AffineSecondOrderExactness4D

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

private abbrev FinsuppSecondJet :=
  ThroatSpatialMultiindexJet2 ActualPhysicalValueProductFiber

private abbrev FinsuppFourthJet :=
  ThroatSpatialMultiindexJet4 ActualPhysicalValueProductFiber

local instance actualPhysicalValueProductFiniteDimensional :
    FiniteDimensional Real ActualPhysicalValueProductFiber := by
  let injection :
      ActualPhysicalValueProductFiber →ₗ[Real] FinsuppSecondJet :=
    (programPT06ThroatSpatialJetCoordinateInjection
      (Fiber := ActualPhysicalValueProductFiber)
      programPT06SecondOrderZeroMultiIndex).toLinearMap
  exact FiniteDimensional.of_injective injection (by
    intro first second hEqual
    have hAtZero := congrArg
      (fun jet : FinsuppSecondJet =>
        jet programPT06SecondOrderZeroMultiIndex) hEqual
    simpa [injection] using hAtZero)

variable (period : Real) (hPeriod : period ≠ 0)

/-- The exact T02 subset whose genuinely nonlinear homogeneous coefficients
vanish. -/
def programPT06T02AffineCoefficientSubset :
    Set (ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :=
  { functional |
      functional.lower.lower.quadratic = 0 ∧
      functional.lower.cubic = 0 ∧
      functional.quartic = 0 }

/-- T02 local functionals with only constant and linear coefficients. -/
abbrev ProgramPT06T02AffineLocalFunctional4D :=
  ↑(programPT06T02AffineCoefficientSubset period hPeriod)

/-- Affine Finsupp-second-jet density obtained by pulling the T02 linear
coefficient through Gate882's physical bridge. -/
def programPT06T02AffineSecondOrderLocalDensity
    (functional : ProgramPT06T02AffineLocalFunctional4D period hPeriod) :
    ProgramPT06AffineSecondOrderLocalDensity4D
      (Fiber := ActualPhysicalValueProductFiber) :=
  (functional.1.lower.lower.constant,
    functional.1.lower.lower.linear.1.comp
      programPT06T02FinsuppSecondJetBridge)

/-- On the affine coefficient subset, Gate882's pulled-back T02 evaluation is
exactly the affine density evaluation used by Gate884. -/
@[simp] theorem programPT06T02AffineSecondOrderLocalDensity_evaluation
    (functional : ProgramPT06T02AffineLocalFunctional4D period hPeriod)
    (jet : FinsuppSecondJet) :
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional.1 jet =
      programPT06AffineSecondOrderLocalDensityEvaluation
        (programPT06T02AffineSecondOrderLocalDensity period hPeriod functional)
        jet := by
  have hCoefficients :
      functional.1.lower.lower.quadratic = 0 ∧
      functional.1.lower.cubic = 0 ∧
      functional.1.quartic = 0 :=
    functional.2
  rcases hCoefficients with ⟨hQuadratic, hCubic, hQuartic⟩
  simp [programPT06T02FinsuppSecondJetLocalLagrangian,
    programPT06T02AffineSecondOrderLocalDensity,
    programPT06AffineSecondOrderLocalDensityEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
    actualPhysicalSecondOrderJetInvariantQuadraticEvaluation,
    actualPhysicalSecondOrderJetInvariantCubicEvaluation,
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation,
    hQuadratic, hCubic, hQuartic]

/-- Function-level form of the affine T02 evaluation identification. -/
theorem programPT06T02AffineSecondOrderLocalLagrangian_eq
    (functional : ProgramPT06T02AffineLocalFunctional4D period hPeriod) :
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional.1 =
      programPT06AffineSecondOrderLocalDensityEvaluation
        (programPT06T02AffineSecondOrderLocalDensity period hPeriod functional) := by
  funext jet
  exact programPT06T02AffineSecondOrderLocalDensity_evaluation
    period hPeriod functional jet

private theorem programPT06ActualPhysicalAffineDensityEvaluation_injective
    (first second : ProgramPT06AffineSecondOrderLocalDensity4D
      (Fiber := ActualPhysicalValueProductFiber))
    (hEvaluation :
      ∀ jet : FinsuppSecondJet,
        programPT06AffineSecondOrderLocalDensityEvaluation first jet =
          programPT06AffineSecondOrderLocalDensityEvaluation second jet) :
    first = second := by
  have hConstant : first.1 = second.1 := by
    simpa [programPT06AffineSecondOrderLocalDensityEvaluation] using
      hEvaluation (0 : FinsuppSecondJet)
  apply Prod.ext
  · exact hConstant
  · apply ContinuousLinearMap.ext
    intro jet
    simpa [programPT06AffineSecondOrderLocalDensityEvaluation, hConstant] using
      hEvaluation jet

/-- Range form of Gate884 exactness, specialized to the affine T02 subset. -/
theorem programPT06T02AffineLocalEuler_eq_zero_iff_augmentedDH_range
    (functional : ProgramPT06T02AffineLocalFunctional4D period hPeriod) :
    (∀ jet : FinsuppFourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional.1) jet = 0) ↔
      programPT06T02AffineSecondOrderLocalDensity period hPeriod functional ∈
        LinearMap.range
          (programPT06AffineSecondOrderAugmentedDH
            (Fiber := ActualPhysicalValueProductFiber)) := by
  rw [programPT06T02AffineSecondOrderLocalLagrangian_eq
    period hPeriod functional]
  exact programPT06SecondOrderLocalEuler_affine_eq_zero_iff
    (programPT06T02AffineSecondOrderLocalDensity period hPeriod functional)

/-- Explicit affine T02 classification: Euler vanishes exactly when the
pulled-back T02 density is a constant plus a genuine horizontal divergence. -/
theorem programPT06T02AffineLocalEuler_eq_zero_iff_exists_constant_add_dH
    (functional : ProgramPT06T02AffineLocalFunctional4D period hPeriod) :
    (∀ jet : FinsuppFourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional.1) jet = 0) ↔
      ∃ (constant : Real)
          (current : ProgramPT06LinearFirstOrderHorizontalCurrent4D
            (Fiber := ActualPhysicalValueProductFiber)),
        ∀ jet : FinsuppSecondJet,
          programPT06T02FinsuppSecondJetLocalLagrangian
              period hPeriod functional.1 jet =
            constant +
              programPT06AffineHorizontalCurrentDivergence
                (programPT06LinearCurrentToAffineCurrent current) jet := by
  constructor
  · intro hEuler
    obtain ⟨input, hInput⟩ :=
      (programPT06T02AffineLocalEuler_eq_zero_iff_augmentedDH_range
        period hPeriod functional).1 hEuler
    refine ⟨input.1, input.2, ?_⟩
    intro jet
    rw [programPT06T02AffineSecondOrderLocalDensity_evaluation
      period hPeriod functional jet]
    rw [← hInput]
    exact programPT06AffineSecondOrderAugmentedDH_evaluation input jet
  · rintro ⟨constant, current, hEvaluation⟩
    apply (programPT06T02AffineLocalEuler_eq_zero_iff_augmentedDH_range
      period hPeriod functional).2
    refine ⟨(constant, current), ?_⟩
    apply programPT06ActualPhysicalAffineDensityEvaluation_injective
    intro jet
    calc
      programPT06AffineSecondOrderLocalDensityEvaluation
          (programPT06AffineSecondOrderAugmentedDH
            (Fiber := ActualPhysicalValueProductFiber) (constant, current)) jet =
        constant +
          programPT06AffineHorizontalCurrentDivergence
            (programPT06LinearCurrentToAffineCurrent current) jet :=
          programPT06AffineSecondOrderAugmentedDH_evaluation
            (constant, current) jet
      _ = programPT06T02FinsuppSecondJetLocalLagrangian
            period hPeriod functional.1 jet := (hEvaluation jet).symm
      _ = programPT06AffineSecondOrderLocalDensityEvaluation
            (programPT06T02AffineSecondOrderLocalDensity
              period hPeriod functional) jet :=
          programPT06T02AffineSecondOrderLocalDensity_evaluation
            period hPeriod functional jet

end
end P0EFTJanusProgramPT06T02AffineSecondOrderExactness4D
end JanusFormal
