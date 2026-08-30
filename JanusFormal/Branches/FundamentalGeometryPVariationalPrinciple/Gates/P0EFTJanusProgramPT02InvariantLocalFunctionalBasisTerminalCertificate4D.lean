import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D

/-!
# Terminal T02 certificate for bounded invariant local functionals

The admissible class is explicitly bounded to polynomial degree at most four
on the genuine actual-physical second-jet product bundle. Within that bound it
contains every invariant continuous symmetric homogeneous component, rather
than a preselected finite list of scalar expressions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D

local instance t02ActualLLNormedAddCommGroup :
    NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  actualLLNormedAddCommGroup

local instance t02ActualLLNormedSpace :
    NormedSpace Real ActualLLSecondOrderJetFiber :=
  actualLLNormedSpace

local instance t02ActualPhysicalFiniteDimensional :
    FiniteDimensional Real ActualPhysicalSecondOrderJetProductFiber :=
  actualPhysicalFiniteDimensional

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance t02EffectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber

private abbrev Chart :=
  ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod

private abbrev Base := MappingTorus (fixedEquatorData period hPeriod)

/-- The explicitly bounded admissible class used by terminal gate `T02`. -/
abbrev ProgramPT02AdmissibleInvariantLocalFunctional4D :=
  ActualPhysicalSecondOrderJetInvariantDegreeFourFunctional period hPeriod

/-- Complete scalar coordinates for the terminal `T02` admissible class. -/
abbrev ProgramPT02AdmissibleInvariantLocalFunctionalCoefficients4D :=
  ActualPhysicalSecondOrderJetInvariantDegreeFourCoefficients period hPeriod

/-- Concrete terminal `T02` certificate on the actual physical second-jet
bundle. Every field is discharged by an implemented construction. -/
structure ProgramPT02InvariantLocalFunctionalBasisCertificate4D : Prop where
  bundle_smooth :
    (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
      .positiveQuarter).IsContMDiff throatCoverModelWithCorners ∞
  fiber_finiteDimensional : FiniteDimensional Real Fiber
  transition_invariant :
    ∀ (functional : ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
      (first second : Chart period hPeriod) (base : Base period hPeriod),
      base ∈
          (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
            .positiveQuarter).baseSet first ∩
          (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
            .positiveQuarter).baseSet second →
        ∀ jet : Fiber,
          actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
              functional
              ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
                .positiveQuarter).coordChange first second base jet) =
            actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
              functional jet
  evaluation_injective :
    Function.Injective
      (fun functional :
          ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod =>
        actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
          functional)
  synthesis_injective :
    Function.Injective
      (actualPhysicalSecondOrderJetInvariantDegreeFourSynthesis period hPeriod)
  reconstruction :
    ∀ functional : ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod,
      actualPhysicalSecondOrderJetInvariantDegreeFourSynthesis period hPeriod
          (actualPhysicalSecondOrderJetInvariantDegreeFourCoordinates period hPeriod
            functional) = functional
  coefficients_unique :
    ∀ functional : ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod,
      ∃! coefficients :
          ProgramPT02AdmissibleInvariantLocalFunctionalCoefficients4D period hPeriod,
        actualPhysicalSecondOrderJetInvariantDegreeFourSynthesis period hPeriod
            coefficients = functional

/-- Public terminal `T02` theorem for the complete explicitly bounded
degree-at-most-four invariant local-functional class. -/
theorem program_p_t02_invariant_local_functional_basis_terminal_gate :
    ProgramPT02InvariantLocalFunctionalBasisCertificate4D period hPeriod where
  bundle_smooth :=
    actualPhysicalSecondOrderJetProductVectorBundleCore_isContMDiff period hPeriod
      .positiveQuarter
  fiber_finiteDimensional := actualPhysicalFiniteDimensional
  transition_invariant := by
    intro functional first second base hBase jet
    exact actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation_transitionInvariant
      period hPeriod functional first second base hBase jet
  evaluation_injective :=
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation_injective period hPeriod
  synthesis_injective :=
    actualPhysicalSecondOrderJetInvariantDegreeFourSynthesis_injective period hPeriod
  reconstruction :=
    actualPhysicalSecondOrderJetInvariantDegreeFour_reconstruction period hPeriod
  coefficients_unique :=
    actualPhysicalSecondOrderJetInvariantDegreeFour_existsUnique_coefficients
      period hPeriod

end
end P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
end JanusFormal
