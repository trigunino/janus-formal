import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D

/-!
# Primitive SpinC finite core in the global tangent

The finite matter coordinate already used by the diagonal Candidate-A bulk
core is synthesized by the exact signed Fourier--monopole basis.  This file
includes that physical tangent with zero D10 coordinate and records faithful
coordinate recovery and compatibility with the closed matter graph.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASpinCMatterGlobalTangentBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The diagonal-bulk finite SpinC matter coordinate, embedded in the legacy
global tangent with zero D10 component. -/
def globalCandidateABulkMatterGlobalFieldTangentLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      GlobalFieldTangent period hPeriod configuration :=
  (globalPhysicalFieldTangentZeroD10InclusionLinearMap
      period hPeriod).comp
    (globalCandidateABulkMatterPhysicalTangentLinearMap
      period hPeriod configuration)

/-- The global-tangent matter slot is exactly the already constructed smooth
finite synthesis. -/
@[simp]
theorem globalCandidateABulkMatterGlobalFieldTangent_spinCMatter
    (configuration : GlobalFieldConfiguration period hPeriod)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (globalCandidateABulkMatterGlobalFieldTangentLinearMap
        period hPeriod configuration coefficients).spinCMatter
        period hPeriod =
      programPPrimitiveSpinCMatterSmoothFiniteSynthesis
        period hPeriod coefficients :=
  rfl

/-- The bridge introduces no D10 coordinate. -/
@[simp]
theorem globalCandidateABulkMatterGlobalFieldTangent_d10
    (configuration : GlobalFieldConfiguration period hPeriod)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (globalCandidateABulkMatterGlobalFieldTangentLinearMap
        period hPeriod configuration coefficients).d10Coordinates
        period hPeriod = 0 :=
  rfl

/-- Every signed Fourier--monopole coefficient is recovered exactly from the
global matter slot. -/
@[simp]
theorem globalCandidateABulkMatterGlobalFieldTangent_fourierCoordinate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (sector : Sector) (mode : PrimitiveSpinCGeometricSignedMode) :
    (primitiveSpinCGeometricSignedDiracModeUnitary
        period hPeriod).symm
        (d9PrimitiveSpinCGeometricL2Embedding
          period hPeriod .positiveQuarter
          ((globalCandidateABulkMatterGlobalFieldTangentLinearMap
            period hPeriod configuration coefficients).spinCMatter
              period hPeriod sector)) mode =
      coefficients (sector, mode) := by
  rw [globalCandidateABulkMatterGlobalFieldTangent_spinCMatter,
    programPPrimitiveSpinCMatterSmoothFiniteSynthesis_fourierCoordinate]

/-- Hence the finite SpinC bulk coordinate embeds faithfully in the global
tangent. -/
theorem globalCandidateABulkMatterGlobalFieldTangent_injective
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Function.Injective
      (globalCandidateABulkMatterGlobalFieldTangentLinearMap
        period hPeriod configuration) := by
  intro first second hEqual
  apply programPPrimitiveSpinCMatterSmoothFiniteSynthesis_injective
    period hPeriod
  have hMatter := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      tangent.spinCMatter period hPeriod) hEqual
  simpa only [globalCandidateABulkMatterGlobalFieldTangent_spinCMatter]
    using hMatter

/-- Any admissible smooth graph realization sends this global-tangent finite
matter slot to the original diagonal finite graph coordinate. -/
@[simp]
theorem globalCandidateABulkMatterGlobalFieldTangent_toGraph
    (configuration : GlobalFieldConfiguration period hPeriod)
    (massSquared : Real)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod massSquared)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    realization.toGraph
        ((globalCandidateABulkMatterGlobalFieldTangentLinearMap
          period hPeriod configuration coefficients).spinCMatter
            period hPeriod) =
      programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
        period hPeriod massSquared coefficients := by
  change realization.toGraph
      (programPPrimitiveSpinCMatterSmoothFiniteSynthesis
        period hPeriod coefficients) =
    programPPrimitiveSpinCMatterGraphFinite
      period hPeriod massSquared coefficients
  exact realization.finite_compatibility coefficients

end
end P0EFTJanusProgramPGlobalCandidateASpinCMatterGlobalTangentBridge4D
end JanusFormal
