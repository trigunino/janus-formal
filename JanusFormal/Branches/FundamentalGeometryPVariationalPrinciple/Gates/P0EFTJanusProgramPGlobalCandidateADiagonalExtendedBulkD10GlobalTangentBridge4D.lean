import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkD10SpineL2Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalyticSpine4D

/-!
# Shared D10 factor of the Candidate-A completion and global tangent

Only the already common D10 coefficient Hilbert space is compared.  The bulk
completion is deliberately discarded: no realization of its coordinates as a
genuine global field tangent is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkD10GlobalTangentBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkD10SpineL2Bridge4D
open P0EFTJanusProgramPGlobalAnalyticSpine4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Linear D10 coordinate of the Candidate-A direct-sum completion. -/
def globalCandidateADiagonalExtendedBulkD10CoordinateLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod data
        analysis →ₗ[Real]
      ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod configuration.d10Completion) where
  toFun := globalCandidateADiagonalExtendedBulkD10Coordinate period hPeriod
    data analysis
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem globalCandidateADiagonalExtendedBulkD10CoordinateLinearMap_section
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : ProgramPD10ModeHilbert4D
      (d10SpectralData period hPeriod configuration.d10Completion)) :
    globalCandidateADiagonalExtendedBulkD10CoordinateLinearMap period hPeriod
        data analysis
        (globalCandidateADiagonalExtendedBulkD10Section period hPeriod data
          analysis state) =
      state := by
  change
    globalCandidateADiagonalExtendedBulkD10Coordinate period hPeriod data
        analysis
        (globalCandidateADiagonalExtendedBulkD10Section period hPeriod data
          analysis state) = state
  exact globalCandidateADiagonalExtendedBulkD10Coordinate_section period
    hPeriod data analysis state

/-- Projection of the Candidate-A completion onto the pure-D10 subspace of
the genuine global tangent. -/
def globalCandidateADiagonalExtendedBulkD10ToGlobalFieldTangentLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod data
        analysis →ₗ[Real]
      GlobalFieldTangent period hPeriod configuration :=
  (globalFieldTangentD10SectionLinearMap period hPeriod).comp
    (globalCandidateADiagonalExtendedBulkD10CoordinateLinearMap period hPeriod
      data analysis)

/-- The bridge preserves the D10 coordinate exactly. -/
@[simp]
theorem globalCandidateADiagonalExtendedBulkD10ToGlobalFieldTangent_coordinate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state :
      GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod data
        analysis) :
    globalFieldTangentD10CoordinateLinearMap period hPeriod
        (globalCandidateADiagonalExtendedBulkD10ToGlobalFieldTangentLinearMap
          period hPeriod data analysis state) =
      globalCandidateADiagonalExtendedBulkD10CoordinateLinearMap period hPeriod
        data analysis state := by
  simp [globalCandidateADiagonalExtendedBulkD10ToGlobalFieldTangentLinearMap]

/-- On a pure D10 state, the bridge is exactly the canonical global-tangent
section. -/
@[simp]
theorem globalCandidateADiagonalExtendedBulkD10ToGlobalFieldTangent_section
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : ProgramPD10ModeHilbert4D
      (d10SpectralData period hPeriod configuration.d10Completion)) :
    globalCandidateADiagonalExtendedBulkD10ToGlobalFieldTangentLinearMap
        period hPeriod data analysis
        (globalCandidateADiagonalExtendedBulkD10Section period hPeriod data
          analysis state) =
      globalFieldTangentD10SectionLinearMap period hPeriod state := by
  simp [globalCandidateADiagonalExtendedBulkD10ToGlobalFieldTangentLinearMap]

/-- Hence the Candidate-A-to-global-tangent bridge is injective on its pure
D10 section. -/
theorem globalCandidateADiagonalExtendedBulkD10ToGlobalFieldTangent_section_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (fun state : ProgramPD10ModeHilbert4D
          (d10SpectralData period hPeriod configuration.d10Completion) =>
        globalCandidateADiagonalExtendedBulkD10ToGlobalFieldTangentLinearMap
          period hPeriod data analysis
          (globalCandidateADiagonalExtendedBulkD10Section period hPeriod data
            analysis state)) := by
  simpa only
    [globalCandidateADiagonalExtendedBulkD10ToGlobalFieldTangent_section]
    using
      (globalFieldTangentD10Section_injective period hPeriod
        (configuration := configuration))

end
end P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkD10GlobalTangentBridge4D
end JanusFormal
