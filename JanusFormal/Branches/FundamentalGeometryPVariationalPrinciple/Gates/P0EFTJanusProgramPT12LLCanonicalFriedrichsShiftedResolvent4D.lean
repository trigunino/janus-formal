import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D

/-!
# Compact shifted resolvents of the canonical LL Friedrichs realization

Every nonnegative shift of the canonical Friedrichs operator is bijective.
Its inverse on the ambient LL `L2` space is the already constructed compact
weak solution operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalFriedrichsShiftedResolvent4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPT12HilbertEnergyShift4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakSolution4D
open P0EFTJanusProgramPT12LLCanonicalThroatRellichCompactness4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl
local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private theorem energyShiftL2Solution_eq_of_adjoint_value
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (I : V →L[Real] H) (shift : Real) (hShift : 0 ≤ shift)
    (x y : H) (hValue : I (I.adjoint y) = x) :
    energyShiftL2Solution I shift hShift (y + shift • x) = x := by
  have hSolution : I.adjoint y =
      energyShiftSolution I shift hShift (y + shift • x) := by
    apply energyShiftSolution_unique
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left, hValue,
      inner_add_left, real_inner_smul_left]
  exact Eq.trans (congrArg I hSolution.symm) hValue

/-- The weak shifted solution is also a left inverse on the Friedrichs domain. -/
theorem canonicalLLFriedrichsShiftedWeak_left_inverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (field : (canonicalLLFriedrichsJacobi period hPeriod analysis).domain) :
    canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift
        (canonicalLLFriedrichsShiftedJacobi period hPeriod analysis shift field) =
      (field : CanonicalLLL2 period hPeriod analysis) := by
  let I := canonicalLLH1ToFluxL2 period hPeriod analysis
  let A := canonicalLLFriedrichsJacobi period hPeriod analysis
  have hValue : I (I.adjoint (A field)) =
      (field : CanonicalLLL2 period hPeriod analysis) := by
    change canonicalLLWeakL2Inverse period hPeriod analysis (A field) = _
    exact canonicalLLWeakL2Inverse_friedrichsJacobi
      period hPeriod analysis field
  rw [canonicalLLFriedrichsShiftedJacobi_apply]
  exact energyShiftL2Solution_eq_of_adjoint_value I shift hShift
    (field : CanonicalLLL2 period hPeriod analysis) (A field) hValue

theorem canonicalLLFriedrichsShiftedJacobi_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift) :
    Function.Injective
      (canonicalLLFriedrichsShiftedJacobi period hPeriod analysis shift) := by
  intro first second hEqual
  apply Subtype.ext
  rw [← canonicalLLFriedrichsShiftedWeak_left_inverse period hPeriod analysis
      shift hShift first,
    ← canonicalLLFriedrichsShiftedWeak_left_inverse period hPeriod analysis
      shift hShift second,
    hEqual]

theorem canonicalLLFriedrichsShiftedJacobi_bijective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift) :
    Function.Bijective
      (canonicalLLFriedrichsShiftedJacobi period hPeriod analysis shift) :=
  ⟨canonicalLLFriedrichsShiftedJacobi_injective period hPeriod analysis
      shift hShift,
    canonicalLLFriedrichsShiftedJacobi_surjective period hPeriod analysis
      shift hShift⟩

/-- The ambient resolvent of the nonnegative shifted Friedrichs operator. -/
def canonicalLLFriedrichsShiftedResolvent
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift) :
    CanonicalLLL2 period hPeriod analysis →L[Real]
      CanonicalLLL2 period hPeriod analysis :=
  canonicalLLShiftedWeakL2Solution period hPeriod analysis shift hShift

theorem canonicalLLFriedrichsShiftedResolvent_compact
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift) :
    IsCompactOperator
      (canonicalLLFriedrichsShiftedResolvent period hPeriod analysis
        shift hShift) := by
  exact canonicalLLShiftedWeakL2Solution_compact_of_rellich
    period hPeriod analysis
      (canonicalLLH1ToFluxL2_isCompact period hPeriod analysis)
      shift hShift

theorem canonicalLLFriedrichsShiftedResolvent_right_inverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (source : CanonicalLLL2 period hPeriod analysis) :
    canonicalLLFriedrichsShiftedJacobi period hPeriod analysis shift
        (canonicalLLFriedrichsShiftedWeakDomainElement period hPeriod analysis
          shift hShift source) = source :=
  canonicalLLFriedrichsShiftedJacobi_right_inverse period hPeriod analysis
    shift hShift source

theorem canonicalLLFriedrichsShiftedResolvent_left_inverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (shift : Real) (hShift : 0 ≤ shift)
    (field : (canonicalLLFriedrichsJacobi period hPeriod analysis).domain) :
    canonicalLLFriedrichsShiftedResolvent period hPeriod analysis shift hShift
        (canonicalLLFriedrichsShiftedJacobi period hPeriod analysis shift field) =
      (field : CanonicalLLL2 period hPeriod analysis) :=
  canonicalLLFriedrichsShiftedWeak_left_inverse period hPeriod analysis
    shift hShift field

end
end P0EFTJanusProgramPT12LLCanonicalFriedrichsShiftedResolvent4D
end JanusFormal
