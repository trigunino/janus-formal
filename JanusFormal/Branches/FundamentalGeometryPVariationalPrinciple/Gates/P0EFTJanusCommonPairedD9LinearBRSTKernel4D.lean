import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonPairedD9LinearBRSTBlock4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeGlobalZeroMode4D

/-! # Exact kernel of the common paired D9 linear BRST block -/

namespace JanusFormal
namespace P0EFTJanusCommonPairedD9LinearBRSTKernel4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeGlobalZeroMode4D
open P0EFTJanusCommonPairedD9LinearBRSTBlock4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Exact kernel of the linear block.  The two input gauge potentials and the
input diffeomorphism ghost are deliberately absent from the right-hand side:
they are unrestricted because this linear differential does not inspect them.
This is a kernel statement, not a complete BRST-cohomology computation. -/
theorem commonPairedD9LinearBRSTDifferential_eq_zero_iff
    (state : CommonPairedD9LinearBRSTBlock period hPeriod) :
    commonPairedD9LinearBRSTDifferential period hPeriod state =
        zeroCommonPairedD9LinearBRSTBlock period hPeriod ↔
      (∃ firstValue : GaugeLieAlgebra,
        ∀ point : EffectiveQuotient period hPeriod,
          state.firstU1.ghost point = firstValue) ∧
      (∃ secondValue : GaugeLieAlgebra,
        ∀ point : EffectiveQuotient period hPeriod,
          state.secondU1.ghost point = secondValue) := by
  constructor
  · intro hKernel
    have hFirstState := congrArg CommonPairedD9LinearBRSTBlock.firstU1 hKernel
    have hSecondState := congrArg CommonPairedD9LinearBRSTBlock.secondU1 hKernel
    have hFirstPotential := congrArg AbelianBRSTState.potential hFirstState
    have hSecondPotential := congrArg AbelianBRSTState.potential hSecondState
    have hFirstExact :
        exactGaugePotential period hPeriod state.firstU1.ghost = 0 := by
      exact hFirstPotential
    have hSecondExact :
        exactGaugePotential period hPeriod state.secondU1.ghost = 0 := by
      exact hSecondPotential
    exact ⟨
      (exactGaugePotential_eq_zero_iff_exists_constant period hPeriod
        state.firstU1.ghost).mp hFirstExact,
      (exactGaugePotential_eq_zero_iff_exists_constant period hPeriod
        state.secondU1.ghost).mp hSecondExact⟩
  · rintro ⟨hFirst, hSecond⟩
    apply CommonPairedD9LinearBRSTBlock.ext
    · apply AbelianBRSTState.ext
      · exact (exactGaugePotential_eq_zero_iff_exists_constant period hPeriod
          state.firstU1.ghost).mpr hFirst
      · rfl
    · apply AbelianBRSTState.ext
      · exact (exactGaugePotential_eq_zero_iff_exists_constant period hPeriod
          state.secondU1.ghost).mpr hSecond
      · rfl
    · rfl

end

end P0EFTJanusCommonPairedD9LinearBRSTKernel4D
end JanusFormal
