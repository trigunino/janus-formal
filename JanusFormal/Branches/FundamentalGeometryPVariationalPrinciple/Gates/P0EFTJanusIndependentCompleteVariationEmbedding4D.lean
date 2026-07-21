import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonGeometricDomain4D

namespace JanusFormal
namespace P0EFTJanusIndependentCompleteVariationEmbedding4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private def zeroThroatGhost : CInfinityThroatGhost period hPeriod where
  toFun := fun _ => 0
  contMDiff_toFun := Bundle.contMDiff_zeroSection ℝ _

/-- Canonical inclusion of the already-used global independent variation into
the completed D9/D10 tangent content, with only the genuinely new geometric
slots set to zero. -/
def independentCompleteVariation
    (variation : IndependentFieldVariation period hPeriod) :
    ProgramPCompleteVariation4D period hPeriod where
  independent := variation
  normalDisplacement := fun _ => zeroNormalDisplacement period hPeriod
  diffeomorphismGhost := fun _ => zeroThroatGhost period hPeriod
  fullMetricPerturbation := fun _ => zeroSymmetricTensor period hPeriod

@[simp] theorem independentCompleteVariation_independent
    (variation : IndependentFieldVariation period hPeriod) :
    (independentCompleteVariation period hPeriod variation).independent = variation := rfl

theorem independentCompleteVariation_injective :
    Function.Injective (independentCompleteVariation period hPeriod) := by
  intro first second h
  exact congrArg ProgramPCompleteVariation4D.independent h

/-- Forgetting the three completion slots is a left inverse of the canonical
inclusion. -/
theorem independentCompleteVariation_leftInverse :
    Function.LeftInverse ProgramPCompleteVariation4D.independent
      (independentCompleteVariation period hPeriod) := by
  intro variation
  rfl

end
end P0EFTJanusIndependentCompleteVariationEmbedding4D
end JanusFormal
