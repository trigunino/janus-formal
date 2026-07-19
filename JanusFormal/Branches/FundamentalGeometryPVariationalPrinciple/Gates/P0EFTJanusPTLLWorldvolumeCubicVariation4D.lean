import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D

/-! The exact cubic world-volume coefficient on a PT orbit. -/

namespace JanusFormal
namespace P0EFTJanusPTLLWorldvolumeCubicVariation4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

def ptLLWorldvolumeCubicCoefficient (variation : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) *
    (llThirdVariationCoefficient period hPeriod variation p +
      llThirdVariationCoefficient period hPeriod variation
        (fixedThroatPT period hPeriod p))

theorem ptLLWorldvolumeCubicCoefficient_formula (variation : LLVariation period hPeriod)
    (p : EffectiveThroat period hPeriod) :
    ptLLWorldvolumeCubicCoefficient period hPeriod variation p =
      (1 / 2 : Real) *
        (variation.measureDirection p * ‖variation.fieldDirection p‖ ^ 2 +
          variation.measureDirection (fixedThroatPT period hPeriod p) *
            ‖variation.fieldDirection (fixedThroatPT period hPeriod p)‖ ^ 2) := by
  rfl

theorem ptLLWorldvolumeCubicCoefficient_continuous (variation : LLVariation period hPeriod) :
    Continuous (ptLLWorldvolumeCubicCoefficient period hPeriod variation) := by
  exact continuous_const.mul
    ((llThirdVariationCoefficient_continuous period hPeriod variation).add
      ((llThirdVariationCoefficient_continuous period hPeriod variation).comp
        (continuous_fixedThroatPT period hPeriod)))

theorem ptLLWorldvolumeCubicCoefficient_integrable (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptLLWorldvolumeCubicCoefficient period hPeriod variation) mu :=
  (ptLLWorldvolumeCubicCoefficient_continuous period hPeriod variation).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def globalPTLLWorldvolumeCubicCoefficient (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ p, ptLLWorldvolumeCubicCoefficient period hPeriod variation p ∂mu

def globalPTLLWorldvolumeThirdDiagonalVariation (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  6 * globalPTLLWorldvolumeCubicCoefficient period hPeriod variation mu

theorem globalPTLLWorldvolumeThirdDiagonalVariation_formula
    (variation : LLVariation period hPeriod) (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTLLWorldvolumeThirdDiagonalVariation period hPeriod variation mu =
      Nat.factorial 3 * globalPTLLWorldvolumeCubicCoefficient period hPeriod variation mu := by
  norm_num [globalPTLLWorldvolumeThirdDiagonalVariation]

theorem cubicTerm_iteratedDeriv_three
    (variation : LLVariation period hPeriod) (mu : Measure (EffectiveThroat period hPeriod)) :
    iteratedDeriv 3
        (fun t : Real => t ^ 3 * globalPTLLWorldvolumeCubicCoefficient period hPeriod variation mu) 0 =
      globalPTLLWorldvolumeThirdDiagonalVariation period hPeriod variation mu := by
  rw [show (fun t : Real => t ^ 3 * globalPTLLWorldvolumeCubicCoefficient period hPeriod variation mu) =
      fun t : Real => globalPTLLWorldvolumeCubicCoefficient period hPeriod variation mu * t ^ 3 by
        funext t; ring]
  rw [iteratedDeriv_const_mul (n := 3) _ (by fun_prop)]
  rw [iteratedDeriv_pow]
  norm_num [globalPTLLWorldvolumeThirdDiagonalVariation]
  ring

end
end P0EFTJanusPTLLWorldvolumeCubicVariation4D
end JanusFormal
