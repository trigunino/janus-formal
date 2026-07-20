import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalRealPowerZeroOverZeroClassification4D

/-!
# Functional diagonal paths at a zero-over-zero face

For arbitrary scalar numerator and denominator paths, the selected diagonal
root is classified by the limit of their ratio.  This is exact on the diagonal
family and does not classify genuinely matrix-valued paths.
-/

namespace JanusFormal
namespace P0EFTJanusGlobalDiagonalFunctionalZeroOverZeroClassification4D

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusGlobalDiagonalRootFrontierControl4D
open P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D

abbrev CoefficientPair :=
  P0EFTJanusGlobalDiagonalLorentzRoot4D.CoefficientPair

def functionalZeroOverZeroPath
    (point : CoefficientPair) (i : Fin 4)
    (numerator denominator : Real → Real) (t : Real) : CoefficientPair :=
  (replaceMagnitude point.1 i (denominator t),
    replaceMagnitude point.2 i (numerator t))

theorem functionalZeroOverZeroPath_mem_globalDomain
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) (numerator denominator : Real → Real) {t : Real}
    (hNumerator : 0 < numerator t) (hDenominator : 0 < denominator t) :
    functionalZeroOverZeroPath point i numerator denominator t ∈
      globalDiagonalLorentzDomain := by
  constructor <;> intro j
  · by_cases hji : j = i
    · subst j
      simpa [functionalZeroOverZeroPath, replaceMagnitude] using hDenominator
    · simpa [functionalZeroOverZeroPath, replaceMagnitude, hji] using hPoint.1 j
  · by_cases hji : j = i
    · subst j
      simpa [functionalZeroOverZeroPath, replaceMagnitude] using hNumerator
    · simpa [functionalZeroOverZeroPath, replaceMagnitude, hji] using hPoint.2 j

theorem functionalZeroOverZeroPath_tendsto_common_boundary
    {filter : Filter Real} (point : CoefficientPair) (i : Fin 4)
    (numerator denominator : Real → Real)
    (hNumerator : Tendsto numerator filter (nhds 0))
    (hDenominator : Tendsto denominator filter (nhds 0)) :
    Tendsto (functionalZeroOverZeroPath point i numerator denominator)
      filter (nhds (equalRateZeroOverZeroPath point i 0)) := by
  have hFirst : Tendsto
      (fun t => replaceMagnitude point.1 i (denominator t)) filter
      (nhds (replaceMagnitude point.1 i 0)) :=
    ((plusCoordinateApproach_continuous point i).fst.tendsto 0).comp hDenominator
  have hSecond : Tendsto
      (fun t => replaceMagnitude point.2 i (numerator t)) filter
      (nhds (replaceMagnitude point.2 i 0)) :=
    ((minusCoordinateApproach_continuous point i).snd.tendsto 0).comp hNumerator
  change Tendsto
    (fun t => (replaceMagnitude point.1 i (denominator t),
      replaceMagnitude point.2 i (numerator t))) filter
    (nhds (replaceMagnitude point.1 i 0, replaceMagnitude point.2 i 0))
  exact hFirst.prodMk_nhds hSecond

@[simp] theorem functionalZeroOverZeroPath_root_eq
    (point : CoefficientPair) (i : Fin 4)
    (numerator denominator : Real → Real) (t : Real) :
    principalRootSpectrum
        (functionalZeroOverZeroPath point i numerator denominator t) i =
      Real.sqrt (numerator t / denominator t) := by
  simp [principalRootSpectrum, relativeRatio, functionalZeroOverZeroPath,
    replaceMagnitude]

theorem functionalZeroOverZeroPath_root_tendsto_of_ratio
    {filter : Filter Real} (point : CoefficientPair) (i : Fin 4)
    (numerator denominator : Real → Real) (ratio : Real)
    (hRatio : Tendsto (fun t => numerator t / denominator t)
      filter (nhds ratio)) :
    Tendsto
      (fun t => principalRootSpectrum
        (functionalZeroOverZeroPath point i numerator denominator t) i)
      filter (nhds (Real.sqrt ratio)) := by
  simpa only [functionalZeroOverZeroPath_root_eq, Function.comp_def] using
    Real.continuous_sqrt.tendsto ratio |>.comp hRatio

theorem functionalZeroOverZeroPath_root_tendsto_atTop_of_ratio
    {filter : Filter Real} (point : CoefficientPair) (i : Fin 4)
    (numerator denominator : Real → Real)
    (hRatio : Tendsto (fun t => numerator t / denominator t)
      filter atTop) :
    Tendsto
      (fun t => principalRootSpectrum
        (functionalZeroOverZeroPath point i numerator denominator t) i)
      filter atTop := by
  simpa only [functionalZeroOverZeroPath_root_eq, Function.comp_def] using
    Real.tendsto_sqrt_atTop.comp hRatio

end

end P0EFTJanusGlobalDiagonalFunctionalZeroOverZeroClassification4D
end JanusFormal
