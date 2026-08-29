import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectReflexivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSymmetry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectTransitivity4D

/-!
# Direct setoid of local throat gauge second-jet presentations

The direct value, Jacobian and Hessian transition law is an equivalence
relation.  Consequently its generated equivalence closure adds no pairs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSetoid4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectReflexivity4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSymmetry4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectTransitivity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Direct equivalence and setoid -/

/-- Direct transition compatibility is an equivalence relation. -/
theorem directTransitionCompatible_equivalence
    (current : EffectiveThroat period hPeriod) :
    Equivalence
      (fun first second :
        ThroatGaugeSecondOrderJetPresentationAt period hPeriod current =>
          DirectTransitionCompatible period hPeriod first second) := by
  constructor
  · exact directTransitionCompatible_refl period hPeriod
  · intro first second hDirect
    exact directTransitionCompatible_symm period hPeriod hDirect
  · intro first second third hFirstSecond hSecondThird
    exact directTransitionCompatible_trans period hPeriod
      hFirstSecond hSecondThird

/-- Setoid defined by the direct transition law itself. -/
def throatGaugeSecondOrderJetPresentationDirectSetoid
    (current : EffectiveThroat period hPeriod) :
    Setoid (ThroatGaugeSecondOrderJetPresentationAt period hPeriod current) where
  r := DirectTransitionCompatible period hPeriod
  iseqv := directTransitionCompatible_equivalence period hPeriod current

/-! ## Collapse of the generated closure -/

/-- The generated equivalence closure contains no compatibility beyond the
direct transition law. -/
theorem generatedTransitionRelation_directCompatible
    {current : EffectiveThroat period hPeriod}
    {first second :
      ThroatGaugeSecondOrderJetPresentationAt period hPeriod current}
    (hGenerated :
      GeneratedTransitionRelation period hPeriod first second) :
    DirectTransitionCompatible period hPeriod first second := by
  induction hGenerated with
  | rel first second hDirect => exact hDirect
  | refl presentation =>
      exact directTransitionCompatible_refl period hPeriod presentation
  | symm first second _ hDirect =>
      exact directTransitionCompatible_symm period hPeriod hDirect
  | trans first second third _ _ hFirstSecond hSecondThird =>
      exact directTransitionCompatible_trans period hPeriod
        hFirstSecond hSecondThird

/-- Direct compatibility and its generated equivalence closure coincide. -/
theorem directTransitionCompatible_iff_generatedTransitionRelation
    {current : EffectiveThroat period hPeriod}
    {first second :
      ThroatGaugeSecondOrderJetPresentationAt period hPeriod current} :
    DirectTransitionCompatible period hPeriod first second ↔
      GeneratedTransitionRelation period hPeriod first second :=
  ⟨directCompatible_generated period hPeriod,
    generatedTransitionRelation_directCompatible period hPeriod⟩

/-- The formerly generated setoid is exactly the direct setoid. -/
theorem throatGaugeSecondOrderJetPresentationGeneratedSetoid_eq_directSetoid
    (current : EffectiveThroat period hPeriod) :
    throatGaugeSecondOrderJetPresentationGeneratedSetoid
        period hPeriod current =
      throatGaugeSecondOrderJetPresentationDirectSetoid
        period hPeriod current := by
  apply Setoid.ext
  intro first second
  exact
    (directTransitionCompatible_iff_generatedTransitionRelation
      period hPeriod (first := first) (second := second)).symm

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSetoid4D
end JanusFormal
