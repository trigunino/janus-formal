import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D

/-!
# Pointwise quotient of local throat gauge second-jet presentations

This gate forms only the pointwise quotient by the generated presentation
setoid.  It makes no smooth bundle or global smooth-section claim.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseQuotientDescent4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeDifferentiatedOverlap4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D

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

/-! ## Pointwise generated quotient -/

/-- The quotient at one throat point by the generated local-presentation
equivalence relation. -/
def ThroatGaugeSecondOrderJetPointwiseQuotient
    (current : EffectiveThroat period hPeriod) :=
  Quotient
    (throatGaugeSecondOrderJetPresentationGeneratedSetoid
      period hPeriod current)

/-- The quotient class represented by one local presentation. -/
def throatGaugeSecondOrderJetPresentationClass
    (current : EffectiveThroat period hPeriod)
    (presentation :
      ThroatGaugeSecondOrderJetPresentationAt period hPeriod current) :
    ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current :=
  Quotient.mk _ presentation

/-! ## Canonical actual representative and descent -/

/-- The actual second jet presented in the frame and chart both centered at
the point itself. -/
def canonicalActualThroatGaugeSecondOrderJetPresentationAt
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (current : EffectiveThroat period hPeriod) :
    ThroatGaugeSecondOrderJetPresentationAt period hPeriod current :=
  actualThroatGaugeSecondOrderJetPresentationAt period hPeriod potential
    component current current current
      (FiberBundle.mem_baseSet_trivializationAt' current)
      (mem_extChartAt_source current)

/-- The canonical pointwise quotient class of the actual extracted jet. -/
def actualThroatGaugeSecondOrderJetPointwiseClass
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (current : EffectiveThroat period hPeriod) :
    ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current :=
  throatGaugeSecondOrderJetPresentationClass period hPeriod current
    (canonicalActualThroatGaugeSecondOrderJetPresentationAt
      period hPeriod potential component current)

/-- Every valid actual local presentation represents the canonical pointwise
class. -/
theorem actualThroatGaugeSecondOrderJetPresentationClass_eq_canonical
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    throatGaugeSecondOrderJetPresentationClass period hPeriod current
        (actualThroatGaugeSecondOrderJetPresentationAt period hPeriod potential
          component frameAnchor chartAnchor current hFrame hChart) =
      actualThroatGaugeSecondOrderJetPointwiseClass period hPeriod potential
        component current := by
  apply Quotient.sound
  exact actualThroatGaugeSecondOrderJetPresentationAt_generatedRelated
    period hPeriod potential component frameAnchor current chartAnchor current
      current
      ⟨hFrame, FiberBundle.mem_baseSet_trivializationAt' current⟩
      hChart (mem_extChartAt_source current)

/-- The family of pointwise quotient carriers over the throat. -/
def ThroatGaugeSecondOrderJetPointwiseQuotientFamily
    (current : EffectiveThroat period hPeriod) :=
  ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseQuotientDescent4D
end JanusFormal
