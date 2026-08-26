import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseQuotientDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSetoid4D

/-!
# Set-theoretic dependent descent of throat gauge second jets

This gate packages the pointwise quotients in `Bundle.TotalSpace` and the actual
classes in a set-theoretic section.  It provides no topology, smooth structure,
fiber-bundle structure, or smoothness claim.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetDependentDescent4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseQuotientDescent4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSetoid4D

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

/-! ## Dependent total space and projection -/

/-- The set-theoretic total space of the pointwise quotient carriers.  The
model-fiber parameter prepares the exact Mathlib `Bundle.TotalSpace` API but
does not install a fiber-bundle structure. -/
def ThroatGaugeSecondOrderJetDependentTotalSpace :=
  Bundle.TotalSpace
    (FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates))
    (ThroatGaugeSecondOrderJetPointwiseQuotientFamily period hPeriod)

/-- Projection of the dependent total space to its throat point. -/
def throatGaugeSecondOrderJetDependentProjection :
    ThroatGaugeSecondOrderJetDependentTotalSpace period hPeriod →
      EffectiveThroat period hPeriod :=
  Bundle.TotalSpace.proj

/-- Include a pointwise quotient class in the dependent total space over its point. -/
def throatGaugeSecondOrderJetPointwiseClassInDependentTotalSpace
    (current : EffectiveThroat period hPeriod)
    (jetClass :
      ThroatGaugeSecondOrderJetPointwiseQuotient period hPeriod current) :
    ThroatGaugeSecondOrderJetDependentTotalSpace period hPeriod :=
  ⟨current, jetClass⟩

/-- Package a local presentation as its quotient class in the dependent total space. -/
def throatGaugeSecondOrderJetPresentationInDependentTotalSpace
    (current : EffectiveThroat period hPeriod)
    (presentation :
      ThroatGaugeSecondOrderJetPresentationAt period hPeriod current) :
    ThroatGaugeSecondOrderJetDependentTotalSpace period hPeriod :=
  throatGaugeSecondOrderJetPointwiseClassInDependentTotalSpace
    period hPeriod current
      (throatGaugeSecondOrderJetPresentationClass
        period hPeriod current presentation)

/-! ## Set-theoretic actual section -/

/-- The actual pointwise quotient classes, packaged only as a function into the
dependent total space. -/
def actualThroatGaugeSecondOrderJetDependentSection
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) :
    EffectiveThroat period hPeriod →
      ThroatGaugeSecondOrderJetDependentTotalSpace period hPeriod :=
  fun current =>
    ⟨current,
      actualThroatGaugeSecondOrderJetPointwiseClass
        period hPeriod potential component current⟩

/-- The set-theoretic actual section lies over its input point. -/
theorem actualThroatGaugeSecondOrderJetDependentProjection_section
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (current : EffectiveThroat period hPeriod) :
    throatGaugeSecondOrderJetDependentProjection period hPeriod
        (actualThroatGaugeSecondOrderJetDependentSection
          period hPeriod potential component current) =
      current :=
  rfl

/-- Every valid actual local presentation gives the same element of the
dependent sum as the canonical actual section at that point. -/
theorem actualThroatGaugeSecondOrderJetPresentationInDependentTotalSpace_eq_section
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    throatGaugeSecondOrderJetPresentationInDependentTotalSpace
        period hPeriod current
        (actualThroatGaugeSecondOrderJetPresentationAt period hPeriod potential
          component frameAnchor chartAnchor current hFrame hChart) =
      actualThroatGaugeSecondOrderJetDependentSection
        period hPeriod potential component current := by
  apply Bundle.TotalSpace.ext (by rfl)
  exact heq_of_eq
    (actualThroatGaugeSecondOrderJetPresentationClass_eq_canonical
      period hPeriod potential component frameAnchor chartAnchor current
        hFrame hChart)

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetDependentDescent4D
end JanusFormal
