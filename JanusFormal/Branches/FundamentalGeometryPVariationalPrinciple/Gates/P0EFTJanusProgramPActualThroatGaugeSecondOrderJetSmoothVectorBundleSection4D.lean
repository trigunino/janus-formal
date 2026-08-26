import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSmoothVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescentLocalTrivialization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D

/-!
# Smooth descended section of the throat gauge second-jet bundle

The actual local second jets define a global `C∞` section of the smooth
vector bundle constructed from their exact transition laws.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSmoothVectorBundleSection4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescent4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescentLocalTrivialization4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeJet :=
  FramedSecondOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

private abbrev GaugeJetCore :=
  throatGaugeSecondOrderJetVectorBundleCore period hPeriod

private theorem gaugeJetCore_isContMDiff_for_localSectionChart :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D.effectiveThroatChartedSpace
        period hPeriod
    (GaugeJetCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D.effectiveThroatChartedSpace
      period hPeriod
  convert
    throatGaugeSecondOrderJetVectorBundleCore_isContMDiff
      period hPeriod using 1

/-- The descended actual gauge second jet is a global smooth section of the
constructed smooth vector bundle. -/
theorem actualThroatGaugeSecondOrderJetVectorBundleSection_contMDiff
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D.effectiveThroatChartedSpace
        period hPeriod
    letI : (GaugeJetCore period hPeriod).IsContMDiff
        throatCoverModelWithCorners ∞ :=
      gaugeJetCore_isContMDiff_for_localSectionChart period hPeriod
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod 𝓘(Real, GaugeJet)) ∞
      (actualThroatGaugeSecondOrderJetVectorBundleSection
        period hPeriod potential component) := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D.effectiveThroatChartedSpace
      period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
    fixedThroatQuotient_isManifold period hPeriod
  letI : (GaugeJetCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ :=
    gaugeJetCore_isContMDiff_for_localSectionChart period hPeriod
  letI : ChartedSpace (GaugeJet) GaugeJet :=
    TopCat.of.chartedSpace GaugeJet
  intro current
  let index :=
    throatGaugeSecondOrderJetBundleIndexAt period hPeriod current
  let localTriv := (GaugeJetCore period hPeriod).localTriv index
  letI : MemTrivializationAtlas localTriv := ⟨⟨index, rfl⟩⟩
  have hCurrent : current ∈ localTriv.baseSet := by
    change current ∈ throatGaugeSecondOrderJetBundleBaseSet period hPeriod
      index
    exact mem_throatGaugeSecondOrderJetBundleBaseSet_indexAt
      period hPeriod current
  let fiberSection : ∀ current, (GaugeJetCore period hPeriod).Fiber current :=
    fun current ↦
      (actualThroatGaugeSecondOrderJetVectorBundleSection
        period hPeriod potential component current).2
  change ContMDiffAt throatCoverModelWithCorners
    (throatCoverModelWithCorners.prod 𝓘(Real, GaugeJet)) ∞
    (fun nearby ↦ Bundle.TotalSpace.mk' GaugeJet nearby
      (fiberSection nearby)) current
  rw [localTriv.contMDiffAt_section_iff hCurrent]
  have hLocal :=
    actualThroatGaugeSecondOrderJetVectorBundleSection_localCoordinate_contMDiffOn
      period hPeriod potential component index
  have hLocalAt := hLocal.contMDiffAt
    (throatGaugeSecondOrderJetBundleBaseSet_isOpen period hPeriod index
      |>.mem_nhds hCurrent)
  convert hLocalAt using 1 <;> rfl

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSmoothVectorBundleSection4D
end JanusFormal
