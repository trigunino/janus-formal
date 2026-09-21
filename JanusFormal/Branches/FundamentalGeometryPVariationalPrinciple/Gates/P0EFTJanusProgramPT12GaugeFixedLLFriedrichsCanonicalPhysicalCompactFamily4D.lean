import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLocus4D

/-!
The canonical reduced Hilbert chart constructs the seven-block physical
extension and specializes the physical T12 Fredholm packet without an
independent extension input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCanonicalPhysicalCompactFamily4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalCompactFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLocus4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section Canonical

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period
  hPeriod (measure := measure) configuration data analysis)
variable (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D
  period hPeriod configuration data analysis chartData)

private abbrev CanonicalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev CanonicalSameAction :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis chartData

private abbrev CanonicalPhysical :=
  globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
    configuration data analysis chartData reducedChart

/-- The canonical reduced chart removes the independent physical-extension
input from the compact Fredholm family packet. -/
structure CanonicalPhysicalCompactFamilyCertificate4D
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) where
  compactFamily :
    ProgramPT12GaugeFixedLLFriedrichsPhysicalCompactFamilyCertificate4D
      period hPeriod configuration data analysis
        (CanonicalChart period hPeriod configuration data analysis chartData)
        (CanonicalSameAction period hPeriod configuration data analysis chartData)
        (CanonicalPhysical period hPeriod configuration data analysis chartData
          reducedChart) covector
  nondegenerateLocusOpen : IsOpen
    (programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet period hPeriod
      configuration data analysis
        (CanonicalChart period hPeriod configuration data analysis chartData)
        (CanonicalSameAction period hPeriod configuration data analysis chartData)
        (CanonicalPhysical period hPeriod configuration data analysis chartData
          reducedChart) covector)

/-- Canonical physical Fredholm/index-zero family with open nondegenerate
locus, constructed from the reduced Hilbert chart. -/
def canonicalPhysicalCompactFamily_gate
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    CanonicalPhysicalCompactFamilyCertificate4D period hPeriod configuration
      data analysis chartData reducedChart covector where
  compactFamily :=
    programPT12GaugeFixedLLFriedrichsPhysicalCompactFamily_gate period hPeriod
      configuration data analysis
        (CanonicalChart period hPeriod configuration data analysis chartData)
        (CanonicalSameAction period hPeriod configuration data analysis chartData)
        (CanonicalPhysical period hPeriod configuration data analysis chartData
          reducedChart) d9Ellipticity
  nondegenerateLocusOpen :=
    programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet_isOpen period
      hPeriod configuration data analysis
        (CanonicalChart period hPeriod configuration data analysis chartData)
        (CanonicalSameAction period hPeriod configuration data analysis chartData)
        (CanonicalPhysical period hPeriod configuration data analysis chartData
          reducedChart) d9Ellipticity

end Canonical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCanonicalPhysicalCompactFamily4D
end JanusFormal
