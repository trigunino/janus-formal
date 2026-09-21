import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreTopologicalClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCanonicalPhysicalCompactFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateDeterminantLine4D

/-!
The weakest reduced dense-core topological closure constructs the reduced
Hilbert chart and hence the canonical physical T12 compact Fredholm family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCanonicalPhysicalFromTopologicalClosure4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreTopologicalClosure4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCanonicalPhysicalCompactFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateDeterminantLine4D
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

section

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
variable (closure :
  ProgramPGlobalMinimalPhysicalReducedDenseCoreTopologicalClosureData4D
    period hPeriod configuration data analysis chartData)

private abbrev ReducedChart :=
  globalCandidateAMinimalPhysicalReducedHilbertChartOfTopologicalDenseCoreClosure
    period hPeriod configuration data analysis chartData closure

private abbrev CanonicalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev CanonicalSameAction :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis chartData

private abbrev CanonicalPhysical :=
  globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
    configuration data analysis chartData
      (ReducedChart period hPeriod configuration data analysis chartData
        closure)

/-- The weakest topological closure data construct the complete canonical
physical compact-Fredholm packet without a separately supplied chart or
physical extension. -/
def canonicalPhysicalCompactFamily_of_topologicalClosure_gate
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    CanonicalPhysicalCompactFamilyCertificate4D period hPeriod configuration
      data analysis chartData
        (ReducedChart period hPeriod configuration data analysis chartData
          closure)
      covector :=
  canonicalPhysicalCompactFamily_gate period hPeriod configuration data
    analysis chartData
      (ReducedChart period hPeriod configuration data analysis chartData
        closure)
    d9Ellipticity

/-- Every chosen point of the canonical nondegenerate locus carries the
coherent rank-one algebraic determinant-line certificate. -/
def canonicalPhysicalNondegenerateDeterminantLine_of_topologicalClosure_gate
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (base :
      ProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateParameter4D
        period hPeriod configuration data analysis
          (CanonicalChart period hPeriod configuration data analysis chartData)
          (CanonicalSameAction period hPeriod configuration data analysis
            chartData)
          (CanonicalPhysical period hPeriod configuration data analysis
            chartData closure)
          covector) :=
  programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateDeterminantLine_gate
    period hPeriod configuration data analysis
      (CanonicalChart period hPeriod configuration data analysis chartData)
      (CanonicalSameAction period hPeriod configuration data analysis chartData)
      (CanonicalPhysical period hPeriod configuration data analysis chartData
        closure)
      d9Ellipticity base

end
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCanonicalPhysicalFromTopologicalClosure4D
end JanusFormal
