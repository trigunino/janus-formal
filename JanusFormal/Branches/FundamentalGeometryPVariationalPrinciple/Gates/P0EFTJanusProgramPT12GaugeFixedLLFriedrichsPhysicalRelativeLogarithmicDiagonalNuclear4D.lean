import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSquareSummableDiagonalSandwichNuclearExpansion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPHilbertBasisNuclearRankOneTraceUniqueness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicNuclear4D

/-!
# Diagonal input for the physical relative logarithmic trace

This module connects a fixed ambient Hilbert basis to the generic weighted
nuclear sandwich theorem.  The direct weighted condition ignores blocks on
which the diagonal right factor vanishes.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicDiagonalNuclear4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap Topology
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceExpansionUniqueness4D
open P0EFTJanusProgramPHilbertBasisNuclearRankOneTraceUniqueness4D
open P0EFTJanusProgramPSquareSummableDiagonalSandwichNuclearExpansion4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenDifferentiableFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicFactorization4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicNuclear4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section Physical

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chart : GlobalCandidateALocalVariationalChart period hPeriod
  couplings NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)
variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis chart sameAction)

/-- Fixed-basis weighted nuclear data sufficient to construct every relative
logarithmic sandwich expansion on the physical nondegenerate locus. -/
structure PhysicalRelativeLogarithmicDiagonalNuclearInput4D
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (Mode : Type) where
  basis : HilbertBasis Mode Real
    (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
      period hPeriod iota analysis)
  coefficient :
    PhysicalRelativeNondegenerateParameter period hPeriod configuration data
      analysis chart sameAction physical covector → Mode → Real
  right_on_basis : ∀ (parameter : PhysicalRelativeNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector) mode,
    ((programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
        period hPeriod d9Ellipticity couplings.matterMassSquared analysis
          parameter.1).comp
      (programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter.1)) (basis mode) =
      coefficient parameter mode • basis mode
  weighted_nuclearSummable : ∀ (parameter :
      PhysicalRelativeNondegenerateParameter period hPeriod configuration data
        analysis chart sameAction physical covector),
    Summable (fun mode =>
      |coefficient parameter mode| *
        ‖programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            parameter.1
          (programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicMiddle
            period hPeriod configuration data analysis chart sameAction physical
              d9Ellipticity parameter.1 (basis mode))‖)

namespace PhysicalRelativeLogarithmicDiagonalNuclearInput4D

/-- The fixed-basis diagonal data generate the conditional physical relative
nuclear input. -/
def toNuclearInput
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    {Mode : Type}
    (input : PhysicalRelativeLogarithmicDiagonalNuclearInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity Mode) :
    PhysicalRelativeLogarithmicNuclearInput4D period hPeriod configuration
      data analysis chart sameAction physical d9Ellipticity where
  traceUniqueness :=
    hilbertBasisNuclearRankOneTraceUniquenessData input.basis
  sandwichExpansion := by
    intro parameter
    unfold
      programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicSandwich
    exact summableWeightedDiagonalSandwichExpansion
      (E := ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis)
      (Index := Mode)
      (programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
        period hPeriod d9Ellipticity couplings.matterMassSquared analysis
          parameter.1)
      (programPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicMiddle
        period hPeriod configuration data analysis chart sameAction
          physical d9Ellipticity parameter.1)
      ((programPT12GaugeFixedLLFriedrichsD11StabilizedAmbientInverse
          period hPeriod d9Ellipticity couplings.matterMassSquared analysis
            parameter.1).comp
        (programPT12GaugeFixedLLFriedrichsD11VariationOperator
          (iota := iota) period hPeriod analysis parameter.1))
      input.basis (input.coefficient parameter)
      (input.right_on_basis parameter)
      (input.weighted_nuclearSummable parameter)

/-- Public diagonal-to-nuclear construction checkpoint. -/
theorem diagonalNuclearInput_gate
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    {Mode : Type}
    (input : PhysicalRelativeLogarithmicDiagonalNuclearInput4D
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity Mode) :
    Nonempty
      (PhysicalRelativeLogarithmicNuclearInput4D period hPeriod configuration
        data analysis chart sameAction physical d9Ellipticity) :=
  ⟨input.toNuclearInput period hPeriod configuration data analysis chart
    sameAction physical⟩

end PhysicalRelativeLogarithmicDiagonalNuclearInput4D
end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicDiagonalNuclear4D
end JanusFormal
