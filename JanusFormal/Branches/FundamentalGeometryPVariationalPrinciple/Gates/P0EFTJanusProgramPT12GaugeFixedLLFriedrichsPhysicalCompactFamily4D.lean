import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsFredholmIndexFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszCompact4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalSelfAdjointFamily4D

/-!
# Compact physical Friedrichs family packet

The transported physical family has one dense domain, self-adjoint closed
fibres, the proved pointwise parameter derivative, and a compact bounded
perturbation of the reference D11 Fredholm-index family.  No Fredholm claim
is made for the perturbed fibres: that requires a compact-perturbation
stability theorem for the unbounded `LinearPMap` realization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalCompactFamily4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsFredholmIndexFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsGreenDifferentiableFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszCompact4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalSelfAdjointFamily4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D

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

local instance programPT12GaugeFixedLLFriedrichsPhysicalLinearPMapStar
    {configuration : GlobalFieldConfiguration period hPeriod}
    (ι : Type*)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Star
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis →ₗ.[Real]
        ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod ι analysis) :=
  LinearPMap.instStar

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

/-- Typed analytic packet for the physical compact perturbation of the D11
Friedrichs family.  The Fredholm field deliberately concerns only the proved
unperturbed reference family. -/
structure ProgramPT12GaugeFixedLLFriedrichsPhysicalCompactFamilyCertificate4D
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) where
  physicalCommonDomain : ∀ parameter,
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter).domain =
      ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain period hPeriod
        covector couplings.matterMassSquared analysis
  commonDomainDense :
    Dense
      (ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain period hPeriod
        covector couplings.matterMassSquared analysis :
        Set (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
          period hPeriod iota analysis))
  fibreSelfAdjoint : ∀ parameter,
    IsSelfAdjoint
      (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod covector parameter)
  fibreClosed : ∀ parameter,
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter).IsClosed
  fibreApplyHasDerivAt : ∀ parameter
      (state : ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain period hPeriod
        covector couplings.matterMassSquared analysis),
    HasDerivAt
      (fun value ↦
        programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart)
              (sameAction := sameAction) (physical := physical)
                period hPeriod covector value state)
      (programPT12GaugeFixedLLFriedrichsD11VariationOperator
        (iota := iota) period hPeriod analysis parameter state.1)
      parameter
  perturbationCompact :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod)
  referenceFredholmIndexFamily :
    CommonDomainFredholmIndexFamilyData
      (fun parameter : Real ↦
        programPT12GaugeFixedLLFriedrichsD11Operator period hPeriod covector
          couplings.matterMassSquared analysis parameter)

/-- The existing D11 Fredholm family and the compact physical perturbation
assemble into the maximal unconditional analytic packet presently available. -/
def programPT12GaugeFixedLLFriedrichsPhysicalCompactFamily_gate
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    ProgramPT12GaugeFixedLLFriedrichsPhysicalCompactFamilyCertificate4D
      period hPeriod configuration data analysis chart sameAction physical
        covector where
  physicalCommonDomain :=
    programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_domain
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector
  commonDomainDense := by
    simpa only [programPT12GaugeFixedLLFriedrichsD11Operator_domain] using
      (programPT12GaugeFixedLLFriedrichsD11Operator_domain_dense period hPeriod
        covector couplings.matterMassSquared analysis 0)
  fibreSelfAdjoint :=
    programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_selfAdjoint
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector
  fibreClosed :=
    programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_closed
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector
  fibreApplyHasDerivAt :=
    programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_apply_hasDerivAt
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector
  perturbationCompact :=
    programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_compact
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod
  referenceFredholmIndexFamily :=
    programPT12GaugeFixedLLFriedrichsD11FredholmIndexFamily_gate
      period hPeriod d9Ellipticity couplings.matterMassSquared analysis

end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalCompactFamily4D
end JanusFormal
