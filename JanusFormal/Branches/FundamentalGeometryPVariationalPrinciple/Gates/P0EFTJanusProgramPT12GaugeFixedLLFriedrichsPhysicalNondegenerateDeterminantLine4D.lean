import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLocus4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsDeterminantLineFamily4D

/-!
On the open physical nondegenerate locus, every fibre has zero kernel and full
range.  Restriction to that locus therefore gives a constant-defect Fredholm
family and its algebraic determinant line, without asserting that the locus is
nonempty.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateDeterminantLine4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
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
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsDeterminantLineFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsFredholmIndexFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalFredholm4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLocus4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D

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

/-- The physical parameter space restricted to invertible fibres. -/
abbrev ProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateParameter4D
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :=
  programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
    period hPeriod configuration data analysis chart sameAction physical covector

/-- The physical family restricted to the nondegenerate locus has constant
zero kernel and full range. -/
def programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateFredholmIndexFamily
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) :
    CommonDomainFredholmIndexFamilyData
      (fun parameter :
          ProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateParameter4D
            period hPeriod configuration data analysis chart sameAction physical
              covector ↦
        programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data) (analysis := analysis)
            (chart := chart) (sameAction := sameAction) (physical := physical)
              period hPeriod covector parameter.1) where
  domainConstant first second := by
    rw [programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_domain,
      programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_domain]
  fredholm parameter :=
    programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_fredholm
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity parameter.1
  kernelTransport first second :=
    LinearEquiv.ofEq _ _ (by
      rw [LinearMap.ker_eq_bot.mpr first.property.1,
        LinearMap.ker_eq_bot.mpr second.property.1]
      rfl)
  rangeConstant first second := by
    rw [LinearMap.range_eq_top.mpr first.property.2,
      LinearMap.range_eq_top.mpr second.property.2]

/-- Algebraic determinant fibre of the restricted physical family. -/
abbrev ProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateDeterminantLine
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (base parameter :
      ProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateParameter4D
        period hPeriod configuration data analysis chart sameAction physical
          covector) :=
  (programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateFredholmIndexFamily
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity).determinantLine base parameter

/-- The restricted physical determinant line has rank-one fibres and coherent
algebraic transports from any supplied nondegenerate base point. -/
def programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateDeterminantLine_gate
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector)
    (base :
      ProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateParameter4D
        period hPeriod configuration data analysis chart sameAction physical
          covector) :
    CommonDomainFredholmIndexFamilyData.DeterminantLineCertificate
      (programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateFredholmIndexFamily
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity) base :=
  (programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateFredholmIndexFamily
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity).determinantLineCertificate base

end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateDeterminantLine4D
end JanusFormal
