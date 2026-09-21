import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreenDifferentiable4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
Conditional intrinsic logarithmic trace on the physical nondegenerate locus.
The sole new analytic input is nuclearity, with presentation independence, of
the already constructed physical logarithmic derivative on each fibre.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLogarithmicTraceFrontier4D

set_option autoImplicit false
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
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreen4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateGreenDifferentiable4D
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

/-- Parameter subtype on which the physical Hessian is invertible. -/
abbrev PhysicalNondegenerateParameter
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :=
  programPT12GaugeFixedLLFriedrichsPhysicalNondegenerateSet
    period hPeriod configuration data analysis chart sameAction physical covector

/-- Exact remaining fibrewise input for an intrinsic physical logarithmic
trace.  Compactness alone does not construct this datum. -/
structure PhysicalNondegenerateLogarithmicTraceData
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) where
  traceClass : ∀ parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector,
    IntrinsicNuclearTraceData.{_, 0}
      (programPT12GaugeFixedLLFriedrichsFullPhysicalLogarithmicDerivative
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter.1)

namespace PhysicalNondegenerateLogarithmicTraceData

/-- Presentation-independent trace of `R_a A'_a`. -/
def trace
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalNondegenerateLogarithmicTraceData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector) : Real :=
  intrinsicNuclearTrace (input.traceClass parameter)

/-- Bismut--Freed coefficient in the zeta-prime sign convention. -/
def bismutFreedCoefficient
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalNondegenerateLogarithmicTraceData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector) : Complex :=
  (-(trace period hPeriod configuration data analysis chart sameAction physical
      input parameter) : Real)

/-- Every certified nuclear presentation computes the canonical trace. -/
theorem expansionTrace_eq
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalNondegenerateLogarithmicTraceData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector)
    (expansion : SummableRankOneOperatorExpansion.{0}
      (programPT12GaugeFixedLLFriedrichsFullPhysicalLogarithmicDerivative
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter.1)) :
    expansion.expansionTrace =
      trace period hPeriod configuration data analysis chart sameAction physical
        input parameter :=
  (input.traceClass parameter).expansionTrace_eq expansion

/-- Nuclearity strengthens the already proved compactness result. -/
theorem logarithmicDerivative_compact
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalNondegenerateLogarithmicTraceData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector) :
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsFullPhysicalLogarithmicDerivative
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter.1) :=
  (input.traceClass parameter).operator_compact

@[simp]
theorem bismutFreedCoefficient_re
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalNondegenerateLogarithmicTraceData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector) :
    (bismutFreedCoefficient period hPeriod configuration data analysis chart
      sameAction physical input parameter).re =
        -trace period hPeriod configuration data analysis chart sameAction
          physical input parameter := by
  rfl

/-- Public conditional physical logarithmic-trace checkpoint. -/
theorem gate
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (input : PhysicalNondegenerateLogarithmicTraceData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity) :
    (∀ parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector,
      IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsFullPhysicalLogarithmicDerivative
        period hPeriod configuration data analysis chart sameAction physical
          d9Ellipticity parameter.1)) ∧
    (∀ parameter : PhysicalNondegenerateParameter
        period hPeriod configuration data analysis chart sameAction physical
          covector,
      ∀ expansion : SummableRankOneOperatorExpansion.{0}
        (programPT12GaugeFixedLLFriedrichsFullPhysicalLogarithmicDerivative
          period hPeriod configuration data analysis chart sameAction physical
            d9Ellipticity parameter.1),
        expansion.expansionTrace =
          trace period hPeriod configuration data analysis chart sameAction
            physical input parameter) ∧
    (∀ parameter : PhysicalNondegenerateParameter
        period hPeriod configuration data analysis chart sameAction physical
          covector,
      (bismutFreedCoefficient period hPeriod configuration data analysis chart
        sameAction physical input parameter).re =
          -trace period hPeriod configuration data analysis chart sameAction
            physical input parameter) :=
  ⟨logarithmicDerivative_compact period hPeriod configuration data analysis
      chart sameAction physical input,
    expansionTrace_eq period hPeriod configuration data analysis chart
      sameAction physical input,
    bismutFreedCoefficient_re period hPeriod configuration data analysis chart
      sameAction physical input⟩

end PhysicalNondegenerateLogarithmicTraceData
end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLogarithmicTraceFrontier4D
end JanusFormal
