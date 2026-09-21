import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLogarithmicTraceFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

/-!
Conditional Bismut--Freed bridge on the physical nondegenerate locus.
It reuses the existing Mellin/zeta family and identifies its connection
coefficient with the intrinsic physical logarithmic trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateBismutFreedBridge4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap Topology
open P0EFTJanusCircleDiracHeatTraceCancellation
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
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLogarithmicTraceFrontier4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateLocus4D

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

/-- A physical intrinsic logarithmic trace together with the existing honest
Mellin/zeta family computing the same Bismut--Freed coefficient. -/
structure PhysicalNondegenerateBismutFreedBridgeData
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) where
  traceData : PhysicalNondegenerateLogarithmicTraceData
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity
  zetaFamily : RelativeHeatMellinZetaFamilyData
  coefficient_agreement : ∀ parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector,
    relativeZetaConnectionCoefficient zetaFamily.toZetaFamily parameter.1 =
      PhysicalNondegenerateLogarithmicTraceData.bismutFreedCoefficient
        period hPeriod configuration data analysis chart sameAction physical
          traceData parameter

namespace PhysicalNondegenerateBismutFreedBridgeData

/-- Physical Bismut--Freed connection on a scalar first jet. -/
def connectionAt
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalNondegenerateBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector)
    (value derivative : Complex) : Complex :=
  derivative +
    PhysicalNondegenerateLogarithmicTraceData.bismutFreedCoefficient
      period hPeriod configuration data analysis chart sameAction physical
        bridge.traceData parameter * value

/-- The physical trace connection is the existing zeta connection. -/
theorem connectionAt_eq_zeta
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalNondegenerateBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector)
    (value derivative : Complex) :
    bridge.connectionAt period hPeriod configuration data analysis chart
        sameAction physical parameter value derivative =
      relativeZetaConnectionAt bridge.zetaFamily.toZetaFamily parameter.1
        value derivative := by
  unfold connectionAt relativeZetaConnectionAt
  rw [← bridge.coefficient_agreement parameter]

/-- The physical zeta determinant is parallel for the intrinsic trace
connection. -/
theorem determinant_parallel
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalNondegenerateBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector) :
    bridge.connectionAt period hPeriod configuration data analysis chart
        sameAction physical parameter
        (relativeHeatMellinZetaFamilyDeterminant bridge.zetaFamily parameter.1)
        (relativeZetaDeterminantCoordinateDerivative
          bridge.zetaFamily.toZetaFamily parameter.1) = 0 := by
  rw [bridge.connectionAt_eq_zeta]
  exact relativeZetaDeterminantCoordinate_parallel
    bridge.zetaFamily.toZetaFamily parameter.1

/-- The finite-part logarithmic derivative is the physical intrinsic trace. -/
theorem finitePart_logDerivative_eq_trace
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalNondegenerateBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector) :
    bridge.zetaFamily.finitePartFamily.logDerivative parameter.1 =
      PhysicalNondegenerateLogarithmicTraceData.trace
        period hPeriod configuration data analysis chart sameAction physical
          bridge.traceData parameter := by
  calc
    bridge.zetaFamily.finitePartFamily.logDerivative parameter.1 =
        -(bridge.zetaFamily.parameterDerivative parameter.1).re :=
      bridge.zetaFamily.connection_realPart parameter.1
    _ = -(
        PhysicalNondegenerateLogarithmicTraceData.bismutFreedCoefficient
          period hPeriod configuration data analysis chart sameAction physical
            bridge.traceData parameter).re := by
      exact congrArg (fun value : Complex ↦ -value.re)
        (bridge.coefficient_agreement parameter)
    _ = PhysicalNondegenerateLogarithmicTraceData.trace
        period hPeriod configuration data analysis chart sameAction physical
          bridge.traceData parameter := by
      rw [PhysicalNondegenerateLogarithmicTraceData.bismutFreedCoefficient_re]
      ring

/-- Quillen metric variation expressed by the physical intrinsic trace. -/
theorem metricWeightDerivative_eq_trace
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalNondegenerateBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector) :
    relativeHeatFinitePartMetricWeightDerivative
        bridge.zetaFamily.finitePartFamily parameter.1 =
      2 * PhysicalNondegenerateLogarithmicTraceData.trace
          period hPeriod configuration data analysis chart sameAction physical
            bridge.traceData parameter *
        relativeHeatFinitePartMetricWeight
          bridge.zetaFamily.finitePartFamily parameter.1 := by
  unfold relativeHeatFinitePartMetricWeightDerivative
  rw [bridge.finitePart_logDerivative_eq_trace]

/-- The physical determinant coordinate has the finite-part norm. -/
theorem determinant_norm_eq_finitePart
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalNondegenerateBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector) :
    ‖relativeHeatMellinZetaFamilyDeterminant bridge.zetaFamily parameter.1‖ =
      relativeHeatFinitePartDeterminantFamily
        bridge.zetaFamily.finitePartFamily parameter.1 :=
  norm_relativeHeatMellinZetaFamilyDeterminant bridge.zetaFamily parameter.1

/-- The normalized physical determinant phase is unitary. -/
theorem phase_norm_one
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalNondegenerateBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector) :
    ‖relativeZetaFinitePartPhase bridge.zetaFamily.toFinitePartComparison
        parameter.1‖ = 1 :=
  relativeHeatMellinZetaFamily_phase_norm_one bridge.zetaFamily parameter.1

/-- Public conditional physical Bismut--Freed checkpoint. -/
theorem gate
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalNondegenerateBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity) :
    (∀ parameter : PhysicalNondegenerateParameter
        period hPeriod configuration data analysis chart sameAction physical
          covector,
      bridge.connectionAt period hPeriod configuration data analysis chart
          sameAction physical parameter
          (relativeHeatMellinZetaFamilyDeterminant bridge.zetaFamily parameter.1)
          (relativeZetaDeterminantCoordinateDerivative
            bridge.zetaFamily.toZetaFamily parameter.1) = 0) ∧
    (∀ parameter : PhysicalNondegenerateParameter
        period hPeriod configuration data analysis chart sameAction physical
          covector,
      bridge.zetaFamily.finitePartFamily.logDerivative parameter.1 =
        PhysicalNondegenerateLogarithmicTraceData.trace
          period hPeriod configuration data analysis chart sameAction physical
            bridge.traceData parameter) ∧
    (∀ parameter : PhysicalNondegenerateParameter
        period hPeriod configuration data analysis chart sameAction physical
          covector,
      ‖relativeHeatMellinZetaFamilyDeterminant bridge.zetaFamily parameter.1‖ =
        relativeHeatFinitePartDeterminantFamily
          bridge.zetaFamily.finitePartFamily parameter.1) ∧
    (∀ parameter : PhysicalNondegenerateParameter
        period hPeriod configuration data analysis chart sameAction physical
          covector,
      ‖relativeZetaFinitePartPhase bridge.zetaFamily.toFinitePartComparison
          parameter.1‖ = 1) :=
  ⟨bridge.determinant_parallel,
    bridge.finitePart_logDerivative_eq_trace,
    bridge.determinant_norm_eq_finitePart,
    bridge.phase_norm_one⟩

end PhysicalNondegenerateBismutFreedBridgeData
end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalNondegenerateBismutFreedBridge4D
end JanusFormal
