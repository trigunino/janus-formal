import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeLogarithmicNuclear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

/-!
# Relative physical Bismut--Freed bridge

This conditional bridge identifies the Mellin/zeta connection coefficient
with the intrinsic trace of the exact physical-minus-D11 logarithmic
derivative on the physical nondegenerate locus.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeBismutFreedBridge4D

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

/-- Nuclear physical-minus-D11 logarithmic trace together with the honest
relative Mellin/zeta family computing the same Bismut--Freed coefficient. -/
structure PhysicalRelativeBismutFreedBridgeData
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector) where
  relativeNuclear : PhysicalRelativeLogarithmicNuclearInput4D
    period hPeriod configuration data analysis chart sameAction physical
      d9Ellipticity
  zetaFamily : RelativeHeatMellinZetaFamilyData
  coefficient_agreement : ∀ parameter : PhysicalRelativeNondegenerateParameter
      period hPeriod configuration data analysis chart sameAction physical
        covector,
    relativeZetaConnectionCoefficient zetaFamily.toZetaFamily parameter.1 =
      relativeNuclear.bismutFreedCoefficient period hPeriod configuration data
        analysis chart sameAction physical parameter

namespace PhysicalRelativeBismutFreedBridgeData

/-- Relative Bismut--Freed connection on a scalar first jet. -/
def connectionAt
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalRelativeBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalRelativeNondegenerateParameter period hPeriod
      configuration data analysis chart sameAction physical covector)
    (value derivative : Complex) : Complex :=
  derivative +
    bridge.relativeNuclear.bismutFreedCoefficient period hPeriod configuration
      data analysis chart sameAction physical parameter * value

/-- The relative physical trace connection is the zeta connection. -/
theorem connectionAt_eq_zeta
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalRelativeBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalRelativeNondegenerateParameter period hPeriod
      configuration data analysis chart sameAction physical covector)
    (value derivative : Complex) :
    bridge.connectionAt period hPeriod configuration data analysis chart
        sameAction physical parameter value derivative =
      relativeZetaConnectionAt bridge.zetaFamily.toZetaFamily parameter.1
        value derivative := by
  unfold connectionAt relativeZetaConnectionAt
  rw [← bridge.coefficient_agreement parameter]

/-- The relative zeta determinant is parallel for the intrinsic
physical-minus-D11 trace connection. -/
theorem determinant_parallel
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalRelativeBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalRelativeNondegenerateParameter period hPeriod
      configuration data analysis chart sameAction physical covector) :
    bridge.connectionAt period hPeriod configuration data analysis chart
        sameAction physical parameter
        (relativeHeatMellinZetaFamilyDeterminant bridge.zetaFamily parameter.1)
        (relativeZetaDeterminantCoordinateDerivative
          bridge.zetaFamily.toZetaFamily parameter.1) = 0 := by
  rw [bridge.connectionAt_eq_zeta]
  exact relativeZetaDeterminantCoordinate_parallel
    bridge.zetaFamily.toZetaFamily parameter.1

/-- The finite-part logarithmic derivative is the intrinsic
physical-minus-D11 logarithmic trace. -/
theorem finitePart_logDerivative_eq_trace
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalRelativeBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalRelativeNondegenerateParameter period hPeriod
      configuration data analysis chart sameAction physical covector) :
    bridge.zetaFamily.finitePartFamily.logDerivative parameter.1 =
      bridge.relativeNuclear.trace period hPeriod configuration data analysis
        chart sameAction physical parameter := by
  calc
    bridge.zetaFamily.finitePartFamily.logDerivative parameter.1 =
        -(bridge.zetaFamily.parameterDerivative parameter.1).re :=
      bridge.zetaFamily.connection_realPart parameter.1
    _ = -(bridge.relativeNuclear.bismutFreedCoefficient period hPeriod
        configuration data analysis chart sameAction physical parameter).re := by
      exact congrArg (fun value : Complex ↦ -value.re)
        (bridge.coefficient_agreement parameter)
    _ = bridge.relativeNuclear.trace period hPeriod configuration data analysis
        chart sameAction physical parameter := by
      rw [PhysicalRelativeLogarithmicNuclearInput4D.bismutFreedCoefficient_re]
      ring

/-- Relative Quillen metric variation expressed by the intrinsic trace. -/
theorem metricWeightDerivative_eq_trace
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalRelativeBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalRelativeNondegenerateParameter period hPeriod
      configuration data analysis chart sameAction physical covector) :
    relativeHeatFinitePartMetricWeightDerivative
        bridge.zetaFamily.finitePartFamily parameter.1 =
      2 * bridge.relativeNuclear.trace period hPeriod configuration data
          analysis chart sameAction physical parameter *
        relativeHeatFinitePartMetricWeight
          bridge.zetaFamily.finitePartFamily parameter.1 := by
  unfold relativeHeatFinitePartMetricWeightDerivative
  rw [bridge.finitePart_logDerivative_eq_trace]

/-- The relative determinant coordinate has the finite-part norm. -/
theorem determinant_norm_eq_finitePart
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalRelativeBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalRelativeNondegenerateParameter period hPeriod
      configuration data analysis chart sameAction physical covector) :
    ‖relativeHeatMellinZetaFamilyDeterminant bridge.zetaFamily parameter.1‖ =
      relativeHeatFinitePartDeterminantFamily
        bridge.zetaFamily.finitePartFamily parameter.1 :=
  norm_relativeHeatMellinZetaFamilyDeterminant bridge.zetaFamily parameter.1

/-- The normalized relative determinant phase is unitary. -/
theorem phase_norm_one
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalRelativeBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity)
    (parameter : PhysicalRelativeNondegenerateParameter period hPeriod
      configuration data analysis chart sameAction physical covector) :
    ‖relativeZetaFinitePartPhase bridge.zetaFamily.toFinitePartComparison
        parameter.1‖ = 1 :=
  relativeHeatMellinZetaFamily_phase_norm_one bridge.zetaFamily parameter.1

/-- Public conditional relative physical Bismut--Freed checkpoint. -/
theorem gate
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    {d9Ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector}
    (bridge : PhysicalRelativeBismutFreedBridgeData
      period hPeriod configuration data analysis chart sameAction physical
        d9Ellipticity) :
    (∀ parameter : PhysicalRelativeNondegenerateParameter period hPeriod
        configuration data analysis chart sameAction physical covector,
      bridge.connectionAt period hPeriod configuration data analysis chart
          sameAction physical parameter
          (relativeHeatMellinZetaFamilyDeterminant bridge.zetaFamily parameter.1)
          (relativeZetaDeterminantCoordinateDerivative
            bridge.zetaFamily.toZetaFamily parameter.1) = 0) ∧
    (∀ parameter : PhysicalRelativeNondegenerateParameter period hPeriod
        configuration data analysis chart sameAction physical covector,
      bridge.zetaFamily.finitePartFamily.logDerivative parameter.1 =
        bridge.relativeNuclear.trace period hPeriod configuration data analysis
          chart sameAction physical parameter) ∧
    (∀ parameter : PhysicalRelativeNondegenerateParameter period hPeriod
        configuration data analysis chart sameAction physical covector,
      ‖relativeHeatMellinZetaFamilyDeterminant bridge.zetaFamily parameter.1‖ =
        relativeHeatFinitePartDeterminantFamily
          bridge.zetaFamily.finitePartFamily parameter.1) ∧
    (∀ parameter : PhysicalRelativeNondegenerateParameter period hPeriod
        configuration data analysis chart sameAction physical covector,
      ‖relativeZetaFinitePartPhase bridge.zetaFamily.toFinitePartComparison
          parameter.1‖ = 1) :=
  ⟨bridge.determinant_parallel,
    bridge.finitePart_logDerivative_eq_trace,
    bridge.determinant_norm_eq_finitePart,
    bridge.phase_norm_one⟩

end PhysicalRelativeBismutFreedBridgeData
end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRelativeBismutFreedBridge4D
end JanusFormal
