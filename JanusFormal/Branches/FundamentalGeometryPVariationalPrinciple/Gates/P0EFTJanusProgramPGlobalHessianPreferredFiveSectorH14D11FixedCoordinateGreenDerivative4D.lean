import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryFrameKernelComplementTrivialization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableSelfAdjointGreenFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11UnitaryFredholmGreenClosure4D

/-!
# Fixed-coordinate H14 Green derivative from the D11 unitary frame

The concrete H14--D11 closure supplies a unitary frame of the genuine moving
kernel complements.  Restricting the frame and pulling every reduced operator
back to `(ker H_0)ᗮ` gives a literally constant operator family.  Its canonical
Green family is therefore constant as well.

This file packages that fixed-coordinate family in the pre-existing
`DifferentiableSelfAdjointUniformGapFamilyData` interface and derives the Green
differentiability packet with

```text
H'_fixed = 0,
G'_fixed = 0 = -G_fixed H'_fixed G_fixed.
```

Thus the ordinary inverse derivative formula is closed in the canonical unitary
coordinates.  Any nonzero geometric connection coefficient must come from the
moving D11 frame, not from a second choice of reduced operators.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11FixedCoordinateGreenDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 152000000
set_option synthInstance.maxHeartbeats 76000000
noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D
open P0EFTJanusProgramPFiniteUnitaryFrameKernelComplementTrivialization4D
open P0EFTJanusProgramPDifferentiableSelfAdjointGreenFamily4D
open P0EFTJanusProgramPSelfAdjointKernelComplementFamilyTrivialization4D
open P0EFTJanusProgramPSelfAdjointUniformGapFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14BasepointFredholmGreenAdapter4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11UnitaryFredholmGreenClosure4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

private abbrev CandidateAHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) candidateAHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}

private abbrev ActualOperator
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  input.familyIndex.baseFamily.actualOperator

private abbrev ActualSelfAdjoint
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  input.familyIndex.baseFamily.familyIndex.actual_selfAdjoint

private abbrev FrameData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :=
  (d11Unitary.toUnitaryAmbientFrame period hPeriod input natural).frameData

/-- The D11 frame expressed in the old fixed-complement uniform-gap interface. -/
def fixedComplementGapFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    SelfAdjointKernelComplementUniformGapTrivializationData
      (ActualOperator period hPeriod input)
      (ActualSelfAdjoint period hPeriod input) :=
  (FrameData period hPeriod input natural d11Unitary).
    toKernelComplementUniformGapTrivialization
      (ActualSelfAdjoint period hPeriod input)
      (h14BasepointGap period hPeriod input)

/-- The fixed reduced operator family has zero derivative. -/
def differentiableFixedReducedFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    DifferentiableSelfAdjointUniformGapFamilyData
      (fixedComplementGapFamily period hPeriod input natural d11Unitary).
        fixedOperator where
  analytic :=
    (fixedComplementGapFamily period hPeriod input natural d11Unitary).
      toUniformGapFamily
  derivative := fun _ => 0
  hasDerivAt_operator := by
    intro parameter
    exact (FrameData period hPeriod input natural d11Unitary).
      hasDerivAt_fixedOperator_zero (ActualSelfAdjoint period hPeriod input)
        (h14BasepointGap period hPeriod input) parameter

/-- The canonical inverse of the fixed reduced family is independent of the
parameter. -/
theorem fixedGreen_eq_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural)
    (parameter : Real) :
    (differentiableFixedReducedFamily period hPeriod input natural d11Unitary).
        analytic.green parameter =
      (differentiableFixedReducedFamily period hPeriod input natural d11Unitary).
        analytic.green 0 := by
  let familyData :=
    differentiableFixedReducedFamily period hPeriod input natural d11Unitary
  apply ContinuousLinearMap.ext
  intro vector
  apply (familyData.analytic.bijective parameter).1
  rw [familyData.analytic.operator_green parameter]
  have hParameter :=
    (FrameData period hPeriod input natural d11Unitary).
      fixedOperator_eq_basepoint (ActualSelfAdjoint period hPeriod input)
        (h14BasepointGap period hPeriod input) parameter
  have hZero :=
    (FrameData period hPeriod input natural d11Unitary).
      fixedOperator_eq_basepoint (ActualSelfAdjoint period hPeriod input)
        (h14BasepointGap period hPeriod input) 0
  change familyData.analytic.operator parameter
      (familyData.analytic.green 0 vector) = vector
  rw [hParameter, ← hZero]
  exact familyData.analytic.operator_green 0 vector

/-- Green differentiability is forced by constancy; its derivative is zero and
satisfies the canonical inverse formula. -/
def fixedGreenDifferentiability
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    (differentiableFixedReducedFamily period hPeriod input natural d11Unitary).
      GreenDifferentiabilityData where
  greenDerivative := fun _ => 0
  hasDerivAt_green := by
    intro parameter
    convert hasDerivAt_const parameter
      ((differentiableFixedReducedFamily period hPeriod input natural d11Unitary).
        analytic.green 0) using 1
    funext current
    exact fixedGreen_eq_zero period hPeriod input natural d11Unitary current
  greenDerivative_eq := by
    intro parameter
    simp [DifferentiableSelfAdjointUniformGapFamilyData.canonicalGreenDerivative,
      differentiableFixedReducedFamily]

/-- Public fixed-coordinate derivative checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_fixed_coordinate_green_derivative_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    let reduced :=
      differentiableFixedReducedFamily period hPeriod input natural d11Unitary
    let inverse :=
      fixedGreenDifferentiability period hPeriod input natural d11Unitary
    (∀ parameter,
      HasDerivAt reduced.analytic.operator 0 parameter) ∧
    (∀ parameter,
      HasDerivAt reduced.analytic.green 0 parameter) ∧
    (∀ parameter,
      inverse.greenDerivative parameter =
        -((reduced.analytic.green parameter).comp
          ((reduced.derivative parameter).comp
            (reduced.analytic.green parameter)))) ∧
    (∀ parameter,
      ‖reduced.analytic.green parameter‖ ≤ reduced.analytic.gap⁻¹) := by
  dsimp only
  let reduced :=
    differentiableFixedReducedFamily period hPeriod input natural d11Unitary
  let inverse :=
    fixedGreenDifferentiability period hPeriod input natural d11Unitary
  exact
    ⟨reduced.hasDerivAt_operator,
      fun parameter => by
        simpa using inverse.hasDerivAt_green parameter,
      inverse.derivative_formula,
      reduced.analytic.green_opNorm_le⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11FixedCoordinateGreenDerivative4D
end JanusFormal
