import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPZeroActualBismutFreedFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11FixedCoordinateGreenDerivative4D

/-!
# Candidate-A Bismut--Freed base family from H14 and the D11 frame

The existing preferred family already fixes

* the Candidate-A actual operator family;
* the intrinsic Quillen atlas;
* the selected reference operator and its intrinsic logarithmic trace;
* the relative Mellin/zeta family and its circle normalization.

Its older family-index field also supplied an independent actual-complement
trivialization, differentiability packet, inverse derivative and one nuclear
certificate at every parameter.

This file rebuilds that base family using instead

* the concrete H14 gap and Green;
* the operator-norm differentiable unitary D11 frame;
* one intrinsic nuclear certificate for the zero operator.

In the D11 fixed coordinates the actual logarithmic trace is zero.  Therefore
the only remaining coefficient comparison is

```text
relative zeta connection coefficient = reference logarithmic trace.
```

All Quillen, reference, zeta and circle data are retained exactly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11ReferenceTraceBismutFreedFamily4D

set_option autoImplicit false
set_option maxHeartbeats 176000000
set_option synthInstance.maxHeartbeats 88000000
noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPSelfAdjointKernelComplementBismutFreedFamily4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPZeroActualBismutFreedFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11FixedCoordinateGreenDerivative4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusCircleDiracHeatTraceCancellation

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelNormedSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelModule
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelCompleteSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedAddCommGroup
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertInnerProductSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertModule
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertCompleteSpace

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

variable {measure : Measure (EffectiveQuotient period hPeriod)}

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
      (measure := measure) period hPeriod configuration data analysis
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
    {Metric Abelian Matter Longitudinal Boundary : Type}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}

private abbrev OldBaseFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  input.familyIndex.baseFamily

private abbrev BaseReduced
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  SelfAdjointKernelComplement
    ((OldBaseFamily period hPeriod input).actualOperator 0)

private abbrev D11Frame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural) :=
  frame.toD11UnitaryAdmissibleIsomorphismFrame period hPeriod input natural

/-- Rebuilt family-index packet with D11/H14 actual data and the unchanged
reference/zeta side. -/
def rebuiltFamilyIndex
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input))
    (referenceCoefficientAgreement : ∀ parameter,
      relativeZetaConnectionCoefficient
          (OldBaseFamily period hPeriod input).familyIndex.zetaFamily.toZetaFamily
          parameter =
        ((OldBaseFamily period hPeriod input).familyIndex.referenceTrace.trace
          parameter : Real)) :
    SelfAdjointKernelComplementBismutFreedFamilyData
      (OldBaseFamily period hPeriod input).actualOperator
      (OldBaseFamily period hPeriod input).referenceOperator :=
  selfAdjointKernelComplementBismutFreedFamilyOfZeroActualDerivative
    (OldBaseFamily period hPeriod input).familyIndex.actual_selfAdjoint
    (fixedComplementGapFamily period hPeriod input natural
      (D11Frame period hPeriod input natural frame))
    (differentiableFixedReducedFamily period hPeriod input natural
      (D11Frame period hPeriod input natural frame))
    rfl
    (fixedGreenDifferentiability period hPeriod input natural
      (D11Frame period hPeriod input natural frame))
    (fun _ => rfl)
    zeroTrace
    (OldBaseFamily period hPeriod input).familyIndex.referenceTrace
    (OldBaseFamily period hPeriod input).familyIndex.zetaFamily
    referenceCoefficientAgreement

/-- Preferred Bismut--Freed base family rebuilt without independent actual-side
family data. -/
def rebuiltBismutFreedFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input))
    (referenceCoefficientAgreement : ∀ parameter,
      relativeZetaConnectionCoefficient
          (OldBaseFamily period hPeriod input).familyIndex.zetaFamily.toZetaFamily
          parameter =
        ((OldBaseFamily period hPeriod input).familyIndex.referenceTrace.trace
          parameter : Real)) :
    GlobalHessianPreferredFiveSectorBismutFreedFamily4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index where
  quillen := (OldBaseFamily period hPeriod input).quillen
  actualOperator := (OldBaseFamily period hPeriod input).actualOperator
  actual_zero := (OldBaseFamily period hPeriod input).actual_zero
  referenceOperator := (OldBaseFamily period hPeriod input).referenceOperator
  familyIndex := rebuiltFamilyIndex period hPeriod input natural frame zeroTrace
    referenceCoefficientAgreement
  zetaFamily_eq := (OldBaseFamily period hPeriod input).zetaFamily_eq
  coefficient_eq_circle := by
    intro parameter
    let newIndex := rebuiltFamilyIndex period hPeriod input natural frame zeroTrace
      referenceCoefficientAgreement
    calc
      newIndex.toBismutFreed.operatorTrace.bismutFreedCoefficient parameter =
          ((OldBaseFamily period hPeriod input).familyIndex.referenceTrace.trace
            parameter : Real) := by
        exact SelfAdjointKernelComplementBismutFreedFamilyData.zeroActualDerivative_bismutFreedCoefficient
            (OldBaseFamily period hPeriod input).familyIndex.actual_selfAdjoint
            (fixedComplementGapFamily period hPeriod input natural
              (D11Frame period hPeriod input natural frame))
            (differentiableFixedReducedFamily period hPeriod input natural
              (D11Frame period hPeriod input natural frame))
            rfl
            (fixedGreenDifferentiability period hPeriod input natural
              (D11Frame period hPeriod input natural frame))
            (fun _ => rfl) zeroTrace
            (OldBaseFamily period hPeriod input).familyIndex.referenceTrace
            (OldBaseFamily period hPeriod input).familyIndex.zetaFamily
            referenceCoefficientAgreement parameter
      _ = relativeZetaConnectionCoefficient
          (OldBaseFamily period hPeriod input).familyIndex.zetaFamily.toZetaFamily
          parameter := (referenceCoefficientAgreement parameter).symm
      _ = ((OldBaseFamily period hPeriod input).familyIndex.toBismutFreed
          |>.operatorTrace.bismutFreedCoefficient parameter) :=
        ((OldBaseFamily period hPeriod input).familyIndex.toBismutFreed
          |>.coefficient_agreement parameter)
      _ = (circleQuillenConnectionCoefficient fold : Complex) :=
        (OldBaseFamily period hPeriod input).coefficient_eq_circle parameter

/-- The rebuilt actual logarithmic trace is identically zero. -/
theorem rebuiltBismutFreedFamily_actualTrace_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input))
    (referenceCoefficientAgreement : ∀ parameter,
      relativeZetaConnectionCoefficient
          (OldBaseFamily period hPeriod input).familyIndex.zetaFamily.toZetaFamily
          parameter =
        ((OldBaseFamily period hPeriod input).familyIndex.referenceTrace.trace
          parameter : Real))
    (parameter : Real) :
    (rebuiltBismutFreedFamily period hPeriod input natural frame zeroTrace
      referenceCoefficientAgreement).familyIndex.actualTrace.trace parameter = 0 := by
  exact SelfAdjointKernelComplementBismutFreedFamilyData.zeroActualDerivative_actualTrace
    (OldBaseFamily period hPeriod input).familyIndex.actual_selfAdjoint
    (fixedComplementGapFamily period hPeriod input natural
      (D11Frame period hPeriod input natural frame))
    (differentiableFixedReducedFamily period hPeriod input natural
      (D11Frame period hPeriod input natural frame))
    rfl
    (fixedGreenDifferentiability period hPeriod input natural
      (D11Frame period hPeriod input natural frame))
    (fun _ => rfl) zeroTrace
    (OldBaseFamily period hPeriod input).familyIndex.referenceTrace
    (OldBaseFamily period hPeriod input).familyIndex.zetaFamily
    referenceCoefficientAgreement parameter

/-- The rebuilt relative trace is exactly minus the unchanged reference trace. -/
theorem rebuiltBismutFreedFamily_relativeTrace
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input))
    (referenceCoefficientAgreement : ∀ parameter,
      relativeZetaConnectionCoefficient
          (OldBaseFamily period hPeriod input).familyIndex.zetaFamily.toZetaFamily
          parameter =
        ((OldBaseFamily period hPeriod input).familyIndex.referenceTrace.trace
          parameter : Real))
    (parameter : Real) :
    (rebuiltBismutFreedFamily period hPeriod input natural frame zeroTrace
      referenceCoefficientAgreement).familyIndex.relativeTrace.trace parameter =
        -(OldBaseFamily period hPeriod input).familyIndex.referenceTrace.trace
          parameter := by
  exact SelfAdjointKernelComplementBismutFreedFamilyData.zeroActualDerivative_relativeTrace
    (OldBaseFamily period hPeriod input).familyIndex.actual_selfAdjoint
    (fixedComplementGapFamily period hPeriod input natural
      (D11Frame period hPeriod input natural frame))
    (differentiableFixedReducedFamily period hPeriod input natural
      (D11Frame period hPeriod input natural frame))
    rfl
    (fixedGreenDifferentiability period hPeriod input natural
      (D11Frame period hPeriod input natural frame))
    (fun _ => rfl) zeroTrace
    (OldBaseFamily period hPeriod input).familyIndex.referenceTrace
    (OldBaseFamily period hPeriod input).familyIndex.zetaFamily
    referenceCoefficientAgreement parameter

/-- Public concrete reference-only Bismut--Freed checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_reference_trace_bismut_freed_family_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input))
    (referenceCoefficientAgreement : ∀ parameter,
      relativeZetaConnectionCoefficient
          (OldBaseFamily period hPeriod input).familyIndex.zetaFamily.toZetaFamily
          parameter =
        ((OldBaseFamily period hPeriod input).familyIndex.referenceTrace.trace
          parameter : Real)) :
    let rebuilt := rebuiltBismutFreedFamily period hPeriod input natural frame
      zeroTrace referenceCoefficientAgreement
    rebuilt.quillen = (OldBaseFamily period hPeriod input).quillen ∧
    rebuilt.actualOperator = (OldBaseFamily period hPeriod input).actualOperator ∧
    rebuilt.referenceOperator =
      (OldBaseFamily period hPeriod input).referenceOperator ∧
    rebuilt.familyIndex.zetaFamily =
      (OldBaseFamily period hPeriod input).familyIndex.zetaFamily ∧
    (∀ parameter, rebuilt.familyIndex.actualTrace.trace parameter = 0) ∧
    (∀ parameter,
      rebuilt.familyIndex.relativeTrace.trace parameter =
        -(OldBaseFamily period hPeriod input).familyIndex.referenceTrace.trace
          parameter) ∧
    (∀ parameter,
      rebuilt.familyIndex.toBismutFreed.operatorTrace.bismutFreedCoefficient
          parameter = (circleQuillenConnectionCoefficient fold : Complex)) := by
  dsimp only
  exact
    ⟨rfl, rfl, rfl, rfl,
      rebuiltBismutFreedFamily_actualTrace_zero period hPeriod input natural frame
        zeroTrace referenceCoefficientAgreement,
      rebuiltBismutFreedFamily_relativeTrace period hPeriod input natural frame
        zeroTrace referenceCoefficientAgreement,
      (rebuiltBismutFreedFamily period hPeriod input natural frame zeroTrace
        referenceCoefficientAgreement).coefficient_eq_circle⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11ReferenceTraceBismutFreedFamily4D
end JanusFormal
