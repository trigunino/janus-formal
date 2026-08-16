import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11ReferenceTraceBismutFreedFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D

/-!
# Reference-only spectral-cut atlas in the H14--D11 frame

The preferred spectral atlas already stores every reference operator, its
intrinsic logarithmic trace and its local relative zeta family.  After the
actual Candidate-A family is trivialized by the operator-norm D11 frame, its
fixed-coordinate logarithmic trace vanishes.

This file rebuilds the whole atlas with

```text
local zeta coefficient = reference logarithmic trace
```

as the only chartwise trace comparison.  It keeps exactly the same actual
operator, reference operators, reference trace certificates, local zeta
families, Quillen base chart and named kernel family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11ReferenceTraceSpectralAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 184000000
set_option synthInstance.maxHeartbeats 92000000
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
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSpectralCutReferenceAtlas4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11ReferenceTraceBismutFreedFamily4D
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

private abbrev OldAtlas
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  input.familyIndex

private abbrev BaseReduced
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  SelfAdjointKernelComplement
    ((OldAtlas period hPeriod input).baseFamily.actualOperator 0)

/-- Spectral-cut atlas rebuilt with the D11/H14 actual family and unchanged
references. -/
def rebuiltSpectralCutReferenceAtlas
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
    (baseReferenceCoefficientAgreement : ∀ parameter,
      relativeZetaConnectionCoefficient
          (OldAtlas period hPeriod input).baseFamily.familyIndex.zetaFamily.
            toZetaFamily parameter =
        ((OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.
          trace parameter : Real))
    (referenceCoefficientAgreement : ∀ index parameter,
      relativeZetaConnectionCoefficient
          ((OldAtlas period hPeriod input).localFamily index).toZetaFamily
          parameter =
        ((OldAtlas period hPeriod input).referenceTrace index).trace parameter) :
    GlobalHessianPreferredFiveSectorSpectralCutReferenceAtlas4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index where
  baseFamily := rebuiltBismutFreedFamily period hPeriod input natural frame
    zeroTrace baseReferenceCoefficientAgreement
  referenceOperator := (OldAtlas period hPeriod input).referenceOperator
  referenceTrace := (OldAtlas period hPeriod input).referenceTrace
  localFamily := (OldAtlas period hPeriod input).localFamily
  baseReference_eq := (OldAtlas period hPeriod input).baseReference_eq
  baseFamily_eq := (OldAtlas period hPeriod input).baseFamily_eq
  coefficient_agreement := by
    intro index parameter
    have hZero := rebuiltBismutFreedFamily_actualTrace_zero period hPeriod input
      natural frame zeroTrace baseReferenceCoefficientAgreement parameter
    rw [hZero]
    simpa using referenceCoefficientAgreement index parameter

/-- Named-kernel closure rebuilt over the reference-only spectral atlas. -/
def rebuiltNamedKernelFamilyClosure
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
    (baseReferenceCoefficientAgreement : ∀ parameter,
      relativeZetaConnectionCoefficient
          (OldAtlas period hPeriod input).baseFamily.familyIndex.zetaFamily.
            toZetaFamily parameter =
        ((OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.
          trace parameter : Real))
    (referenceCoefficientAgreement : ∀ index parameter,
      relativeZetaConnectionCoefficient
          ((OldAtlas period hPeriod input).localFamily index).toZetaFamily
          parameter =
        ((OldAtlas period hPeriod input).referenceTrace index).trace parameter) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index where
  familyIndex := rebuiltSpectralCutReferenceAtlas period hPeriod input natural
    frame zeroTrace baseReferenceCoefficientAgreement
      referenceCoefficientAgreement
  kernels := input.kernels
  basis_zero_agreement := input.basis_zero_agreement

/-- Public reference-only spectral-atlas checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_reference_trace_spectral_atlas_gate
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
    (baseReferenceCoefficientAgreement : ∀ parameter,
      relativeZetaConnectionCoefficient
          (OldAtlas period hPeriod input).baseFamily.familyIndex.zetaFamily.
            toZetaFamily parameter =
        ((OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.
          trace parameter : Real))
    (referenceCoefficientAgreement : ∀ index parameter,
      relativeZetaConnectionCoefficient
          ((OldAtlas period hPeriod input).localFamily index).toZetaFamily
          parameter =
        ((OldAtlas period hPeriod input).referenceTrace index).trace parameter) :
    let rebuilt := rebuiltSpectralCutReferenceAtlas period hPeriod input natural
      frame zeroTrace baseReferenceCoefficientAgreement
        referenceCoefficientAgreement
    rebuilt.referenceOperator = (OldAtlas period hPeriod input).referenceOperator ∧
    rebuilt.referenceTrace = (OldAtlas period hPeriod input).referenceTrace ∧
    rebuilt.localFamily = (OldAtlas period hPeriod input).localFamily ∧
    rebuilt.baseFamily.quillen = (OldAtlas period hPeriod input).baseFamily.quillen ∧
    (∀ parameter,
      rebuilt.baseFamily.familyIndex.actualTrace.trace parameter = 0) ∧
    (∀ index parameter,
      relativeZetaConnectionCoefficient (rebuilt.localFamily index).toZetaFamily
          parameter = (rebuilt.referenceTrace index).trace parameter) := by
  dsimp only
  exact
    ⟨rfl, rfl, rfl, rfl,
      rebuiltBismutFreedFamily_actualTrace_zero period hPeriod input natural frame
        zeroTrace baseReferenceCoefficientAgreement,
      referenceCoefficientAgreement⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11ReferenceTraceSpectralAtlas4D
end JanusFormal
