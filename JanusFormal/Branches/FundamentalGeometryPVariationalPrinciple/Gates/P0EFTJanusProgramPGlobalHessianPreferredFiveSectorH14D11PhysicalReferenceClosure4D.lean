import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11ReferenceTraceSpectralAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D

/-!
# Physical D11 kernel family over the reference-only spectral atlas

Two independent replacements have now been constructed:

* the spectral-cut atlas is rebuilt so that the fixed-coordinate actual trace
  vanishes and every local coefficient is supplied solely by its reference
  trace;
* the exact H12 kernel basis is transported by the unitary D11 frame, producing
  a sector-pure C1 basis of every true kernel.

This file combines them into one named-kernel closure.  It retains the local
reference operators and zeta charts from the original atlas while replacing
its arbitrary named kernel basis by the physical D11-transported basis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11PhysicalReferenceClosure4D

set_option autoImplicit false
set_option maxHeartbeats 190000000
set_option synthInstance.maxHeartbeats 95000000
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
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11ReferenceTraceSpectralAtlas4D
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

private def physicalOutput
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural) :=
  (frame.toConcreteH14D11UnitaryFredholmGreenClosure period hPeriod input natural).
    fredholmFrame period hPeriod input natural |>.physical

/-- Physical named-kernel family over the rebuilt reference-only atlas. -/
def physicalReferenceNamedKernelClosure
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
  kernels := (physicalOutput period hPeriod input natural frame).closure.kernels
  basis_zero_agreement := by
    intro mode
    change
      ((physicalOutput period hPeriod input natural frame).closure.kernels.basis
        0 mode).1 =
      ((OldAtlas period hPeriod input).baseFamily.quillen.intrinsicFamily.
        basepoint.intrinsic.closure.basis mode).1
    exact (physicalOutput period hPeriod input natural frame).closure.
      basis_zero_agreement mode

/-- The combined closure is physically sector-resolved. -/
def physicalReferenceResolvedKernelFamily
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
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod
      (physicalReferenceNamedKernelClosure period hPeriod input natural frame
        zeroTrace baseReferenceCoefficientAgreement
          referenceCoefficientAgreement) where
  basis_fixed_by_sector := by
    intro parameter mode
    change
      (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod
        (physicalOutput period hPeriod input natural frame).closure).sectorProjector
        (namedModeFiveSector period hPeriod
          (physicalOutput period hPeriod input natural frame).closure mode)
        ((physicalOutput period hPeriod input natural frame).closure.kernels.vector
          parameter mode) =
      (physicalOutput period hPeriod input natural frame).closure.kernels.vector
        parameter mode
    exact (physicalOutput period hPeriod input natural frame).resolved.
      basis_fixed_by_sector parameter mode

/-- The combined physical basis remains C1 in the ambient Candidate-A Hilbert
space. -/
def physicalReferenceRegularity
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
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod
        (physicalReferenceNamedKernelClosure period hPeriod input natural frame
          zeroTrace baseReferenceCoefficientAgreement
            referenceCoefficientAgreement) where
  vector_differentiable :=
    (physicalOutput period hPeriod input natural frame).regularity.
      vector_differentiable

/-- Public physical/reference combined closure checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_physical_reference_closure_gate
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
    let closure := physicalReferenceNamedKernelClosure period hPeriod input
      natural frame zeroTrace baseReferenceCoefficientAgreement
        referenceCoefficientAgreement
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod closure ∧
    closure.familyIndex.referenceOperator =
      (OldAtlas period hPeriod input).referenceOperator ∧
    closure.familyIndex.localFamily =
      (OldAtlas period hPeriod input).localFamily ∧
    (∀ parameter,
      closure.familyIndex.baseFamily.familyIndex.actualTrace.trace parameter = 0) := by
  dsimp only
  exact
    ⟨physicalReferenceResolvedKernelFamily period hPeriod input natural frame
        zeroTrace baseReferenceCoefficientAgreement
          referenceCoefficientAgreement,
      physicalReferenceRegularity period hPeriod input natural frame zeroTrace
        baseReferenceCoefficientAgreement referenceCoefficientAgreement,
      rfl, rfl,
      rebuiltBismutFreedFamily_actualTrace_zero period hPeriod input natural frame
        zeroTrace baseReferenceCoefficientAgreement⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11PhysicalReferenceClosure4D
end JanusFormal
