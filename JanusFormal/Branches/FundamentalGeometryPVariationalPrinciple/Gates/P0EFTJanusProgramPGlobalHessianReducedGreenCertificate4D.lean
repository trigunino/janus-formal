import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedReducedInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianConcreteCertificate4D

/-!
# Concrete Hessian certificate with reduced Green operator

The concrete three-packet frontier now yields one terminal object containing:

* the same-action H10--H14 closure certificate;
* the exact Fredholm splitting `ker H = range P`, `range H = ker P`;
* the bijective restriction of `H` to `ker P`;
* its continuous inverse, with norm at most the reciprocal coercivity constant.

This is the operator package needed by the reduced determinant and by stability
on the zero-mode quotient.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianReducedGreenCertificate4D

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option synthInstance.maxHeartbeats 3500000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyBoundaryProjection4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalAgreement4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedReducedInverse4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianConcreteAgreementClosure4D
open P0EFTJanusProgramPGlobalHessianConcreteCertificate4D

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
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- H14, exact splitting and reduced Green operator in one certificate. -/
structure GlobalCandidateAHessianReducedGreenCertificate4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family))
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions)) :
    Prop where
  hessian : GlobalCandidateAConcreteHessianCertificate4D period hPeriod
    configuration data analysis einsteinScale hBoundaryTransverse family
      extensions shift
  reducedGreen : GlobalCandidateAAugmentedReducedInverseCertificate4D period
    hPeriod configuration data analysis
      (globalCandidateABoundaryProjectionChart period hPeriod configuration
        data analysis einsteinScale hBoundaryTransverse family)
      (globalCandidateABoundaryProjectionSameAction period hPeriod configuration
        data analysis einsteinScale hBoundaryTransverse family)
      (globalCandidateAConcretePhysicalExtension period hPeriod configuration
        data analysis einsteinScale hBoundaryTransverse family extensions)
      shift

/-- Construction from the same three analytic packets. -/
theorem global_candidateA_hessian_reducedGreen_certificate_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family))
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions)) :
    GlobalCandidateAHessianReducedGreenCertificate4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift where
  hessian := global_candidateA_hessian_concrete_certificate_gate period hPeriod
    configuration data analysis einsteinScale hBoundaryTransverse family
      extensions shift
  reducedGreen := global_candidateA_augmented_reduced_inverse_gate period hPeriod
    configuration data analysis
      (globalCandidateABoundaryProjectionChart period hPeriod configuration
        data analysis einsteinScale hBoundaryTransverse family)
      (globalCandidateABoundaryProjectionSameAction period hPeriod configuration
        data analysis einsteinScale hBoundaryTransverse family)
      (globalCandidateAConcretePhysicalExtension period hPeriod configuration
        data analysis einsteinScale hBoundaryTransverse family extensions)
      shift

/-- Exact zero-mode identification. -/
theorem GlobalCandidateAHessianReducedGreenCertificate4D.kernel_eq_defect
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)}
    {shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions)}
    (certificate : GlobalCandidateAHessianReducedGreenCertificate4D period
      hPeriod configuration data analysis einsteinScale hBoundaryTransverse
        family extensions shift) :=
  certificate.hessian.kernel_eq_defect

/-- Exact range complement. -/
theorem GlobalCandidateAHessianReducedGreenCertificate4D.range_eq_complement
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)}
    {shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions)}
    (certificate : GlobalCandidateAHessianReducedGreenCertificate4D period
      hPeriod configuration data analysis einsteinScale hBoundaryTransverse
        family extensions shift) :=
  certificate.hessian.range_eq_complement

/-- Quantitative bound on the reduced Green operator. -/
theorem GlobalCandidateAHessianReducedGreenCertificate4D.reducedGreen_opNorm_le
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)}
    {shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions)}
    (certificate : GlobalCandidateAHessianReducedGreenCertificate4D period
      hPeriod configuration data analysis einsteinScale hBoundaryTransverse
        family extensions shift) :
    ‖globalCandidateAAugmentedReducedInverse period hPeriod configuration data
      analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions)
        shift‖ ≤ shift.coerciveShift.coercivityConstant⁻¹ :=
  certificate.reducedGreen.inverse_opNorm_le

end
end P0EFTJanusProgramPGlobalHessianReducedGreenCertificate4D
end JanusFormal
