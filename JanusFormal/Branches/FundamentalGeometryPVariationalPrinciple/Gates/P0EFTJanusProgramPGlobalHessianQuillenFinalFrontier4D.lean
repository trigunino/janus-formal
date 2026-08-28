import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianQuillenClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianZetaDeterminantAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaFinitePartFamily4D

/-!
# Final coherent Quillen frontier for the Candidate-A Hessian

The preceding layers construct three complementary pieces:

* the actual circle determinant line, metric, connection and clutching together
  with the global Candidate-A parallel section;
* a general multi-chart zeta atlas, independent of the special circle frame;
* the parameterwise equality between the complex zeta norm and the real
  finite-part determinant metric.

This file requires those pieces to be based on the *same* Candidate-A zeta
determinant and the same one-parameter zeta family.  It then packages the
circle closure, the Cech atlas, the positive metric variation and the unitary
phase in one terminal certificate.  No new determinant, line, completion or
connection is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianQuillenFinalFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 6000000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace ComplexConjugate
open P0EFTJanusCircleDiracHeatTraceCancellation
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
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianConcreteAgreementClosure4D
open P0EFTJanusProgramPGlobalHessianQuillenFamilyBridge4D
open P0EFTJanusProgramPGlobalHessianQuillenClosure4D
open P0EFTJanusProgramPGlobalHessianZetaDeterminant4D
open P0EFTJanusProgramPGlobalHessianZetaDeterminantAtlas4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D

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

/-- Coherent terminal input.  The equality fields prevent the circle bridge,
the general atlas and the finite-part metric family from referring to three
unrelated zeta determinants. -/
structure GlobalCandidateAHessianQuillenFinalFrontierData4D
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
          data analysis einsteinScale hBoundaryTransverse family extensions))
    (fold : Fold) (Index : Type*) where
  bridge : GlobalCandidateAHessianQuillenFamilyBridgeData4D period hPeriod
    configuration data analysis einsteinScale hBoundaryTransverse family
      extensions shift fold
  atlas : GlobalCandidateAHessianZetaDeterminantAtlasData4D period hPeriod
    configuration data analysis einsteinScale hBoundaryTransverse family
      extensions shift Index
  metricComparison : RelativeZetaFinitePartFamilyComparisonData
  atlas_determinant_eq : atlas.determinant = bridge.basepointDeterminant
  metric_zetaFamily_eq : metricComparison.zetaFamily = bridge.zetaFamily

/-- The periodic Candidate-A determinant has exactly the positive finite-part
magnitude supplied by the metric family. -/
theorem GlobalCandidateAHessianQuillenFinalFrontierData4D.basepoint_norm_eq
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
    {fold : Fold} {Index : Type*}
    (inputs : GlobalCandidateAHessianQuillenFinalFrontierData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift fold Index) :
    ‖globalCandidateAHessianZetaDeterminant
        inputs.bridge.basepointDeterminant‖ =
      relativeHeatFinitePartDeterminantFamily
        inputs.metricComparison.finitePartFamily 0 := by
  rw [← inputs.bridge.basepoint_agreement]
  rw [← inputs.metric_zetaFamily_eq]
  exact inputs.metricComparison.norm_zeta_eq_finitePart 0

/-- The selected atlas base chart represents the same concrete Candidate-A
zeta determinant as the circle bridge. -/
theorem GlobalCandidateAHessianQuillenFinalFrontierData4D.atlas_base_eq_bridge
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
    {fold : Fold} {Index : Type*}
    (inputs : GlobalCandidateAHessianQuillenFinalFrontierData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift fold Index) :
    globalCandidateAHessianZetaAtlasCoordinate inputs.atlas
        inputs.atlas.baseIndex inputs.atlas.baseParameter =
      globalCandidateAHessianZetaDeterminant
        inputs.bridge.basepointDeterminant := by
  rw [globalCandidateAHessianZetaAtlasCoordinate_base]
  rw [inputs.atlas_determinant_eq]

/-- Coherent terminal certificate. -/
structure GlobalCandidateAHessianQuillenFinalFrontierCertificate4D
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
    {fold : Fold} {Index : Type*}
    (inputs : GlobalCandidateAHessianQuillenFinalFrontierData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift fold Index) where
  globalClosure : GlobalCandidateAHessianQuillenClosureCertificate4D period
    hPeriod configuration data analysis einsteinScale hBoundaryTransverse family
      extensions shift fold inputs.bridge
  atlasCertificate :
    GlobalCandidateAHessianZetaDeterminantAtlasCertificate4D inputs.atlas
  basepointNorm :
    ‖globalCandidateAHessianZetaDeterminant
        inputs.bridge.basepointDeterminant‖ =
      relativeHeatFinitePartDeterminantFamily
        inputs.metricComparison.finitePartFamily 0
  metricVariation : ∀ parameter,
    relativeHeatFinitePartMetricWeightDerivative
        inputs.metricComparison.finitePartFamily parameter =
      -2 *
        (relativeZetaConnectionCoefficient
          inputs.metricComparison.zetaFamily parameter).re *
        relativeHeatFinitePartMetricWeight
          inputs.metricComparison.finitePartFamily parameter
  phaseUnitary : ∀ parameter,
    ‖relativeZetaFinitePartPhase inputs.metricComparison parameter‖ = 1

/-- Build the coherent terminal certificate. -/
def globalCandidateAHessianQuillenFinalFrontierCertificate
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
    {fold : Fold} {Index : Type*}
    (inputs : GlobalCandidateAHessianQuillenFinalFrontierData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift fold Index) :
    GlobalCandidateAHessianQuillenFinalFrontierCertificate4D inputs where
  globalClosure :=
    globalCandidateAHessianQuillenClosureCertificate inputs.bridge
  atlasCertificate :=
    globalCandidateAHessianZetaDeterminantAtlasCertificate inputs.atlas
  basepointNorm := inputs.basepoint_norm_eq period hPeriod
  metricVariation :=
    inputs.metricComparison.metricWeightDerivative_eq_connection
  phaseUnitary :=
    relativeZetaFinitePartPhase_norm_one inputs.metricComparison

/-- Public final coherent Quillen gate. -/
def global_candidateA_hessian_quillen_final_frontier_gate
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
    {fold : Fold} {Index : Type*}
    (inputs : GlobalCandidateAHessianQuillenFinalFrontierData4D period hPeriod
      configuration data analysis einsteinScale hBoundaryTransverse family
        extensions shift fold Index) :
    GlobalCandidateAHessianQuillenFinalFrontierCertificate4D inputs :=
  globalCandidateAHessianQuillenFinalFrontierCertificate inputs

end
end P0EFTJanusProgramPGlobalHessianQuillenFinalFrontier4D
end JanusFormal
