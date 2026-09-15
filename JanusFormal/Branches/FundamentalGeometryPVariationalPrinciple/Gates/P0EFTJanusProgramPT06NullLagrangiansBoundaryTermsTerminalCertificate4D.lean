import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06EulerRelativeRadialNormalForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06PhysicalBoundaryDensityClassificationBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalVariationalCohomology4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05FiniteNullHorizontalIntegrationMorphism4D

/-!
# Terminal null-Lagrangian and boundary-term certificate for T06

This certificate records the exhaustive scopes proved for T06: functional
cohomology on normed charts, the genuine bounded T02 Euler kernel and its
smooth physical radial J3 current, and exactness of the integrated T05
relative carrier.  The common Euler-relative normal form links the local and
relative statements.  The established GHY and faithful null/joint families
are concrete instances of the relative classification.

As for the T05 terminal certificate, a globally inhabited physical collar
atlas, intrinsic coarea measure and an atlas-glued Stokes theorem are stronger
follow-up objectives, not assumptions of this classification theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06NullLagrangiansBoundaryTermsTerminalCertificate4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open MeasureTheory
open scoped BigOperators ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalVariationalCohomology4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05FiniteNullHorizontalIntegrationMorphism4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityRegularity4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityHorizontalDifferential4D
open P0EFTJanusProgramPT06EulerRelativeRadialNormalForm4D
open P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D
open P0EFTJanusProgramPT06PhysicalBoundaryDensityClassificationBridge4D
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

attribute [local instance]
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

universe u v

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

private abbrev Fiber := ActualPhysicalValueProductFiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

local notation "Bicomplex" => programPT05ExactT03RelativeBicomplex

/-- The terminal T06 classification certificate at the proved global,
bounded-local and integrated-relative scopes. -/
structure ProgramPT06NullLagrangiansBoundaryTermsCertificate4D : Prop where
  functional_null_iff_constant :
    ∀ {Configuration : Type u}
      [NormedAddCommGroup Configuration] [NormedSpace Real Configuration]
      (lagrangian : Configuration → Real),
      VariationallyNull lagrangian ↔
        ∃ constant : Real, ∀ configuration, lagrangian configuration = constant
  same_global_euler_mod_constant :
    ∀ {couplings : GlobalCandidateAActionCouplings}
      {NonNullFace NullFace : Type u} [Fintype NonNullFace] [Fintype NullFace]
      {measure : Measure (EffectiveQuotient period hPeriod)}
      (chart : GlobalCandidateAVariationalChart.{v, u, u} period hPeriod couplings
        NonNullFace NullFace measure)
      (firstAction secondAction : chart.Configuration → Real),
      (∀ configuration,
        HasFDerivAt firstAction
          (globalEulerLagrangeOperator period hPeriod chart configuration)
          configuration) →
      (∀ configuration,
        HasFDerivAt secondAction
          (globalEulerLagrangeOperator period hPeriod chart configuration)
          configuration) →
      ∃ constant : Real, ∀ configuration,
        firstAction configuration = secondAction configuration + constant
  global_counterterms_mod_constant :
    ∀ {couplings : GlobalCandidateAActionCouplings}
      {NonNullFace NullFace : Type u} [Fintype NonNullFace] [Fintype NullFace]
      {measure : Measure (EffectiveQuotient period hPeriod)}
      (chart : GlobalCandidateAVariationalChart.{v, u, u} period hPeriod couplings
        NonNullFace NullFace measure)
      (firstCounterterm secondCounterterm : chart.Configuration → Real),
      (∀ configuration,
        HasFDerivAt firstCounterterm
          (-globalEulerLagrangeOperator period hPeriod chart configuration)
          configuration) →
      (∀ configuration,
        HasFDerivAt secondCounterterm
          (-globalEulerLagrangeOperator period hPeriod chart configuration)
          configuration) →
      ∃ constant : Real, ∀ configuration,
        firstCounterterm configuration =
          secondCounterterm configuration + constant
  t02_euler_iff_constant_add_physical_radial_dH :
    ∀ (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod),
      (∀ jet : FourthJet,
        programPT06SecondOrderLocalEuler
          (programPT06T02FinsuppSecondJetLocalLagrangian
            period hPeriod functional) jet = 0) ↔
        ∀ jet : FourthJet,
          programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod
              functional
              (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) =
            functional.lower.lower.constant +
              programPT06ActualPhysicalThirdJetVectorDensityChartwiseDH
                (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
                  period hPeriod functional) jet
  physical_radial_current_smooth :
    ∀ (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod),
      ContDiff Real ∞
        (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
          period hPeriod functional)
  relative_null_iff_boundary :
    ∀ (density : ProgramPT06RelativeDensity4D),
      IsHorizontalDensity density →
        (IsRelativeNullLagrangian density ↔ IsRelativeBoundaryTerm density)
  relative_boundary_has_unique_normalized_primitive :
    ∀ (density : ProgramPT06RelativeDensity4D),
      IsRelativeBoundaryTerm density →
        ∃! primitive : ProgramPT06RelativeBoundaryPrimitive4D,
          IsNormalizedRelativeBoundaryPrimitive primitive ∧
            (Bicomplex).dH 3 0 primitive = density
  common_euler_relative_normal_form :
    ∀ (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod),
      IsProgramPT06EulerRelativeNull period hPeriod functional ↔
        ∃! normalForm : ProgramPT06EulerRelativeRadialNormalForm4D,
          IsProgramPT06EulerRelativeRadialNormalForm
            period hPeriod functional normalForm
  canonical_ghy_is_boundary_and_null :
    ∀ (einsteinScale : Real)
      (metric : RegularGeneralLorentzMetric period hPeriod)
      (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real),
      IsRelativeBoundaryTerm
          (programPT06CanonicalGHYBoundaryDensity period hPeriod einsteinScale
            metric current) ∧
        IsRelativeNullLagrangian
          (programPT06CanonicalGHYBoundaryDensity period hPeriod einsteinScale
            metric current)
  canonical_ghy_primitive_is_action :
    ∀ (einsteinScale : Real)
      (metric : RegularGeneralLorentzMetric period hPeriod)
      (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real),
      programPT05GHYDensityIntegratedRelativeCochain period hPeriod
          (programPT05CanonicalGHYLocalDensityCochain period hPeriod
            einsteinScale metric current) .nonNullBoundary =
        (candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation
          period hPeriod einsteinScale metric current, 0)
  faithful_null_joint_is_boundary_and_null :
    ∀ {NullFace : Type u} [Fintype NullFace]
      (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
      (input : FiniteNullFacePhysicalHilbert NullFace),
      input ∈ faithful.realization.geometry.domain →
        IsRelativeBoundaryTerm
            (programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
              faithful input) ∧
          IsRelativeNullLagrangian
            (programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
              faithful input)
  faithful_joint_is_oriented_action_change :
    ∀ {NullFace : Type u} [Fintype NullFace]
      (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
      (input : FiniteNullFacePhysicalHilbert NullFace),
      (programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
          faithful input .joint).1 =
        ∑ face : NullFace,
          (reparametrizedEndpointJointAction
              (faithful.realization.geometry.toFiniteNullFaceActionDatum
                input face) -
            endpointJointAction
              (faithful.realization.geometry.toFiniteNullFaceActionDatum
                input face))
  integrated_physical_packet_null_iff_boundary :
    ∀ {NullFace : Type u} [Fintype NullFace]
      (couplings : GlobalCandidateAActionCouplings)
      (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
      (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
      (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
      (input : FiniteNullFacePhysicalHilbert NullFace),
      IsRelativeNullLagrangian
          (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
            couplings bulk ghy faithful input) ↔
        IsRelativeBoundaryTerm
          (programPT05T03FaithfulGeometricDensityIntegrationMap period hPeriod
            couplings bulk ghy faithful input)

/-- Public terminal theorem: every field is discharged by a previously proved
classification or concrete geometric corollary. -/
theorem program_p_t06_null_lagrangians_boundary_terms_terminal_gate :
    ProgramPT06NullLagrangiansBoundaryTermsCertificate4D period hPeriod where
  functional_null_iff_constant := variationallyNull_iff_exists_constant
  same_global_euler_mod_constant := by
    intro couplings NonNullFace NullFace _ _ measure chart firstAction
      secondAction hFirst hSecond
    exact sameGlobalEulerActions_differ_by_constant period hPeriod chart
      firstAction secondAction hFirst hSecond
  global_counterterms_mod_constant := by
    intro couplings NonNullFace NullFace _ _ measure chart firstCounterterm
      secondCounterterm hFirst hSecond
    exact globalBoundaryCounterterms_differ_by_constant period hPeriod chart
      firstCounterterm secondCounterterm hFirst hSecond
  t02_euler_iff_constant_add_physical_radial_dH := by
    intro functional
    exact
      (isProgramPT06EulerRelativeNull_iff_euler_zero
        period hPeriod functional).symm.trans
      (isProgramPT06EulerRelativeNull_iff_physicalRadialNormalForm
        period hPeriod functional)
  physical_radial_current_smooth :=
    programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_contDiff
      period hPeriod
  relative_null_iff_boundary := horizontalDensity_null_iff_boundary
  relative_boundary_has_unique_normalized_primitive :=
    relativeBoundaryTerm_existsUnique_normalizedPrimitive
  common_euler_relative_normal_form :=
    isProgramPT06EulerRelativeNull_iff_existsUnique_radialNormalForm
      period hPeriod
  canonical_ghy_is_boundary_and_null :=
    programPT06CanonicalGHYBoundaryDensity_boundary_and_null period hPeriod
  canonical_ghy_primitive_is_action :=
    programPT06CanonicalGHYPrimitive_nonNull_eq_action period hPeriod
  faithful_null_joint_is_boundary_and_null := by
    intro NullFace _ faithful input hInput
    exact programPT06FaithfulNullJointBoundaryDensity_boundary_and_null
      faithful input hInput
  faithful_joint_is_oriented_action_change := by
    intro NullFace _ faithful input
    exact programPT06FaithfulNullJointBoundaryDensity_joint_eq_actionChanges
      faithful input
  integrated_physical_packet_null_iff_boundary := by
    intro NullFace _ couplings bulk ghy faithful input
    exact programPT06T03FaithfulGeometricDensity_null_iff_boundary
      period hPeriod couplings bulk ghy faithful input

end
end P0EFTJanusProgramPT06NullLagrangiansBoundaryTermsTerminalCertificate4D
end JanusFormal
