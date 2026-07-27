import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationModuleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationD9FieldAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationBoundaryDomainBridge4D

/-!
# Constructed D7/D9 core of the complete Program-P variation

This gate records only facts that are already constructed:

* the independent variation embeds linearly and retracts exactly;
* the completed tangent is a real module and its geometric D9 coordinates
  are linear;
* the boundary domain is exactly the pullback along the independent slot;
* the complete local D9 field is assembled canonically from one tangent.

No equivalence between the smooth tangent and the complete D10 Hilbert space,
Fredholm identification, or Hessian spectral agreement is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCompleteVariationConstructedCore4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusCompleteVariationD9FieldAssembly4D
open P0EFTJanusCompleteVariationBoundaryDomainBridge4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD9DiffeomorphismGhostPrincipalSymbolBridge4D
open P0EFTJanusD9FullSymmetricMetricLocalCompletion4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Canonical algebraic and boundary facts for the complete variation. -/
structure ProgramPCompleteVariationLinearCoreCertificate4D : Prop where
  moduleStructure :
    Nonempty (Module Real (ProgramPCompleteVariation4D period hPeriod))
  extension_retract :
    ∀ variation : IndependentFieldVariation period hPeriod,
      (independentCompleteVariationLinearMap period hPeriod variation).independent =
        variation
  extension_injective :
    Function.Injective (independentCompleteVariationLinearMap period hPeriod)
  normal_add :
    ∀ first second sector point,
      (first + second : ProgramPCompleteVariation4D period hPeriod).normalModeAt
          period hPeriod sector point =
        first.normalModeAt period hPeriod sector point +
          second.normalModeAt period hPeriod sector point
  normal_smul :
    ∀ scalar variation sector point,
      (scalar • variation : ProgramPCompleteVariation4D period hPeriod).normalModeAt
          period hPeriod sector point =
        scalar * variation.normalModeAt period hPeriod sector point
  ghost_add :
    ∀ first second sector point,
      (first + second : ProgramPCompleteVariation4D period hPeriod).diffeomorphismGhostAt
          period hPeriod sector point =
        addTangent
          (first.diffeomorphismGhostAt period hPeriod sector point)
          (second.diffeomorphismGhostAt period hPeriod sector point)
  ghost_smul :
    ∀ scalar variation sector point,
      (scalar • variation :
          ProgramPCompleteVariation4D period hPeriod).diffeomorphismGhostAt
            period hPeriod sector point =
        scaleTangent scalar
          (variation.diffeomorphismGhostAt period hPeriod sector point)
  metric_add :
    ∀ first second sector point,
      (first + second : ProgramPCompleteVariation4D period hPeriod).metricPerturbationAt
          period hPeriod sector point =
        addSymmetric
          (first.metricPerturbationAt period hPeriod sector point)
          (second.metricPerturbationAt period hPeriod sector point)
  metric_smul :
    ∀ scalar variation sector point,
      (scalar • variation :
          ProgramPCompleteVariation4D period hPeriod).metricPerturbationAt
            period hPeriod sector point =
        scaleSymmetric scalar
          (variation.metricPerturbationAt period hPeriod sector point)
  boundary_exact :
    ∀ (domain : ProgramPCommonGeometricDomain4D period hPeriod)
      (variation : ProgramPCompleteVariation4D period hPeriod),
      variation ∈ programPBoundaryTangentDomain4D period hPeriod domain ↔
        variation.independent ∈
          independentBoundaryTangentDomain4D period hPeriod domain

/-- The algebraic/boundary certificate is unconditional. -/
theorem programPCompleteVariationLinearCoreCertificate4D :
    ProgramPCompleteVariationLinearCoreCertificate4D period hPeriod where
  moduleStructure := ⟨inferInstance⟩
  extension_retract := independentCompleteVariation_independent period hPeriod
  extension_injective := by
    intro first second h
    exact independentCompleteVariation_injective period hPeriod h
  normal_add := normalModeAt_add period hPeriod
  normal_smul := normalModeAt_smul period hPeriod
  ghost_add := diffeomorphismGhostAt_add period hPeriod
  ghost_smul := diffeomorphismGhostAt_smul period hPeriod
  metric_add := metricPerturbationAt_add period hPeriod
  metric_smul := metricPerturbationAt_smul period hPeriod
  boundary_exact := completeVariation_mem_boundaryDomain_iff period hPeriod

/-- Exact component equations for the canonical local D9 assembly. -/
structure ProgramPCompleteVariationD9CoreCertificate4D
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor) : Prop where
  normalMode :
    ∀ variation sector column point,
      (completeVariationD9Field period hPeriod matterSpinorIdentification
          variation sector column point).bosonic.normalMode =
        variation.normalModeAt period hPeriod sector point
  gaugeOneForm :
    ∀ variation sector column point,
      (completeVariationD9Field period hPeriod matterSpinorIdentification
          variation sector column point).bosonic.gaugeOneForm =
        d9GaugeOneForm period hPeriod variation.independent sector column point
  metricPerturbation :
    ∀ variation sector column point,
      (completeVariationD9Field period hPeriod matterSpinorIdentification
          variation sector column point).bosonic.metricPerturbation =
        variation.metricPerturbationAt period hPeriod sector point
  u1Ghost :
    ∀ variation sector column point,
      (completeVariationD9Field period hPeriod matterSpinorIdentification
          variation sector column point).ghosts.u1Ghost =
        d9U1Ghost period hPeriod variation.independent sector column point
  diffeomorphismGhost :
    ∀ variation sector column point,
      (completeVariationD9Field period hPeriod matterSpinorIdentification
          variation sector column point).ghosts.diffeomorphismGhost =
        variation.diffeomorphismGhostAt period hPeriod sector point
  spinor :
    ∀ variation sector column point,
      (completeVariationD9Field period hPeriod matterSpinorIdentification
          variation sector column point).spinor =
        matterSpinorIdentification
          (d9MatterCoefficient period hPeriod variation.independent sector point)

/-- The D9 assembly certificate is definitional for every chosen
identification of the matter fiber with the local spinor model. -/
theorem programPCompleteVariationD9CoreCertificate4D
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor) :
    ProgramPCompleteVariationD9CoreCertificate4D
      period hPeriod matterSpinorIdentification where
  normalMode :=
    completeVariationD9Field_normalMode
      period hPeriod matterSpinorIdentification
  gaugeOneForm :=
    completeVariationD9Field_gaugeOneForm
      period hPeriod matterSpinorIdentification
  metricPerturbation :=
    completeVariationD9Field_metricPerturbation
      period hPeriod matterSpinorIdentification
  u1Ghost :=
    completeVariationD9Field_u1Ghost
      period hPeriod matterSpinorIdentification
  diffeomorphismGhost :=
    completeVariationD9Field_diffeomorphismGhost
      period hPeriod matterSpinorIdentification
  spinor :=
    completeVariationD9Field_spinor
      period hPeriod matterSpinorIdentification

/-- Combined constructed core, separated from every remaining analytic
Hessian/Fredholm requirement. -/
structure ProgramPCompleteVariationConstructedCoreCertificate4D
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor) : Prop where
  linearCore :
    ProgramPCompleteVariationLinearCoreCertificate4D period hPeriod
  d9Core :
    ProgramPCompleteVariationD9CoreCertificate4D
      period hPeriod matterSpinorIdentification

theorem programPCompleteVariationConstructedCoreCertificate4D
    {Spinor : Type*}
    (matterSpinorIdentification : MatterFiber ≃ Spinor) :
    ProgramPCompleteVariationConstructedCoreCertificate4D
      period hPeriod matterSpinorIdentification :=
  ⟨programPCompleteVariationLinearCoreCertificate4D period hPeriod,
    programPCompleteVariationD9CoreCertificate4D
      period hPeriod matterSpinorIdentification⟩

/-- Assumption-free canonical instance using the native matter fiber. -/
theorem programPCompleteVariationConstructedCore_nonempty :
    Nonempty
      (ProgramPCompleteVariationConstructedCoreCertificate4D
        period hPeriod (Equiv.refl MatterFiber)) :=
  ⟨programPCompleteVariationConstructedCoreCertificate4D
    period hPeriod (Equiv.refl MatterFiber)⟩

end
end P0EFTJanusProgramPCompleteVariationConstructedCore4D
end JanusFormal
