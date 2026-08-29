import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCompleteVariationConstructedCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalysisDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierBridge4D

/-!
# Constructed global analytic spine and exact residual bridges

The global tangent already contains the D10 Hilbert coordinate as a direct
factor.  Consequently its D10 projection has a canonical linear section; no
equivalence between all smooth fields and one spectral sector is needed.

The constructed bulk, sectorwise SpinC, D10 and LL factors now form one
concrete Hilbert product with a dense injective operator core.  The complete
all-level SpinC coefficient certificate, D10 Fredholm certificate and LL
Riesz core are integrated.

The remaining Hessian problem is split into two honest geometric inputs:

* a dense injective analysis of the genuine smooth global tangent into a
  regular variational chart;
* the all-level geometric Fourier realization of the primitive SpinC smooth
  bundle core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalAnalyticSpine4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCompleteVariationConstructedCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierBridge4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D

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

attribute [local instance]
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- Canonical projection onto the D10 factor of the genuine global tangent. -/
def globalFieldTangentD10CoordinateLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod} :
    GlobalFieldTangent period hPeriod configuration →ₗ[Real]
      ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod configuration.d10Completion) where
  toFun := GlobalFieldTangent.d10Coordinates period hPeriod
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical inclusion of a D10 coefficient packet as a pure D10 tangent. -/
def globalFieldTangentD10SectionLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod} :
    ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod configuration.d10Completion) →ₗ[Real]
      GlobalFieldTangent period hPeriod configuration where
  toFun := fun state => (0, (0, state))
  map_add' _ _ := by
    simp
  map_smul' _ _ := by
    simp

@[simp]
theorem globalFieldTangentD10Coordinate_section
    {configuration : GlobalFieldConfiguration period hPeriod}
    (state :
      ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod configuration.d10Completion)) :
    globalFieldTangentD10CoordinateLinearMap period hPeriod
        (globalFieldTangentD10SectionLinearMap period hPeriod state) =
      state :=
  by
    simp [globalFieldTangentD10CoordinateLinearMap,
      globalFieldTangentD10SectionLinearMap,
      GlobalFieldTangent.d10Coordinates]

theorem globalFieldTangentD10Coordinate_surjective
    {configuration : GlobalFieldConfiguration period hPeriod} :
    Function.Surjective
      (globalFieldTangentD10CoordinateLinearMap
        period hPeriod (configuration := configuration)) := by
  intro state
  exact
    ⟨globalFieldTangentD10SectionLinearMap period hPeriod state,
      globalFieldTangentD10Coordinate_section period hPeriod state⟩

theorem globalFieldTangentD10Section_injective
    {configuration : GlobalFieldConfiguration period hPeriod} :
    Function.Injective
      (globalFieldTangentD10SectionLinearMap
        period hPeriod (configuration := configuration)) := by
  intro first second h
  have hCoordinates := congrArg
    (globalFieldTangentD10CoordinateLinearMap
      period hPeriod (configuration := configuration)) h
  simpa only [globalFieldTangentD10Coordinate_section] using hCoordinates

/-- Concrete Hilbert target already shared by the constructed analytic
sectors.  The primitive SpinC factor occurs once per physical sector. -/
abbrev ProgramPGlobalAnalysisHilbert4D
    (configuration : GlobalFieldConfiguration period hPeriod)
    (data : GlobalAnalysisData period hPeriod configuration) :=
  GlobalBulkDirichletHilbertH1 period hPeriod ×
    ((Sector → PrimitiveSpinCGeometricL2) ×
      (ProgramPD10ModeHilbert4D
          (d10SpectralData period hPeriod configuration.d10Completion) ×
        LLH1Space period hPeriod (data.llH1Data period hPeriod)))

/-- Dense operator core of the constructed bulk, SpinC, D10 and physical LL
blocks.  This is an actual product type, not a monolithic spectral
identification of the global tangent. -/
abbrev ProgramPGlobalDenseOperatorCore4D
    (configuration : GlobalFieldConfiguration period hPeriod)
    (data : GlobalAnalysisData period hPeriod configuration) :=
  GlobalBulkDirichletHilbertH1 period hPeriod ×
    ((Sector → PrimitiveSpinCGeometricH2 period hPeriod) ×
      (programPD10FredholmModeDomainSubmodule4D
          (d10SpectralData period hPeriod configuration.d10Completion) ×
        LLH1Smooth period hPeriod (data.llH1Data period hPeriod)))

/-- Canonical inclusion of the common operator core into the concrete global
Hilbert product. -/
def programPGlobalDenseOperatorCoreInclusion
    (configuration : GlobalFieldConfiguration period hPeriod)
    (data : GlobalAnalysisData period hPeriod configuration) :
    ProgramPGlobalDenseOperatorCore4D period hPeriod configuration data →ₗ[Real]
      ProgramPGlobalAnalysisHilbert4D period hPeriod configuration data where
  toFun := fun state =>
    (state.1,
      ((fun sector => (state.2.1 sector).1),
        (state.2.2.1.1,
          llH1SmoothEmbedding period hPeriod
            (data.llH1Data period hPeriod) state.2.2.2)))
  map_add' := by
    intro first second
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext sector
        apply Subtype.ext
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · exact map_add
            (llH1SmoothEmbedding period hPeriod
              (data.llH1Data period hPeriod)) _ _
  map_smul' := by
    intro scalar state
    apply Prod.ext
    · simp
    · apply Prod.ext
      · funext sector
        apply Subtype.ext
        simp
      · apply Prod.ext
        · apply Subtype.ext
          simp
        · simpa using map_smul
            (llH1SmoothEmbedding period hPeriod
              (data.llH1Data period hPeriod)) scalar state.2.2.2

theorem programPGlobalDenseOperatorCoreInclusion_injective
    (configuration : GlobalFieldConfiguration period hPeriod)
    (data : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (programPGlobalDenseOperatorCoreInclusion
        period hPeriod configuration data) := by
  intro first second hEqual
  apply Prod.ext
  · exact congrArg
      (fun state :
        ProgramPGlobalAnalysisHilbert4D
          period hPeriod configuration data => state.1) hEqual
  · apply Prod.ext
    · funext sector
      apply Subtype.ext
      exact congrFun (congrArg (fun state => state.2.1) hEqual) sector
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun state => state.2.2.1) hEqual
      · apply UniformSpace.Completion.coe_injective
        exact congrArg (fun state => state.2.2.2) hEqual

theorem programPGlobalDenseOperatorCoreInclusion_denseRange
    (configuration : GlobalFieldConfiguration period hPeriod)
    (data : GlobalAnalysisData period hPeriod configuration) :
    DenseRange
      (programPGlobalDenseOperatorCoreInclusion
        period hPeriod configuration data) := by
  have hBulk :
      DenseRange
        (fun state : GlobalBulkDirichletHilbertH1 period hPeriod => state) :=
    denseRange_id
  have hSpinCOne :
      DenseRange
        (fun state : PrimitiveSpinCGeometricH2 period hPeriod =>
          (state.1 : PrimitiveSpinCGeometricL2)) := by
    change Dense
      (Set.range
        (fun state : PrimitiveSpinCGeometricH2 period hPeriod =>
          (state.1 : PrimitiveSpinCGeometricL2)))
    rw [show
      Set.range
          (fun state : PrimitiveSpinCGeometricH2 period hPeriod =>
            (state.1 : PrimitiveSpinCGeometricL2)) =
        (PrimitiveSpinCGeometricH2 period hPeriod :
          Set PrimitiveSpinCGeometricL2) by
      ext state
      constructor
      · rintro ⟨source, rfl⟩
        exact source.2
      · intro hState
        exact ⟨⟨state, hState⟩, rfl⟩]
    exact primitiveSpinCGeometricH2_dense period hPeriod
  have hSpinC :
      DenseRange
        (Pi.map fun _ : Sector =>
          (fun state : PrimitiveSpinCGeometricH2 period hPeriod =>
            (state.1 : PrimitiveSpinCGeometricL2))) :=
    DenseRange.piMap fun _ => hSpinCOne
  have hD10 :
      DenseRange
        (fun state :
            programPD10FredholmModeDomainSubmodule4D
              (d10SpectralData period hPeriod configuration.d10Completion) =>
          state.1) := by
    change Dense
      (Set.range
        (fun state :
            programPD10FredholmModeDomainSubmodule4D
              (d10SpectralData period hPeriod configuration.d10Completion) =>
          state.1))
    rw [show
      Set.range
          (fun state :
              programPD10FredholmModeDomainSubmodule4D
                (d10SpectralData period hPeriod
                  configuration.d10Completion) =>
            state.1) =
        programPD10FredholmModeDomain4D
          (d10SpectralData period hPeriod configuration.d10Completion) by
      ext state
      constructor
      · rintro ⟨source, rfl⟩
        exact source.2
      · intro hState
        exact ⟨⟨state, hState⟩, rfl⟩]
    exact programPD10FredholmModeDomain4D_dense
      (d10SpectralData period hPeriod configuration.d10Completion)
  have hLL :
      DenseRange
        (llH1SmoothEmbedding period hPeriod
          (data.llH1Data period hPeriod)) :=
    llH1SmoothEmbedding_denseRange period hPeriod
      (data.llH1Data period hPeriod)
  have hProduct :=
    hBulk.prodMap (hSpinC.prodMap (hD10.prodMap hLL))
  have hFunction :
      (programPGlobalDenseOperatorCoreInclusion
          period hPeriod configuration data :
        ProgramPGlobalDenseOperatorCore4D
            period hPeriod configuration data →
          ProgramPGlobalAnalysisHilbert4D
            period hPeriod configuration data) =
        Prod.map (fun state => state)
          (Prod.map
            (Pi.map fun _ : Sector =>
              (fun state : PrimitiveSpinCGeometricH2 period hPeriod =>
                (state.1 : PrimitiveSpinCGeometricL2)))
            (Prod.map
              (fun state :
                  programPD10FredholmModeDomainSubmodule4D
                    (d10SpectralData period hPeriod
                      configuration.d10Completion) =>
                state.1)
              (llH1SmoothEmbedding period hPeriod
                (data.llH1Data period hPeriod)))) := by
    funext state
    rfl
  rw [hFunction]
  exact hProduct

/-- All already constructed, unconditional pieces of the global analytic
spine. -/
structure ProgramPGlobalAnalyticSpineCertificate4D
    (configuration : GlobalFieldConfiguration period hPeriod) : Prop where
  completeVariationCore :
    Nonempty
      (ProgramPCompleteVariationConstructedCoreCertificate4D
        period hPeriod (Equiv.refl MatterFiber))
  d10ProjectionSurjective :
    Function.Surjective
      (globalFieldTangentD10CoordinateLinearMap
        period hPeriod (configuration := configuration))
  d10SectionInjective :
    Function.Injective
      (globalFieldTangentD10SectionLinearMap
        period hPeriod (configuration := configuration))
  commonHilbertCore :
    ∀ data : GlobalAnalysisData period hPeriod configuration,
      Function.Injective
        (programPGlobalDenseOperatorCoreInclusion
          period hPeriod configuration data) ∧
      DenseRange
        (programPGlobalDenseOperatorCoreInclusion
          period hPeriod configuration data)
  allLevelSpinCCoefficientTower :
    Nonempty
      (ProgramPPrimitiveSpinCGeometricSpectralCertificate4D
        period hPeriod)
  d10Fredholm :
    ∀ data : GlobalAnalysisData period hPeriod configuration,
      ProgramPD10FredholmCertificate4D
        (d10SpectralData period hPeriod configuration.d10Completion)
  llRieszCore :
    ∀ data : GlobalAnalysisData period hPeriod configuration,
      DenseRange
          (strongLLJacobiH1Operator period hPeriod
            (data.llH1Data period hPeriod)) ∧
        ∀ direction,
          strongLLJacobiH1Operator period hPeriod
              (data.llH1Data period hPeriod) direction = 0 ↔
            direction = 0
  commonClosedDomainInhabited :
    ∀ data : GlobalAnalysisData period hPeriod configuration,
      Nonempty (GlobalCommonClosedDomain period hPeriod data)

/-- The global algebraic/Sobolev/D10 spine is constructed without a residual
agreement assumption. -/
theorem programPGlobalAnalyticSpineCertificate4D
    (configuration : GlobalFieldConfiguration period hPeriod) :
    ProgramPGlobalAnalyticSpineCertificate4D
      period hPeriod configuration where
  completeVariationCore :=
    programPCompleteVariationConstructedCore_nonempty period hPeriod
  d10ProjectionSurjective :=
    globalFieldTangentD10Coordinate_surjective period hPeriod
  d10SectionInjective :=
    globalFieldTangentD10Section_injective period hPeriod
  commonHilbertCore := fun data =>
    ⟨programPGlobalDenseOperatorCoreInclusion_injective
        period hPeriod configuration data,
      programPGlobalDenseOperatorCoreInclusion_denseRange
        period hPeriod configuration data⟩
  allLevelSpinCCoefficientTower :=
    ⟨programPPrimitiveSpinCGeometricSpectralCertificate4D
      period hPeriod⟩
  d10Fredholm := fun _ =>
    programPD10FredholmCertificate4D
      (d10SpectralData period hPeriod configuration.d10Completion)
  llRieszCore := fun data =>
    ⟨strongLLJacobiH1Operator_denseDomain period hPeriod
        (data.llH1Data period hPeriod),
      strongLLJacobiH1Operator_kernel period hPeriod
        (data.llH1Data period hPeriod)⟩
  commonClosedDomainInhabited :=
    globalCommonClosedDomain_nonempty period hPeriod

/-- Exact missing chart input: the genuine smooth tangent is a dense,
injective core of the regular normed variational chart at the same physical
configuration. -/
structure ProgramPGlobalVariationalChartCoreBridge4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalFieldConfiguration period hPeriod)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) where
  baseConfiguration : chart.Configuration
  baseConfiguration_fields :
    chart.family.configurationAt baseConfiguration = configuration
  tangentAnalysis :
    GlobalFieldTangent period hPeriod configuration →ₗ[Real]
      chart.Configuration
  tangentAnalysis_injective : Function.Injective tangentAnalysis
  tangentAnalysis_denseRange : DenseRange tangentAnalysis

/-- Independent geometric Fourier residual.  It is intentionally not folded
into the D10 projection, which is already a constructed direct factor. -/
abbrev ProgramPGlobalSpinCGeometricFourierContract4D :=
  ProgramPD9PrimitiveSpinCGeometricFourierRealization4D period hPeriod

end
end P0EFTJanusProgramPGlobalAnalyticSpine4D
end JanusFormal
