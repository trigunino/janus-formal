import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCompleteVariationConstructedCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalysisDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricFourierBridge4D

/-!
# Constructed global analytic spine and exact residual bridges

The global tangent already contains the D10 Hilbert coordinate as a direct
factor.  Consequently its D10 projection has a canonical linear section; no
equivalence between all smooth fields and one spectral sector is needed.

The remaining Hessian problem is split into two honest inputs:

* a dense injective analysis of the genuine smooth global tangent into a
  regular variational chart;
* the geometric Fourier realization of the primitive SpinC smooth core.
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
open P0EFTJanusProgramPMultiplicityAwareD10Galerkin4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

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
