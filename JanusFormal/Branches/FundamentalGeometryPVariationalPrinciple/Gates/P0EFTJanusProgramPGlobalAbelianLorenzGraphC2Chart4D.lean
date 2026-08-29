import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D

/-!
# Global Abelian Lorenz graph C2 chart

The Lorenz graph completion is used as a global linear Hilbert chart.  Its
quadratic gauge action is smooth, and its first and second Frechet derivatives
are the existing bounded Lorenz form and Riesz representative.  On the dense
smooth core the Hessian is exactly the reduced on-shell BRST polarization.

For Candidate A the same intrinsic smooth potentials inject simultaneously
into this graph chart and into the corrected minimal physical tangent.  This
does not construct the still-missing total gauge-fixed chart, a Green formula,
or a Fredholm realization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalAbelianLorenzGraphC2Chart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D

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

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance globalPairedAbelianLorenzGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric)
    ).toNormedSpace

local instance globalPairedAbelianLorenzGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric)
    ).toNormedSpace.toModule

/-- Constant bounded Hessian form on the global Lorenz graph chart. -/
def globalPairedAbelianLorenzGraphHessian
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric →L[Real]
        Real :=
  (innerSL Real).bilinearComp
    (globalPairedAbelianLorenzFeatureProjection period hPeriod metric)
    (globalPairedAbelianLorenzFeatureProjection period hPeriod metric)

@[simp]
theorem globalPairedAbelianLorenzGraphHessian_apply
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :
    globalPairedAbelianLorenzGraphHessian period hPeriod metric first second =
      inner Real
        (globalPairedAbelianLorenzFeatureProjection period hPeriod metric first)
        (globalPairedAbelianLorenzFeatureProjection period hPeriod metric
          second) :=
  rfl

theorem globalPairedAbelianLorenzGraphHessian_comm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :
    globalPairedAbelianLorenzGraphHessian period hPeriod metric first second =
      globalPairedAbelianLorenzGraphHessian period hPeriod metric second first :=
  by
    rw [globalPairedAbelianLorenzGraphHessian_apply,
      globalPairedAbelianLorenzGraphHessian_apply]
    exact real_inner_comm _ _

/-- The graph Hessian is represented by the already constructed `P†P`. -/
theorem globalPairedAbelianLorenzGraphHessian_eq_rieszPairing
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :
    globalPairedAbelianLorenzGraphHessian period hPeriod metric first second =
      inner Real
        (globalPairedAbelianLorenzGraphRieszOperator
          period hPeriod metric first) second := by
  rw [globalPairedAbelianLorenzGraphHessian_apply,
    globalPairedAbelianLorenzGraphRieszOperator_pairing]

/-- Quadratic Lorenz gauge action on its faithful graph completion. -/
def globalPairedAbelianLorenzGraphAction
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :
    Real :=
  (1 / 2 : Real) *
    globalPairedAbelianLorenzGraphHessian
      period hPeriod metric state state

private theorem symmetricQuadratic_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second,
      bilinear first second = bilinear second first)
    (point : E) :
    HasFDerivAt (fun state => (1 / 2 : Real) * bilinear state state)
      (bilinear point) point := by
  have hDiagonal :=
    (bilinear.hasFDerivAt (x := point)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) point)
  have hHalf := hDiagonal.const_mul (1 / 2 : Real)
  apply hHalf.congr_fderiv
  ext direction
  change (1 / 2 : Real) *
      (bilinear point direction + bilinear direction point) =
    bilinear point direction
  rw [hSymmetric direction point]
  ring

/-- The displayed graph action has the Lorenz form as first derivative. -/
theorem globalPairedAbelianLorenzGraphAction_hasFDerivAt
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :
    HasFDerivAt
      (globalPairedAbelianLorenzGraphAction period hPeriod metric)
      (globalPairedAbelianLorenzGraphHessian period hPeriod metric state)
      state :=
  symmetricQuadratic_hasFDerivAt
    (globalPairedAbelianLorenzGraphHessian period hPeriod metric)
    (globalPairedAbelianLorenzGraphHessian_comm period hPeriod metric)
    state

theorem globalPairedAbelianLorenzGraphAction_fderiv
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :
    fderiv Real
        (globalPairedAbelianLorenzGraphAction period hPeriod metric) state =
      globalPairedAbelianLorenzGraphHessian
        period hPeriod metric state :=
  (globalPairedAbelianLorenzGraphAction_hasFDerivAt
    period hPeriod metric state).fderiv

/-- The genuine second Frechet derivative is the constant Lorenz Hessian. -/
theorem globalPairedAbelianLorenzGraphAction_second_fderiv
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (base : GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :
    fderiv Real
        (fun state => fderiv Real
          (globalPairedAbelianLorenzGraphAction period hPeriod metric) state)
        base =
      globalPairedAbelianLorenzGraphHessian period hPeriod metric := by
  rw [show
      (fun state => fderiv Real
        (globalPairedAbelianLorenzGraphAction period hPeriod metric) state) =
      (fun state =>
        globalPairedAbelianLorenzGraphHessian
          period hPeriod metric state) from by
    funext state
    exact globalPairedAbelianLorenzGraphAction_fderiv
      period hPeriod metric state]
  exact ContinuousLinearMap.fderiv
    (𝕜 := Real)
    (E := GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric)
    (F :=
      GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric →L[Real] Real)
    (globalPairedAbelianLorenzGraphHessian period hPeriod metric)

/-- The graph action is in fact smooth, hence in particular `C2`. -/
theorem globalPairedAbelianLorenzGraphAction_contDiff
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real ⊤
      (globalPairedAbelianLorenzGraphAction period hPeriod metric) := by
  unfold globalPairedAbelianLorenzGraphAction
  exact contDiff_const.mul
    ((globalPairedAbelianLorenzGraphHessian period hPeriod metric
      ).contDiff.clm_apply contDiff_id)

theorem globalPairedAbelianLorenzGraphAction_contDiff_two
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (globalPairedAbelianLorenzGraphAction period hPeriod metric) :=
  (globalPairedAbelianLorenzGraphAction_contDiff
    period hPeriod metric).of_le (by simp)

/-- On the dense smooth core, the actual second derivative is the unchanged
reduced on-shell BRST polarization. -/
theorem globalPairedAbelianLorenzGraphAction_second_fderiv_smooth_eq_BRST
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (base : GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric)
    (first second : GlobalPairedAbelianPotentialSmooth period hPeriod) :
    fderiv Real
        (fun state => fderiv Real
          (globalPairedAbelianLorenzGraphAction period hPeriod metric) state)
        base
        (globalPairedAbelianLorenzSmoothEmbedding
          period hPeriod metric first)
        (globalPairedAbelianLorenzSmoothEmbedding
          period hPeriod metric second) =
      globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric
        (globalPairedAbelianLorenzOnShellState
          period hPeriod metric first)
        (globalPairedAbelianLorenzOnShellState
          period hPeriod metric second)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [globalPairedAbelianLorenzGraphAction_second_fderiv]
  exact globalPairedAbelianLorenzFeature_inner_eq_BRST
    period hPeriod metric first second

/-! ## Common smooth core with the corrected physical tangent -/

/-- The common intrinsic smooth core mapped both to the Lorenz graph chart
and to the corrected minimal physical tangent. -/
def globalCandidateALorenzPhysicalCoreLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    GlobalPairedAbelianPotentialSmooth period hPeriod →ₗ[Real]
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) ×
        GlobalMinimalPhysicalFieldTangent
          period hPeriod configuration) where
  toFun potential :=
    (globalPairedAbelianLorenzSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) potential,
      globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
        period hPeriod data potential)
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalPairedAbelianLorenzSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          ).map_add first second
    · exact
        (globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
          period hPeriod data).map_add first second
  map_smul' scalar potential := by
    apply Prod.ext
    · exact
        (globalPairedAbelianLorenzSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          ).map_smul scalar potential
    · exact
        (globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
          period hPeriod data).map_smul scalar potential

theorem globalCandidateALorenzPhysicalCoreLinearMap_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    Function.Injective
      (globalCandidateALorenzPhysicalCoreLinearMap period hPeriod data) := by
  intro first second hEqual
  apply globalPairedAbelianLorenzSmoothEmbedding_injective
    period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
  exact congrArg Prod.fst hEqual

end
end P0EFTJanusProgramPGlobalAbelianLorenzGraphC2Chart4D
end JanusFormal
