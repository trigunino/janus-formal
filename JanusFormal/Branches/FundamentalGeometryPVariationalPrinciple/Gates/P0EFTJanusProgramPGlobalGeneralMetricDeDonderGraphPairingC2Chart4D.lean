import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D

/-!
# C² chart for the exact global de Donder pairing graph

The refined faithful graph carries the bounded symmetric Hessian constructed
from the exact Lorentzian inverse-metric pairing.  Its quadratic action is
smooth, and its genuine second Fréchet derivative restricts on the dense
smooth core to the original integrated de Donder gauge block.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairingC2Chart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonderGaugePairing4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D

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

local instance baseGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)).toNormedSpace

local instance baseGraphModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)).toNormedSpace.toModule

local instance pairingGraphAmbientNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric)).toNormedSpace

local instance pairingGraphAmbientModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric)).toNormedSpace.toModule

local instance pairingGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)).toNormedSpace

local instance pairingGraphModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)).toNormedSpace.toModule

private def globalGeneralMetricDeDonderPairingC2CrossForm
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (innerSL Real :
    GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
        Real).bilinearComp
    (𝕜₁' := Real) (𝕜₂' := Real)
    (E' :=
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)
    (F' :=
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)
    (globalGeneralMetricDeDonderPairingFeatureProjection
      period hPeriod metric)
    (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
      period hPeriod metric)

private def globalGeneralMetricDeDonderPairingC2ReverseCrossForm
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (innerSL Real :
    GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
        Real).bilinearComp
    (𝕜₁' := Real) (𝕜₂' := Real)
    (E' :=
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)
    (F' :=
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)
    (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
      period hPeriod metric)
    (globalGeneralMetricDeDonderPairingFeatureProjection
      period hPeriod metric)

/-- Calculus-facing representative of the already constructed bounded
Hessian.  It uses the local chart instances and agrees pointwise with the
graph Hessian. -/
def globalGeneralMetricDeDonderPairingC2Hessian
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (1 / 2 : Real) •
    (globalGeneralMetricDeDonderPairingC2CrossForm
        period hPeriod metric +
      globalGeneralMetricDeDonderPairingC2ReverseCrossForm
        period hPeriod metric)

@[simp]
theorem globalGeneralMetricDeDonderPairingC2Hessian_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :
    globalGeneralMetricDeDonderPairingC2Hessian
        period hPeriod metric first second =
      (1 / 2 : Real) *
        (inner Real
            (globalGeneralMetricDeDonderPairingFeatureProjection
              period hPeriod metric first)
            (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
              period hPeriod metric second) +
          inner Real
            (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
              period hPeriod metric first)
            (globalGeneralMetricDeDonderPairingFeatureProjection
              period hPeriod metric second)) := by
  simp [globalGeneralMetricDeDonderPairingC2Hessian,
    globalGeneralMetricDeDonderPairingC2CrossForm,
    globalGeneralMetricDeDonderPairingC2ReverseCrossForm]
  ring

theorem globalGeneralMetricDeDonderPairingC2Hessian_eq_graphHessian
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :
    globalGeneralMetricDeDonderPairingC2Hessian
        period hPeriod metric first second =
      globalGeneralMetricDeDonderPairingGraphHessian
        period hPeriod metric first second := by
  rw [globalGeneralMetricDeDonderPairingC2Hessian_apply,
    globalGeneralMetricDeDonderPairingGraphHessian_apply]

theorem globalGeneralMetricDeDonderPairingC2Hessian_comm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :
    globalGeneralMetricDeDonderPairingC2Hessian
        period hPeriod metric first second =
      globalGeneralMetricDeDonderPairingC2Hessian
        period hPeriod metric second first := by
  rw [globalGeneralMetricDeDonderPairingC2Hessian_apply,
    globalGeneralMetricDeDonderPairingC2Hessian_apply]
  rw [real_inner_comm
      (globalGeneralMetricDeDonderPairingFeatureProjection
        period hPeriod metric first),
    real_inner_comm
      (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
        period hPeriod metric first)]
  ring

theorem globalGeneralMetricDeDonderPairingC2Hessian_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderPairingC2Hessian
        period hPeriod metric
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod metric first)
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod metric second) =
      globalGeneralMetricDeDonderGaugePairingValue
        period hPeriod metric first second := by
  rw [globalGeneralMetricDeDonderPairingC2Hessian_eq_graphHessian]
  exact globalGeneralMetricDeDonderPairingGraphHessian_smooth
    period hPeriod metric first second

/-- Quadratic de Donder gauge action on the refined faithful graph. -/
def globalGeneralMetricDeDonderPairingGraphAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state :
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) : Real :=
  (1 / 2 : Real) *
    globalGeneralMetricDeDonderPairingC2Hessian
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

theorem globalGeneralMetricDeDonderPairingGraphAction_hasFDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state :
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :
    HasFDerivAt
      (globalGeneralMetricDeDonderPairingGraphAction
        period hPeriod metric)
      (globalGeneralMetricDeDonderPairingC2Hessian
        period hPeriod metric state)
      state := by
  exact @symmetricQuadratic_hasFDerivAt
    (GlobalGeneralMetricDeDonderPairingGraphHilbert
      period hPeriod metric)
    inferInstance
    (pairingGraphNormedSpace period hPeriod metric)
    (globalGeneralMetricDeDonderPairingC2Hessian
      period hPeriod metric)
    (globalGeneralMetricDeDonderPairingC2Hessian_comm
      period hPeriod metric)
    state

theorem globalGeneralMetricDeDonderPairingGraphAction_fderiv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state :
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :
    fderiv Real
        (globalGeneralMetricDeDonderPairingGraphAction
          period hPeriod metric) state =
      globalGeneralMetricDeDonderPairingC2Hessian
        period hPeriod metric state :=
  (globalGeneralMetricDeDonderPairingGraphAction_hasFDerivAt
    period hPeriod metric state).fderiv

theorem globalGeneralMetricDeDonderPairingGraphAction_second_fderiv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (base :
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :
    fderiv Real
        (fun state => fderiv Real
          (globalGeneralMetricDeDonderPairingGraphAction
            period hPeriod metric) state)
        base =
      globalGeneralMetricDeDonderPairingC2Hessian
        period hPeriod metric := by
  rw [show
      (fun state => fderiv Real
        (globalGeneralMetricDeDonderPairingGraphAction
          period hPeriod metric) state) =
      (fun state =>
        globalGeneralMetricDeDonderPairingC2Hessian
          period hPeriod metric state) from by
    funext state
    exact globalGeneralMetricDeDonderPairingGraphAction_fderiv
      period hPeriod metric state]
  exact ContinuousLinearMap.fderiv
    (𝕜 := Real)
    (E :=
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)
    (F :=
      GlobalGeneralMetricDeDonderPairingGraphHilbert
          period hPeriod metric →L[Real] Real)
    (globalGeneralMetricDeDonderPairingC2Hessian
      period hPeriod metric)

theorem globalGeneralMetricDeDonderPairingGraphAction_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real ⊤
      (globalGeneralMetricDeDonderPairingGraphAction
        period hPeriod metric) := by
  unfold globalGeneralMetricDeDonderPairingGraphAction
  have hHessian :
      ContDiff Real ⊤
        (globalGeneralMetricDeDonderPairingC2Hessian
          period hPeriod metric) :=
    @ContinuousLinearMap.contDiff
      Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
          period hPeriod metric →L[Real] Real)
      inferInstance
      inferInstance
      (pairingGraphNormedSpace period hPeriod metric)
      inferInstance
      inferInstance
      ⊤
      (globalGeneralMetricDeDonderPairingC2Hessian
        period hPeriod metric)
  have hIdentity :
      ContDiff Real ⊤
        (id :
          GlobalGeneralMetricDeDonderPairingGraphHilbert
              period hPeriod metric →
            GlobalGeneralMetricDeDonderPairingGraphHilbert
              period hPeriod metric) :=
    @contDiff_id
      Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)
      inferInstance
      inferInstance
      (pairingGraphNormedSpace period hPeriod metric)
      ⊤
  have hDiagonal :
      ContDiff Real ⊤
        (fun state =>
          globalGeneralMetricDeDonderPairingC2Hessian
            period hPeriod metric state state) :=
    @ContDiff.clm_apply
      Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)
      Real
      inferInstance
      inferInstance
      (pairingGraphNormedSpace period hPeriod metric)
      inferInstance
      (pairingGraphNormedSpace period hPeriod metric)
      inferInstance
      inferInstance
      ⊤
      (globalGeneralMetricDeDonderPairingC2Hessian
        period hPeriod metric)
      id
      hHessian
      hIdentity
  exact contDiff_const.mul hDiagonal

theorem globalGeneralMetricDeDonderPairingGraphAction_contDiff_two
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (globalGeneralMetricDeDonderPairingGraphAction
        period hPeriod metric) :=
  (globalGeneralMetricDeDonderPairingGraphAction_contDiff
    period hPeriod metric).of_le (by simp)

/-- The genuine second Fréchet derivative restricts to the original smooth
gauge Hessian, with no change of density or pairing. -/
theorem globalGeneralMetricDeDonderPairingGraphAction_second_fderiv_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (base :
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)
    (first second :
      SmoothSymmetricCovariantTwoTensor period hPeriod) :
    fderiv Real
        (fun state => fderiv Real
          (globalGeneralMetricDeDonderPairingGraphAction
            period hPeriod metric) state)
        base
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod metric first)
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod metric second) =
      globalGeneralMetricDeDonderGaugePairingValue
        period hPeriod metric first second := by
  rw [globalGeneralMetricDeDonderPairingGraphAction_second_fderiv]
  exact globalGeneralMetricDeDonderPairingC2Hessian_smooth
    period hPeriod metric first second

end
end P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairingC2Chart4D
end JanusFormal
