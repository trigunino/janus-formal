import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothPTFieldAction4D

/-!
# L2 fields and PT on the effective D8 quotient

The compact smooth quotient supports genuine `L2` completions for every finite
Borel measure. Smooth coefficient fields map into that space. If PT preserves
the measure, pullback is an involutive linear isometric equivalence and agrees
with smooth PT pullback. No Sobolev derivative or boundary trace is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusL2PTFunctionalSpace4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D

variable (period : Real) (hPeriod : Not (period = 0))

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) :=
  borel (EffectiveQuotient period hPeriod)

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

universe u

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
  (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]

/-- A smooth quotient field is `L2` for every finite Borel measure because the
actual D8 quotient is compact. -/
theorem smoothQuotientField_memLp
    (field : SmoothQuotientField period hPeriod Fiber) :
    MemLp field.toFun (2 : ENNReal) mu := by
  exact field.contMDiff_toFun.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace field.toFun)

/-- The completed quotient `L2` space is complete. -/
@[implicit_reducible]
def quotientL2CompleteSpace [CompleteSpace Fiber] :
    CompleteSpace (Lp Fiber (2 : ENNReal) mu) :=
  inferInstance

/-- If the coefficient fiber is Hilbert, the quotient `L2` completion is the
corresponding Hilbert space. -/
@[implicit_reducible]
def quotientL2InnerProductSpace [InnerProductSpace Real Fiber]
    [CompleteSpace Fiber] :
    InnerProductSpace Real (Lp Fiber (2 : ENNReal) mu) :=
  inferInstance

/-- The Hilbert `L2` completion is nonempty. -/
theorem quotientL2_nonempty : Nonempty (Lp Fiber (2 : ENNReal) mu) :=
  ⟨0⟩

/-- Canonical inclusion of smooth quotient coefficient fields into `L2`. -/
def smoothFieldToL2
    (field : SmoothQuotientField period hPeriod Fiber) :
    Lp Fiber (2 : ENNReal) mu :=
  (smoothQuotientField_memLp period hPeriod Fiber mu field).toLp field.toFun

theorem smoothFieldToL2_ae
    (field : SmoothQuotientField period hPeriod Fiber) :
    (smoothFieldToL2 period hPeriod Fiber mu field :
      EffectiveQuotient period hPeriod -> Fiber) =ᵐ[mu] field.toFun :=
  (smoothQuotientField_memLp period hPeriod Fiber mu field).coeFn_toLp

/-- A full-support finite Borel measure makes the smooth-to-`L2` map
injective, so no smooth information is lost modulo almost-everywhere equality. -/
theorem smoothFieldToL2_injective [mu.IsOpenPosMeasure] :
    Function.Injective (smoothFieldToL2 period hPeriod Fiber mu) := by
  intro first second hEqual
  apply SmoothQuotientField.ext period hPeriod Fiber
  have hAe : first.toFun =ᵐ[mu] second.toFun := by
    have hMiddle :
        (smoothFieldToL2 period hPeriod Fiber mu first :
          EffectiveQuotient period hPeriod -> Fiber) =ᵐ[mu]
        (smoothFieldToL2 period hPeriod Fiber mu second :
          EffectiveQuotient period hPeriod -> Fiber) := by rw [hEqual]
    exact (smoothFieldToL2_ae period hPeriod Fiber mu first).symm.trans
      (hMiddle.trans (smoothFieldToL2_ae period hPeriod Fiber mu second))
  have hFunctions : first.toFun = second.toFun :=
    ((Continuous.ae_eq_iff_eq mu first.contMDiff_toFun.continuous
      second.contMDiff_toFun.continuous).1 hAe)
  exact fun point => congrFun hFunctions point

variable
  (hPT : MeasurePreserving (reflectedSpherePT period hPeriod) mu mu)

/-- PT pullback on the completed `L2` field space. -/
def ptL2Pullback :
    Lp Fiber (2 : ENNReal) mu →L[Real] Lp Fiber (2 : ENNReal) mu :=
  (Lp.compMeasurePreservingₗᵢ Real
    (reflectedSpherePT period hPeriod) hPT).toContinuousLinearMap

theorem ptL2Pullback_norm
    (field : Lp Fiber (2 : ENNReal) mu) :
    ‖ptL2Pullback period hPeriod Fiber mu hPT field‖ = ‖field‖ :=
  Lp.norm_compMeasurePreserving field hPT

theorem ptL2Pullback_involutive
    (field : Lp Fiber (2 : ENNReal) mu) :
    ptL2Pullback period hPeriod Fiber mu hPT
      (ptL2Pullback period hPeriod Fiber mu hPT field) = field := by
  change Lp.compMeasurePreserving (reflectedSpherePT period hPeriod) hPT
      (Lp.compMeasurePreserving (reflectedSpherePT period hPeriod) hPT field) = field
  rw [← Lp.compMeasurePreserving_comp_apply field hPT hPT]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving field (hPT.comp hPT)]
    with point hPoint
  simpa [Function.comp_def, reflectedSpherePT_involutive] using hPoint

theorem ptL2Pullback_surjective :
    Function.Surjective (ptL2Pullback period hPeriod Fiber mu hPT) := by
  intro field
  exact Exists.intro (ptL2Pullback period hPeriod Fiber mu hPT field)
    (ptL2Pullback_involutive period hPeriod Fiber mu hPT field)

/-- PT is an exact linear isometric equivalence of the global `L2` space. -/
def ptL2Equiv :
    Lp Fiber (2 : ENNReal) mu ≃ₗᵢ[Real] Lp Fiber (2 : ENNReal) mu :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ Real
      (reflectedSpherePT period hPeriod) hPT)
    (ptL2Pullback_surjective period hPeriod Fiber mu hPT)

/-- The `L2` action restricts exactly to the previously constructed smooth PT
pullback; both levels therefore use the same global involution. -/
theorem ptL2Pullback_smoothFieldToL2
    (field : SmoothQuotientField period hPeriod Fiber) :
    ptL2Pullback period hPeriod Fiber mu hPT
        (smoothFieldToL2 period hPeriod Fiber mu field) =
      smoothFieldToL2 period hPeriod Fiber mu
        (ptPullback period hPeriod Fiber field) := by
  change Lp.compMeasurePreserving (reflectedSpherePT period hPeriod) hPT
      ((smoothQuotientField_memLp period hPeriod Fiber mu field).toLp field.toFun) = _
  rw [Lp.toLp_compMeasurePreserving
    (smoothQuotientField_memLp period hPeriod Fiber mu field) hPT]
  rfl

end

end P0EFTJanusMappingTorusL2PTFunctionalSpace4D
end JanusFormal
