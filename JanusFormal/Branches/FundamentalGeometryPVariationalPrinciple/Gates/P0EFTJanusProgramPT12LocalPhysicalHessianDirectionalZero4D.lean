import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D

/-! A locally vanishing physical Euler component annihilates the corresponding
mixed Hessian slot in the same H11 chart. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LocalPhysicalHessianDirectionalZero4D

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- Vanishing of one Euler component on a neighborhood kills every Hessian
pairing in that fixed second slot. The neighborhood condition controls the
mixed derivatives, not merely the second derivative along one line. -/
theorem localPhysicalHessian_second_slot_zero_of_eventually_euler_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain)
    (direction : chart.Model)
    (hEuler :
      (fun state : chart.Model =>
        actionGradient
          (fullCoupledPhysicalAction
            (globalCandidateAActionBlocks period hPeriod
              (chart.family.toActionFamily period hPeriod 0
                chart.zero_mem_domain) measure)) state direction) =ᶠ[𝓝 point]
        fun _ => (0 : Real))
    (other : chart.Model) :
    globalCandidateALocalPhysicalHessian period hPeriod chart point
      other direction = 0 := by
  let blocks := globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain) measure
  let physicalAction := fullCoupledPhysicalAction blocks
  have hC2 : FullCoupledC2At blocks point :=
    fullCoupledC2WithinAt_toAt
      (chart.blocksC2Within point hPoint) chart.isOpen_domain hPoint
  have hPhysicalC2 : ContDiffAt Real 2 physicalAction point :=
    fullCoupledPhysicalAction_contDiffAt blocks point hC2
  have hGradientC1 : ContDiffAt Real 1 (actionGradient physicalAction) point := by
    change ContDiffAt Real 1 (fderiv Real physicalAction) point
    exact hPhysicalC2.fderiv_right (by norm_num)
  have hGradientDiff : DifferentiableAt Real (actionGradient physicalAction) point :=
    hGradientC1.differentiableAt (by norm_num)
  have hEuler' :
      (fun state : chart.Model => actionGradient physicalAction state direction) =ᶠ[𝓝 point]
        fun _ => (0 : Real) := hEuler
  have hZero :
      HasFDerivAt
        (fun state : chart.Model => actionGradient physicalAction state direction)
        (0 : chart.Model →L[Real] Real) point :=
    hasFDerivAt_zero_of_eventually_const (0 : Real) hEuler'
  have hApplied :
      HasFDerivAt
        (fun state : chart.Model => actionGradient physicalAction state direction)
        ((fderiv Real (actionGradient physicalAction) point).flip direction) point := by
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add] using
      hGradientDiff.hasFDerivAt.clm_apply (hasFDerivAt_const direction point)
  have hDerivativeZero := hApplied.unique hZero
  have hAtOther := congrArg (fun linear : chart.Model →L[Real] Real => linear other)
    hDerivativeZero
  simpa only [globalCandidateALocalPhysicalHessian,
    ContinuousLinearMap.flip_apply, zero_apply] using hAtOther

end
end P0EFTJanusProgramPT12LocalPhysicalHessianDirectionalZero4D
end JanusFormal
