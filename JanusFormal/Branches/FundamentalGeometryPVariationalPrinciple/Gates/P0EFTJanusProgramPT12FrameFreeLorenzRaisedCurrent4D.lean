import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LorenzRaisedCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeCurrentPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowFrame4D

/-! The raised Lorenz current uses the ten smooth generators, without a global tangent basis. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeLorenzRaisedCurrent4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusAbelianLorenzCodifferentialTransition4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameLorenzCovariantTrace4D
open P0EFTJanusEffectiveD8SmoothInverseMusical4D
open P0EFTJanusProgramPT12FrameFreeCurrentPullback4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Vector4 := Fin 4 → Real
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

def frameFreeLorenzRaisedCurrent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2) :
    SmoothTangentField period hPeriod where
  toFun := fun point => ∑ index : Fin 10,
    finiteFramePotentialCoefficient period hPeriod
        (canonicalTenFlowFrame period hPeriod) potential component index point •
      effectiveD8SmoothInverseMusical ⟨period, hPeriod⟩ metric
        (finiteFrameDualCovector period hPeriod
          (canonicalTenFlowFrame period hPeriod) metric index) point
  contMDiff_toFun := by
    apply ContMDiff.sum_section
    intro index _
    exact (finiteFramePotentialCoefficient period hPeriod
      (canonicalTenFlowFrame period hPeriod) potential component index).contMDiff_toFun.smul_section
      (effectiveD8SmoothInverseMusical ⟨period, hPeriod⟩ metric
        (finiteFrameDualCovector period hPeriod
          (canonicalTenFlowFrame period hPeriod) metric index)).contMDiff

theorem frameFreeLorenzRaisedCurrent_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    frameFreeLorenzRaisedCurrent period hPeriod metric potential component point =
      inverseMetricSharp period hPeriod metric point (potential.toFun component point) := by
  simp only [frameFreeLorenzRaisedCurrent, finiteFramePotentialCoefficient_apply,
    effectiveD8SmoothInverseMusical_apply, finiteFrameDualCovector_apply]
  have h := congrArg (inverseMetricSharp period hPeriod metric point)
    (finiteFrameCovector_reconstructs period hPeriod
      (canonicalTenFlowFrame period hPeriod) metric point (potential.toFun component point))
  simp only [map_sum, map_smul] at h
  exact h.symm

theorem frameFreeLorenzRaisedCurrent_pullback
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    frameFreeCurrentPullback period hPeriod patch
        (frameFreeLorenzRaisedCurrent period hPeriod metric potential component) coordinate =
      localRaisedAbelianGaugePotential period hPeriod metric potential component patch coordinate := by
  apply (frameFreeCoordinateDerivativeEquiv period hPeriod patch coordinate).injective
  have hFirst := frameFreeCurrentPullback_pushforward period hPeriod patch
    (frameFreeLorenzRaisedCurrent period hPeriod metric potential component) coordinate
  have hSecond := coordinateMap_mfderiv_localRaisedAbelianGaugePotential period hPeriod
    metric potential component patch coordinate
  rw [frameFreeLorenzRaisedCurrent_apply] at hFirst
  have h := hFirst.trans hSecond.symm
  rw [← frameFreeCoordinateDerivativeEquiv_coe] at h
  exact h

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeLorenzRaisedCurrent4D
