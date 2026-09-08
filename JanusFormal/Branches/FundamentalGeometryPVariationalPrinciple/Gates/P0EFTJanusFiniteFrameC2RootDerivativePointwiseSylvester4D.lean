import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2SpectralPotentialDerivativeAtCenter4D

/-! # Pointwise Sylvester equation for the finite-frame root derivative -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2RootDerivativePointwiseSylvester4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 4000

noncomputable section

open scoped Manifold ContDiff Topology Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFramePairedRelativeC2RootDerivativeAtCenter4D
open P0EFTJanusFiniteFramePairedRelativeC2TargetDerivativeAtCenter4D
open P0EFTJanusFiniteFrameC2SpectralPotentialDerivativeAtCenter4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
@[reducible] local instance : NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup
@[reducible] local instance : NormedSpace Real Matrix4 :=
  Matrix.frobeniusNormedSpace
local instance : CompleteSpace Matrix4 :=
  FiniteDimensional.complete Real Matrix4
local instance (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup (C2FiniteFrameCorner period hPeriod frame metric) :=
  (c2FiniteFrameCornerSubmodule period hPeriod frame metric).normedAddCommGroup
local instance (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (C2FiniteFrameCorner period hPeriod frame metric) := inferInstance
local instance (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod frame metric).normedAddCommGroup
local instance (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (GeneralMetricRelativeC2Core period hPeriod frame metric) := inferInstance

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (frame : SmoothD8Frame period hPeriod)
  (hRegular : ∀ point, Function.Bijective
    (intrinsicCandidateASylvesterAt period hPeriod geometry point))

private abbrev Model :=
  PairedFiniteFrameMetricC2Core period hPeriod geometry frame

/-- Pointwise intrinsic matrix of the derivative of the paired relative
target at the center. -/
def pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    Model period hPeriod geometry frame →L[Real] Matrix4 :=
  (finiteFrameC2CornerMatrixAtCLM
      period hPeriod geometry frame point basis).comp
    (pairedFiniteFrameRelativeC2TargetDerivativeAtZero
      period hPeriod geometry frame)

@[simp]
theorem pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero_apply
    (direction : Model period hPeriod geometry frame)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero
        period hPeriod geometry frame point basis direction =
      LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
          (c2FiniteMatrixValueAt period hPeriod frame.count
            (-c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
                direction.1.1
                (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric
                  (c2GlobalCandidateAFiniteFrameRootCorner
                    period hPeriod geometry frame)).1 +
              direction.2.1) point)).toLinearMap := by
  change finiteFrameC2CornerMatrixAtCLM period hPeriod geometry frame point basis
      (pairedFiniteFrameRelativeC2TargetDerivativeAtZero
        period hPeriod geometry frame direction) = _
  rw [pairedFiniteFrameRelativeC2TargetDerivativeAtZero_apply,
    finiteFrameC2CornerMatrixAtCLM_projection]

/-- The decoded finite root velocity satisfies the ordinary pointwise
four-dimensional Sylvester equation. -/
theorem pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero_sylvester
    (direction : Model period hPeriod geometry frame)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap *
          pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero
            period hPeriod geometry frame hRegular point basis direction +
        pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero
            period hPeriod geometry frame hRegular point basis direction *
          LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap =
      pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero
        period hPeriod geometry frame point basis direction := by
  have hFinite := congrArg
    (fun value => finiteFrameC2CornerMatrixAtCLM
      period hPeriod geometry frame point basis value)
    (pairedFiniteFrameMetricC2RootDerivativeAtZero_sylvester
      period hPeriod geometry frame hRegular direction)
  rw [finiteFrameC2CornerMatrixAtCLM_sylvester,
    finiteFrameC2CornerMatrixAtCLM_candidateRoot] at hFinite
  exact hFinite

/-- Expanded pointwise Sylvester equation, with the redundant projection
removed by intrinsic decoding. -/
theorem pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero_sylvester_explicit
    (direction : Model period hPeriod geometry frame)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentSpace coverModelWithCorners point)) :
    LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap *
          pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero
            period hPeriod geometry frame hRegular point basis direction +
        pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero
            period hPeriod geometry frame hRegular point basis direction *
          LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap =
      LinearMap.toMatrix basis basis
        (finiteFrameMatrixDecodeAt period hPeriod frame geometry.plusMetric point
          (c2FiniteMatrixValueAt period hPeriod frame.count
            (-c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
                direction.1.1
                (c2FiniteFrameCornerSquare period hPeriod frame geometry.plusMetric
                  (c2GlobalCandidateAFiniteFrameRootCorner
                    period hPeriod geometry frame)).1 +
              direction.2.1) point)).toLinearMap := by
  rw [pairedFiniteFrameMetricC2RootMatrixDerivativeAtZero_sylvester,
    pairedFiniteFrameRelativeC2TargetMatrixDerivativeAtZero_apply]

end
end P0EFTJanusFiniteFrameC2RootDerivativePointwiseSylvester4D
end JanusFormal
