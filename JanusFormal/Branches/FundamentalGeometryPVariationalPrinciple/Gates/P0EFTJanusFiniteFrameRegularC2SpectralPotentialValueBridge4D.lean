import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2CanonicalVolumeDerivativeBridge4D

/-! # Finite-frame/regular bridge for the central spectral potential -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2SpectralPotentialValueBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 4000

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotential4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusFiniteFrameIntrinsicSpectralPotential4D
open P0EFTJanusFiniteFrameC2SpectralInteraction4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusPairedInteractionRecenterValue4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

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
local instance (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

/-- At the paired center, the finite-frame potential is exactly the regular
four-dimensional matrix spectral potential. -/
theorem pairedFiniteFrameC2SpectralPotential_zero_regular_valueAt
    (coefficients : PotentialCoefficients)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hFiniteRegular
          coefficients 0) point =
      matrixSpectralPotential coefficients
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase 0) point) := by
  dsimp only
  rw [pairedFiniteFrameC2SpectralPotential_zero_valueAt period hPeriod frame
    (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
    (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
      plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
    coefficients point (regularMetricBasisAt period hPeriod plusBase point)]
  apply congrArg (matrixSpectralPotential coefficients)
  change
    (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart).rootMatrixAt
        period hPeriod point (regularMetricBasisAt period hPeriod plusBase point) = _
  rw [regularGeneralMetricC2LorentzChartGeometry_rootMatrixAt_regularMetricBasis]
  unfold regularGeneralMetricC2PairedRelativeRoot
  rw [pairedInteractionRelativeMatrix_zero]
  rfl

end
end P0EFTJanusFiniteFrameRegularC2SpectralPotentialValueBridge4D
end JanusFormal
