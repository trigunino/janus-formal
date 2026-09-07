import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusSmoothIdentityRootVelocity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMobileMaxwellDerivativeRecenter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricInducedSmoothGaugeVelocity4D

/-! # Smooth representative of the genuine off-center gauge transition velocity

Both terms of the completed transition derivative are retained.  The old
root velocity is solved by the smooth inverse Sylvester operator, and the
new frame contributes the negative one-half metric-induced velocity.
-/
namespace JanusFormal
namespace P0EFTJanusSmoothMaxwellRecenterGaugeVelocity4D
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D

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


open P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootJetRigidity4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusMetricInducedSmoothGaugeVelocity4D
open P0EFTJanusSmoothIdentityRootVelocity4D
open P0EFTJanusMobileMaxwellDerivativeRecenter4D
open P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D

private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real
local instance : NormedRing Matrix4 := Matrix.frobeniusNormedRing
local instance : NormedAlgebra Real Matrix4 := Matrix.frobeniusNormedAlgebra
@[reducible] local instance canonicalMatrixNormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance : AddCommGroup Matrix4 := canonicalMatrixNormedAddCommGroup.toAddCommGroup
local instance canonicalMatrixPseudoMetricSpace : PseudoMetricSpace Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toPseudoMetricSpace
local instance canonicalMatrixUniformSpace : UniformSpace Matrix4 :=
  canonicalMatrixPseudoMetricSpace.toUniformSpace
local instance : TopologicalSpace Matrix4 := canonicalMatrixUniformSpace.toTopologicalSpace
@[reducible] local instance canonicalMatrixNormedSpace : NormedSpace Real Matrix4 :=
  NormedAlgebra.toNormedSpace Matrix4
local instance : Module Real Matrix4 := canonicalMatrixNormedSpace.toModule
local instance : CompleteSpace Matrix4 := FiniteDimensional.complete Real Matrix4

/-- The complete smooth packet underlying the transition derivative. -/
def smoothMobileMaxwellRecenterGaugeCoefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    SmoothQuotientField period hPeriod GaugeFiber :=
  let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
  smoothGaugeCoefficientFrameTransport period hPeriod
    (regularGeneralMetricC2IdentityRootInverseMatrixField period hPeriod metric shift hShift)
    (smoothGaugeCoefficientFrameTransport period hPeriod
      (regularGeneralMetricSmoothIdentityRootVelocity period hPeriod metric shift direction hShift)
      coefficients) -
    metricInducedGaugeCoefficients period hPeriod shifted direction
      (regularFrameGaugePotentialFromCoefficients period hPeriod shifted coefficients)

/-- Equality in the full C² core, not only equality of the value fields. -/
theorem smoothMobileMaxwellRecenterGaugeCoefficients_toC2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      (smoothMobileMaxwellRecenterGaugeCoefficients period hPeriod metric shift direction hShift coefficients) =
    mobileMaxwellRecenterGaugeVelocity period hPeriod metric shift direction hShift
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) := by
  let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
  let packet := smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients
  have hInduced := metricInducedGaugeCoefficients_toC2 period hPeriod shifted direction
    (regularFrameGaugePotentialFromCoefficients period hPeriod shifted coefficients)
  rw [gaugePotentialFrameCoefficients_reconstructed] at hInduced
  have hNegative :
      gaugeCoefficientC2CoreFrameTransport period hPeriod
        (-((1 / 2 : Real) • regularGeneralMetricC2VariationMatrix period hPeriod shifted direction)) packet =
      -((1 / 2 : Real) • gaugeCoefficientC2CoreFrameTransport period hPeriod
        (regularGeneralMetricC2VariationMatrix period hPeriod shifted direction) packet) := by
    have h := (gaugeCoefficientC2CoreFrameTransportLeftCLM period hPeriod packet).map_neg
      ((1 / 2 : Real) • regularGeneralMetricC2VariationMatrix period hPeriod shifted direction)
    rw [map_smul] at h
    simpa only [gaugeCoefficientC2CoreFrameTransportLeftCLM_apply] using h
  unfold smoothMobileMaxwellRecenterGaugeCoefficients
  rw [map_sub, ← gaugeCoefficientC2CoreFrameTransport_smooth,
    ← gaugeCoefficientC2CoreFrameTransport_smooth,
    ← regularGeneralMetricC2IdentityRootInverseC2Matrix_eq_smoothMatrixFieldToC2,
    regularGeneralMetricSmoothIdentityRootVelocity_lift]
  rw [hInduced]
  unfold mobileMaxwellRecenterGaugeVelocity
  dsimp only
  rw [hNegative]
  rfl

/-- An actual smooth intrinsic potential in the reconstructed regular frame. -/
def smoothMobileMaxwellRecenterGaugePotential
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    SmoothAbelianGaugePotential period hPeriod :=
  regularFrameGaugePotentialFromCoefficients period hPeriod
    (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
    (smoothMobileMaxwellRecenterGaugeCoefficients period hPeriod metric shift direction hShift coefficients)

/-- The smooth potential represents exactly the velocity in the native Maxwell derivative. -/
theorem smoothMobileMaxwellRecenterGaugePotential_toC2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      (gaugePotentialFrameCoefficients period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
        (smoothMobileMaxwellRecenterGaugePotential period hPeriod metric shift direction hShift coefficients)) =
    mobileMaxwellRecenterGaugeVelocity period hPeriod metric shift direction hShift
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) := by
  rw [smoothMobileMaxwellRecenterGaugePotential, gaugePotentialFrameCoefficients_reconstructed]
  exact smoothMobileMaxwellRecenterGaugeCoefficients_toC2 period hPeriod metric shift direction hShift coefficients

end
end P0EFTJanusSmoothMaxwellRecenterGaugeVelocity4D
end JanusFormal
