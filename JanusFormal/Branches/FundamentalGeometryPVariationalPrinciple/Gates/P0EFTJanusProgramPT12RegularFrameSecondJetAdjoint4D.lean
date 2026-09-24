import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalFormalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricInducedMaxwellResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D

/-! Ordered second-jet integration by parts against the actual canonical measure. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12RegularFrameSecondJetAdjoint4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusMetricInducedSmoothGaugeVelocity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open P0EFTJanusRegularFrameCanonicalFormalAdjoint4D

variable (metric : RegularGeneralLorentzMetric period hPeriod)

/-- The adjoint reverses the order; no commutation of frame vectors is used. -/
theorem regularFrameSecondDerivative_adjoint
    (coefficient test : SmoothScalarField period hPeriod) (outer inner : Fin 4) :
    canonicalSmoothScalarIntegral period hPeriod
      (smoothScalarFieldMul period hPeriod coefficient
        (frameDerivativeComponentField period hPeriod (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (frameDerivativeComponentField period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) test inner) outer)) =
    canonicalSmoothScalarIntegral period hPeriod
      (smoothScalarFieldMul period hPeriod
        (regularFrameCanonicalFormalAdjoint period hPeriod metric
          (regularFrameCanonicalFormalAdjoint period hPeriod metric coefficient outer) inner) test) := by
  rw [regularFrameCanonicalFormalAdjoint_smoothIntegral,
    regularFrameCanonicalFormalAdjoint_smoothIntegral]

def regularFrameSecondJetDensity
    (value : SmoothScalarField period hPeriod)
    (first : Fin 4 → SmoothScalarField period hPeriod)
    (second : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
    (test : SmoothScalarField period hPeriod) : SmoothScalarField period hPeriod :=
  smoothScalarFieldMul period hPeriod value test +
  ∑ direction : Fin 4, smoothScalarFieldMul period hPeriod (first direction)
    (frameDerivativeComponentField period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) test direction) +
  ∑ outer : Fin 4, ∑ inner : Fin 4, smoothScalarFieldMul period hPeriod (second outer inner)
    (frameDerivativeComponentField period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) test inner) outer)

def regularFrameSecondJetAdjoint
    (value : SmoothScalarField period hPeriod)
    (first : Fin 4 → SmoothScalarField period hPeriod)
    (second : Fin 4 → Fin 4 → SmoothScalarField period hPeriod) : SmoothScalarField period hPeriod :=
  value + (∑ direction : Fin 4, regularFrameCanonicalFormalAdjoint period hPeriod metric (first direction) direction) +
    ∑ outer : Fin 4, ∑ inner : Fin 4, regularFrameCanonicalFormalAdjoint period hPeriod metric
      (regularFrameCanonicalFormalAdjoint period hPeriod metric (second outer inner) outer) inner

private def coefficientIntegral (test : SmoothScalarField period hPeriod) :
    SmoothScalarField period hPeriod →ₗ[Real] Real where
  toFun := fun coefficient => canonicalSmoothScalarIntegral period hPeriod
    (smoothScalarFieldMul period hPeriod coefficient test)
  map_add' := by
    intro first second
    rw [← map_add]
    apply congrArg (canonicalSmoothScalarIntegral period hPeriod)
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change (first point + second point) * test point = first point * test point + second point * test point
    exact add_mul _ _ _
  map_smul' := by
    intro scalar coefficient
    rw [← map_smul]
    apply congrArg (canonicalSmoothScalarIntegral period hPeriod)
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change (scalar * coefficient point) * test point = scalar * (coefficient point * test point)
    exact mul_assoc _ _ _

theorem regularFrameSecondJetAdjoint_integral
    (value : SmoothScalarField period hPeriod)
    (first : Fin 4 → SmoothScalarField period hPeriod)
    (second : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
    (test : SmoothScalarField period hPeriod) :
    canonicalSmoothScalarIntegral period hPeriod
      (regularFrameSecondJetDensity period hPeriod metric value first second test) =
    canonicalSmoothScalarIntegral period hPeriod (smoothScalarFieldMul period hPeriod
      (regularFrameSecondJetAdjoint period hPeriod metric value first second) test) := by
  change _ = coefficientIntegral period hPeriod test _
  simp only [regularFrameSecondJetDensity, regularFrameSecondJetAdjoint, map_add, map_sum]
  simp_rw [regularFrameSecondDerivative_adjoint, regularFrameCanonicalFormalAdjoint_smoothIntegral]
  rfl

end
end P0EFTJanusProgramPT12RegularFrameSecondJetAdjoint4D
end JanusFormal
