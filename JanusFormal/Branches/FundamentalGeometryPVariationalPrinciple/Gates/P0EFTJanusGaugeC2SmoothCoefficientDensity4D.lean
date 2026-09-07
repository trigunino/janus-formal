import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D

/-! # Density of actual smooth gauge coefficients in the C² coefficient cores -/

namespace JanusFormal
namespace P0EFTJanusGaugeC2SmoothCoefficientDensity4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

/-- Every eight-tuple of smooth scalars is an actual smooth gauge coefficient field. -/
def smoothGaugeCoefficientFieldOfComponents
    (components : Fin 4 → Fin 2 → SmoothQuotientField period hPeriod Real) :
    SmoothQuotientField period hPeriod GaugeFiber where
  toFun := fun point =>
    (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm
      (fun index => components index.1 index.2 point)
  contMDiff_toFun := by
    apply (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm.contDiff.contMDiff.comp
    rw [contMDiff_pi_space]
    intro index
    exact (components index.1 index.2).contMDiff_toFun

@[simp]
theorem regularFrameGaugeCoefficient_fieldOfComponents
    (components : Fin 4 → Fin 2 → SmoothQuotientField period hPeriod Real)
    (frameIndex : Fin 4) (component : Fin 2) :
    regularFrameGaugeCoefficient period hPeriod
        (smoothGaugeCoefficientFieldOfComponents period hPeriod components)
        (frameIndex, component) = components frameIndex component := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

theorem smoothGaugeCoefficientC2CoreLinearMap_denseRange :
    DenseRange (smoothGaugeCoefficientC2CoreLinearMap period hPeriod) := by
  have hDense : DenseRange
      (fun components : Fin 4 → Fin 2 → SmoothQuotientField period hPeriod Real =>
        fun frameIndex component => smoothToCanonicalPhysicalScalarC2JetCore
          period hPeriod (components frameIndex component)) :=
    DenseRange.piMap fun _ : Fin 4 =>
      DenseRange.piMap fun _ : Fin 2 =>
        smoothToCanonicalPhysicalScalarC2JetCore_denseRange period hPeriod
  refine Dense.mono ?_ hDense
  rintro _ ⟨components, rfl⟩
  refine ⟨smoothGaugeCoefficientFieldOfComponents period hPeriod components, ?_⟩
  funext frameIndex component
  rw [smoothGaugeCoefficientC2CoreLinearMap_apply,
    regularFrameGaugeCoefficient_fieldOfComponents]

theorem smoothGaugeVariationPairC2CoreLinearMap_denseRange :
    DenseRange (smoothGaugeVariationPairC2CoreLinearMap period hPeriod) :=
  (smoothGaugeCoefficientC2CoreLinearMap_denseRange period hPeriod).prodMap
    (smoothGaugeCoefficientC2CoreLinearMap_denseRange period hPeriod)

end
end P0EFTJanusGaugeC2SmoothCoefficientDensity4D
end JanusFormal
