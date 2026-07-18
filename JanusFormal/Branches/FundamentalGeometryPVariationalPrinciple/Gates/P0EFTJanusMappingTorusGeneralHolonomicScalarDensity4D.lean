import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzTensor4D

/-!
# Intrinsic holonomic scalar density on the effective D8 quotient

This gate defines a pointwise metric density evaluation and a scalar
Lagrangian using one general Lorentz metric.  Its inverse, contraction and
volume all come from that metric, while the covector is the manifold
differential of the same scalar field.  No spacetime integral is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open scoped Manifold ContDiff Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

/-- A smooth general Lorentz metric with its genuine musical equivalence.
The equality field prevents the inverse from being chosen independently of
the covariant metric. -/
structure SmoothGeneralLorentzMetric where
  tensor : SmoothSymmetricCovariantTwoTensor period hPeriod
  musical : ∀ point, TangentFiber period hPeriod point ≃L[Real]
    CotangentFiber period hPeriod point
  musical_eq_tensor : ∀ point,
    (musical point : TangentFiber period hPeriod point →L[Real]
      CotangentFiber period hPeriod point) = tensor.tensor point
  lorentzian : IsEverywhereLorentzian period hPeriod tensor

/-- The metric map is nondegenerate because the inverse is the inverse of the
same musical equivalence. -/
theorem metric_nondegenerate_at
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    IsNondegenerateAt period hPeriod metric.tensor point := by
  rw [IsNondegenerateAt, FiberIsNondegenerate,
    ← metric.musical_eq_tensor point]
  exact (metric.musical point).injective

theorem metric_everywhere_nondegenerate
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    IsEverywhereNondegenerate period hPeriod metric.tensor := by
  intro point
  exact metric_nondegenerate_at period hPeriod metric point

/-- The inverse metric is the inverse of the covariant metric map. -/
def inverseMetricSharp
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    CotangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point :=
  (metric.musical point).symm

@[simp]
theorem metric_flat_inverseMetricSharp
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (covector : CotangentFiber period hPeriod point) :
    metric.musical point
        (inverseMetricSharp period hPeriod metric point covector) = covector := by
  simp [inverseMetricSharp]

@[simp]
theorem inverseMetricSharp_metric_flat
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    inverseMetricSharp period hPeriod metric point
        (metric.musical point vector) = vector := by
  simp [inverseMetricSharp]

/-- Intrinsic inverse-metric contraction of two covectors. -/
def inverseMetricContraction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : CotangentFiber period hPeriod point) : Real :=
  first (inverseMetricSharp period hPeriod metric point second)

/-- Gram matrix of the metric on an ordered tangent frame. -/
def metricGramMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) :
    Matrix (Fin 4) (Fin 4) Real :=
  fun i j => metric.tensor.tensor point (frame i) (frame j)

/-- Intrinsic absolute metric-density evaluation on an ordered tangent frame.
It is the square root of the absolute Gram determinant. -/
def metricVolumeDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) : Real :=
  Real.sqrt |(metricGramMatrix period hPeriod metric point frame).det|

/-- Smooth real scalar fields on the effective quotient. -/
abbrev SmoothScalarField :=
  SmoothQuotientField period hPeriod Real

/-- The holonomic covector is the manifold differential of the scalar field
at the same point. -/
def scalarDifferential
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    CotangentFiber period hPeriod point :=
  mfderiv coverModelWithCorners 𝓘(Real, Real) field point

/-- Pointwise scalar Lagrangian density evaluated on a tangent frame. -/
def holonomicScalarDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) : Real :=
  metricVolumeDensity period hPeriod metric point frame *
    (1 / 2 * inverseMetricContraction period hPeriod metric point
      (scalarDifferential period hPeriod field point)
      (scalarDifferential period hPeriod field point) -
      1 / 2 * massSquared * (field point) ^ 2)

/-- Smooth affine variation of one scalar field. -/
def scalarFieldLine
    (field variation : SmoothScalarField period hPeriod)
    (epsilon : Real) : SmoothScalarField period hPeriod where
  toFun := fun point => field point + epsilon * variation point
  contMDiff_toFun := field.contMDiff_toFun.add
    (contMDiff_const.mul variation.contMDiff_toFun)

@[simp]
theorem scalarFieldLine_apply
    (field variation : SmoothScalarField period hPeriod)
    (epsilon : Real)
    (point : EffectiveQuotient period hPeriod) :
    scalarFieldLine period hPeriod field variation epsilon point =
      field point + epsilon * variation point :=
  rfl

/-- Holonomicity is preserved along the field line: the varied covector is
the differential of the varied scalar, not an independent jet variable. -/
theorem scalarDifferential_scalarFieldLine
    (field variation : SmoothScalarField period hPeriod)
    (epsilon : Real)
    (point : EffectiveQuotient period hPeriod) :
    scalarDifferential period hPeriod
        (scalarFieldLine period hPeriod field variation epsilon) point =
      scalarDifferential period hPeriod field point +
        epsilon • scalarDifferential period hPeriod variation point := by
  unfold scalarDifferential scalarFieldLine
  change mfderiv coverModelWithCorners _
      (field.toFun + epsilon • variation.toFun) point = _
  rw [mfderiv_add (field.contMDiff_toFun.mdifferentiableAt (by simp))
      ((variation.contMDiff_toFun.mdifferentiableAt (by simp)).const_smul epsilon),
    const_smul_mfderiv
      (variation.contMDiff_toFun.mdifferentiableAt (by simp)) epsilon]
  ext tangent
  rfl

/-- Exact coefficient linear in a holonomic scalar variation. -/
def holonomicScalarDensityFirstVariation
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) : Real :=
  let differential := scalarDifferential period hPeriod field point
  let differentialVariation :=
    scalarDifferential period hPeriod variation point
  metricVolumeDensity period hPeriod metric point frame *
    (1 / 2 *
        (inverseMetricContraction period hPeriod metric point
            differentialVariation differential +
          inverseMetricContraction period hPeriod metric point
            differential differentialVariation) -
      massSquared * field point * variation point)

/-- Quadratic remainder along the affine scalar line. -/
def holonomicScalarDensityQuadraticRemainder
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (variation : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) : Real :=
  let differentialVariation :=
    scalarDifferential period hPeriod variation point
  metricVolumeDensity period hPeriod metric point frame *
    (1 / 2 * inverseMetricContraction period hPeriod metric point
        differentialVariation differentialVariation -
      1 / 2 * massSquared * (variation point) ^ 2)

/-- Exact pointwise expansion.  In particular the displayed first variation
is the genuine linear coefficient while `p = dφ` throughout. -/
theorem holonomicScalarDensity_line_expansion
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (epsilon : Real)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) :
    holonomicScalarDensity period hPeriod metric massSquared
        (scalarFieldLine period hPeriod field variation epsilon) point frame =
      holonomicScalarDensity period hPeriod metric massSquared field point frame +
        epsilon * holonomicScalarDensityFirstVariation period hPeriod metric
          massSquared field variation point frame +
        epsilon ^ 2 * holonomicScalarDensityQuadraticRemainder period hPeriod
          metric massSquared variation point frame := by
  unfold holonomicScalarDensity holonomicScalarDensityFirstVariation
    holonomicScalarDensityQuadraticRemainder
  rw [scalarDifferential_scalarFieldLine]
  simp only [scalarFieldLine_apply]
  simp only [inverseMetricContraction, inverseMetricSharp, map_add, map_smul,
    add_apply, smul_apply, smul_eq_mul]
  ring

end

end P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
end JanusFormal
