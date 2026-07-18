import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

/-!
# Frame covariance of the intrinsic D8 scalar density

The results are fiberwise.  A continuous linear equivalence transports the
metric, covectors and tangent frame coherently; the Gram matrix, its
determinant, the metric volume and the full scalar density are then natural.
The final statements specialize the equivalence to an actual D8
diffeomorphism derivative.  No integration claim is made.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open scoped Manifold ContDiff Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

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

private abbrev MusicalFiber (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point ≃L[Real] CotangentFiber period hPeriod point

/-- Pullback of covectors along a continuous linear equivalence. -/
def pullbackCovector
    {source target : EffectiveQuotient period hPeriod}
    (equivalence : TangentFiber period hPeriod source ≃L[Real]
      TangentFiber period hPeriod target) :
    CotangentFiber period hPeriod target ≃L[Real]
      CotangentFiber period hPeriod source :=
  equivalence.symm.arrowCongr (ContinuousLinearEquiv.refl Real Real)

@[simp]
theorem pullbackCovector_apply
    {source target : EffectiveQuotient period hPeriod}
    (equivalence : TangentFiber period hPeriod source ≃L[Real]
      TangentFiber period hPeriod target)
    (covector : CotangentFiber period hPeriod target)
    (vector : TangentFiber period hPeriod source) :
    pullbackCovector period hPeriod equivalence covector vector =
      covector (equivalence vector) :=
  rfl

/-- Pullback of the metric musical equivalence. -/
def pullbackMusical
    {source target : EffectiveQuotient period hPeriod}
    (equivalence : TangentFiber period hPeriod source ≃L[Real]
      TangentFiber period hPeriod target)
    (musical : MusicalFiber period hPeriod target) :
    MusicalFiber period hPeriod source :=
  equivalence.trans
    (musical.trans (pullbackCovector period hPeriod equivalence))

@[simp]
theorem pullbackMusical_apply
    {source target : EffectiveQuotient period hPeriod}
    (equivalence : TangentFiber period hPeriod source ≃L[Real]
      TangentFiber period hPeriod target)
    (musical : MusicalFiber period hPeriod target)
    (first second : TangentFiber period hPeriod source) :
    pullbackMusical period hPeriod equivalence musical first second =
      musical (equivalence first) (equivalence second) :=
  rfl

/-- Inverse-metric contraction attached to one musical equivalence. -/
def fiberInverseMetricContraction
    {point : EffectiveQuotient period hPeriod}
    (musical : MusicalFiber period hPeriod point)
    (first second : CotangentFiber period hPeriod point) : Real :=
  first (musical.symm second)

/-- Inverse contraction is natural under coherent pullback. -/
theorem fiberInverseMetricContraction_pullback
    {source target : EffectiveQuotient period hPeriod}
    (equivalence : TangentFiber period hPeriod source ≃L[Real]
      TangentFiber period hPeriod target)
    (musical : MusicalFiber period hPeriod target)
    (first second : CotangentFiber period hPeriod target) :
    fiberInverseMetricContraction period hPeriod
        (pullbackMusical period hPeriod equivalence musical)
        (pullbackCovector period hPeriod equivalence first)
        (pullbackCovector period hPeriod equivalence second) =
      fiberInverseMetricContraction period hPeriod musical first second := by
  simp [fiberInverseMetricContraction, pullbackMusical, pullbackCovector]
  congr 2
  apply ContinuousLinearMap.ext
  intro vector
  change second (equivalence (equivalence.symm vector)) = second vector
  rw [equivalence.apply_symm_apply]

/-- Gram matrix in an ordered tangent frame. -/
def fiberGramMatrix
    {point : EffectiveQuotient period hPeriod}
    (musical : MusicalFiber period hPeriod point)
    (frame : Fin 4 → TangentFiber period hPeriod point) :
    Matrix (Fin 4) (Fin 4) Real :=
  fun i j => musical (frame i) (frame j)

/-- The pulled metric in the source frame has the target Gram matrix in the
pushed frame. -/
theorem fiberGramMatrix_pullback
    {source target : EffectiveQuotient period hPeriod}
    (equivalence : TangentFiber period hPeriod source ≃L[Real]
      TangentFiber period hPeriod target)
    (musical : MusicalFiber period hPeriod target)
    (frame : Fin 4 → TangentFiber period hPeriod source) :
    fiberGramMatrix period hPeriod
        (pullbackMusical period hPeriod equivalence musical) frame =
      fiberGramMatrix period hPeriod musical
        (fun i => equivalence (frame i)) := by
  ext i j
  rfl

theorem fiberGramDeterminant_pullback
    {source target : EffectiveQuotient period hPeriod}
    (equivalence : TangentFiber period hPeriod source ≃L[Real]
      TangentFiber period hPeriod target)
    (musical : MusicalFiber period hPeriod target)
    (frame : Fin 4 → TangentFiber period hPeriod source) :
    (fiberGramMatrix period hPeriod
      (pullbackMusical period hPeriod equivalence musical) frame).det =
      (fiberGramMatrix period hPeriod musical
        (fun i => equivalence (frame i))).det := by
  rw [fiberGramMatrix_pullback]

/-- Fiber metric-volume evaluation. -/
def fiberMetricVolumeDensity
    {point : EffectiveQuotient period hPeriod}
    (musical : MusicalFiber period hPeriod point)
    (frame : Fin 4 → TangentFiber period hPeriod point) : Real :=
  Real.sqrt |(fiberGramMatrix period hPeriod musical frame).det|

theorem fiberMetricVolumeDensity_pullback
    {source target : EffectiveQuotient period hPeriod}
    (equivalence : TangentFiber period hPeriod source ≃L[Real]
      TangentFiber period hPeriod target)
    (musical : MusicalFiber period hPeriod target)
    (frame : Fin 4 → TangentFiber period hPeriod source) :
    fiberMetricVolumeDensity period hPeriod
        (pullbackMusical period hPeriod equivalence musical) frame =
      fiberMetricVolumeDensity period hPeriod musical
        (fun i => equivalence (frame i)) := by
  simp only [fiberMetricVolumeDensity, fiberGramDeterminant_pullback]

/-- Pointwise scalar density written only from one musical metric, a
holonomic covector and a frame. -/
def fiberHolonomicScalarDensity
    {point : EffectiveQuotient period hPeriod}
    (musical : MusicalFiber period hPeriod point)
    (massSquared fieldValue : Real)
    (differential : CotangentFiber period hPeriod point)
    (frame : Fin 4 → TangentFiber period hPeriod point) : Real :=
  fiberMetricVolumeDensity period hPeriod musical frame *
    (1 / 2 * fiberInverseMetricContraction period hPeriod musical
      differential differential - 1 / 2 * massSquared * fieldValue ^ 2)

/-- Full fiber density invariance when metric, covector and frame are
transported coherently. -/
theorem fiberHolonomicScalarDensity_pullback
    {source target : EffectiveQuotient period hPeriod}
    (equivalence : TangentFiber period hPeriod source ≃L[Real]
      TangentFiber period hPeriod target)
    (musical : MusicalFiber period hPeriod target)
    (massSquared fieldValue : Real)
    (differential : CotangentFiber period hPeriod target)
    (frame : Fin 4 → TangentFiber period hPeriod source) :
    fiberHolonomicScalarDensity period hPeriod
        (pullbackMusical period hPeriod equivalence musical)
        massSquared fieldValue
        (pullbackCovector period hPeriod equivalence differential) frame =
      fiberHolonomicScalarDensity period hPeriod musical massSquared fieldValue
        differential (fun i => equivalence (frame i)) := by
  simp [fiberHolonomicScalarDensity, fiberMetricVolumeDensity_pullback,
    fiberInverseMetricContraction_pullback]

/-- The fiber volume is exactly the volume used by the smooth metric gate. -/
theorem metricVolumeDensity_eq_fiber
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) :
    metricVolumeDensity period hPeriod metric point frame =
      fiberMetricVolumeDensity period hPeriod (metric.musical point) frame := by
  have hGram :
      metricGramMatrix period hPeriod metric point frame =
        fiberGramMatrix period hPeriod (metric.musical point) frame := by
    ext i j
    change metric.tensor.tensor point (frame i) (frame j) =
      metric.musical point (frame i) (frame j)
    rw [← metric.musical_eq_tensor point]
    rfl
  rw [metricVolumeDensity, fiberMetricVolumeDensity, hGram]

/-- The smooth-gate density is the same fiber density, not a second
coordinate formula. -/
theorem holonomicScalarDensity_eq_fiber
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) :
    holonomicScalarDensity period hPeriod metric massSquared field point frame =
      fiberHolonomicScalarDensity period hPeriod (metric.musical point)
        massSquared (field point) (scalarDifferential period hPeriod field point)
        frame := by
  rw [holonomicScalarDensity, fiberHolonomicScalarDensity,
    metricVolumeDensity_eq_fiber]
  rfl

/-- The actual tangent equivalence supplied by a D8 diffeomorphism. -/
def diffeomorphismDerivative
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real]
      TangentFiber period hPeriod (diffeomorphism point) :=
  diffeomorphism.mfderivToContinuousLinearEquiv
    (I := coverModelWithCorners) (J := coverModelWithCorners) (by simp) point

/-- The differential of the pulled scalar is the pulled differential of the
original scalar. -/
theorem scalarDifferential_pullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    scalarDifferential period hPeriod
        (pullbackSmoothField period hPeriod Real diffeomorphism field) point =
      pullbackCovector period hPeriod
        (diffeomorphismDerivative period hPeriod diffeomorphism point)
        (scalarDifferential period hPeriod field (diffeomorphism point)) := by
  apply ContinuousLinearMap.ext
  intro tangent
  have hOuter := field.contMDiff_toFun.mdifferentiableAt
    (x := diffeomorphism point) (by simp)
  have hInner := diffeomorphism.contMDiff.mdifferentiableAt
    (x := point) (by simp)
  change mfderiv coverModelWithCorners 𝓘(Real, Real)
      (field.toFun ∘ diffeomorphism) point tangent =
    mfderiv coverModelWithCorners 𝓘(Real, Real) field
      (diffeomorphism point)
      (mfderiv coverModelWithCorners coverModelWithCorners
        diffeomorphism point tangent)
  rw [mfderiv_comp point hOuter hInner]
  rfl

/-- Naturality of the holonomic density under the derivative of an actual D8
diffeomorphism.  The source metric is the genuine pullback musical metric and
the source covector is `d(φ ∘ F)`. -/
theorem holonomicScalarDensity_diffeomorphism
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frame : Fin 4 → TangentFiber period hPeriod point) :
    fiberHolonomicScalarDensity period hPeriod
        (pullbackMusical period hPeriod
          (diffeomorphismDerivative period hPeriod diffeomorphism point)
          (metric.musical (diffeomorphism point)))
        massSquared (field (diffeomorphism point))
        (scalarDifferential period hPeriod
          (pullbackSmoothField period hPeriod Real diffeomorphism field) point)
        frame =
      holonomicScalarDensity period hPeriod metric massSquared field
        (diffeomorphism point)
        (fun i => diffeomorphismDerivative period hPeriod diffeomorphism point
          (frame i)) := by
  rw [scalarDifferential_pullback]
  rw [fiberHolonomicScalarDensity_pullback]
  exact (holonomicScalarDensity_eq_fiber period hPeriod metric massSquared field
    (diffeomorphism point)
    (fun i => diffeomorphismDerivative period hPeriod diffeomorphism point
      (frame i))).symm

end

end P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D
end JanusFormal
