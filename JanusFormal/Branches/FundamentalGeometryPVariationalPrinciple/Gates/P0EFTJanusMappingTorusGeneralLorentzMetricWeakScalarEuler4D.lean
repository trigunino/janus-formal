import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

/-!
# Weak covariant scalar Euler equation for a general Lorentz metric

The metric sharp map gives the intrinsic scalar gradient `sharp (d phi)`.
Because the repository does not yet provide the required Lorentzian
divergence theorem, divergence and boundary flux are packaged in an explicit
integration-by-parts certificate.  No Stokes formula is asserted without that
certificate.

Under the three displayed integrability hypotheses, the already proved
general-metric first variation is exactly the weak Euler pairing plus the
certified boundary flux.  Hence the action is stationary when the weak Euler
pairing and boundary flux both vanish.  The construction is also specialized
to the unconditional intrinsic D8 Lorentz metric.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricWeakScalarEuler4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarVariation4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {frame : OrderedTangentVectorFamily period hPeriod}

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

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

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

/-- Intrinsic tangent-vector fields at the minimal pointwise level needed by
the divergence interface.  Smoothness belongs to a future divergence API. -/
abbrev GeneralTangentVectorField :=
  ∀ point : EffectiveQuotient period hPeriod,
    TangentFiber period hPeriod point

/-- The genuine metric gradient `sharp (d phi)`. -/
def generalLorentzScalarGradient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod) :
    GeneralTangentVectorField period hPeriod :=
  fun point => inverseMetricSharp period hPeriod metric point
    (scalarDifferential period hPeriod field point)

@[simp]
theorem metric_flat_generalLorentzScalarGradient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    metric.musical point
        (generalLorentzScalarGradient period hPeriod metric field point) =
      scalarDifferential period hPeriod field point := by
  exact metric_flat_inverseMetricSharp period hPeriod metric point
    (scalarDifferential period hPeriod field point)

/-- Symmetry of the inverse contraction follows from symmetry of the same
covariant tensor whose musical equivalence is inverted. -/
theorem inverseMetricContraction_comm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : CotangentFiber period hPeriod point) :
    inverseMetricContraction period hPeriod metric point first second =
      inverseMetricContraction period hPeriod metric point second first := by
  let firstSharp := inverseMetricSharp period hPeriod metric point first
  let secondSharp := inverseMetricSharp period hPeriod metric point second
  change first secondSharp = second firstSharp
  calc
    first secondSharp = metric.tensor.tensor point firstSharp secondSharp := by
      rw [← metric.musical_eq_tensor point]
      simp [firstSharp]
    _ = metric.tensor.tensor point secondSharp firstSharp :=
      metric.tensor.symmetric point firstSharp secondSharp
    _ = second firstSharp := by
      rw [← metric.musical_eq_tensor point]
      simp [secondSharp]

/-- The symmetrized kinetic coefficient in the existing variation is the
directional pairing `d variation (sharp (d field))`. -/
theorem generalLorentzHolonomicScalarFirstVariation_eq_gradient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalLorentzHolonomicScalarFirstVariation period hPeriod metric
        massSquared field variation frame point =
      metricVolumeDensity period hPeriod metric point (frame point) *
        (scalarDifferential period hPeriod variation point
            (generalLorentzScalarGradient period hPeriod metric field point) -
          massSquared * field point * variation point) := by
  dsimp [generalLorentzHolonomicScalarFirstVariation,
    holonomicScalarDensityFirstVariation, generalLorentzScalarGradient]
  rw [inverseMetricContraction_comm period hPeriod metric point
    (scalarDifferential period hPeriod field point)
    (scalarDifferential period hPeriod variation point)]
  unfold inverseMetricContraction
  ring

/-- Minimal honest interface for a divergence and its boundary flux.  Its
last field is the exact Green identity used below; supplying this structure,
rather than postulating a global theorem, is the remaining geometric task. -/
structure GeneralLorentzScalarDivergenceBoundaryInterface
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) where
  divergence : GeneralTangentVectorField period hPeriod →
    EffectiveQuotient period hPeriod → Real
  boundaryFlux : GeneralTangentVectorField period hPeriod →
    SmoothScalarField period hPeriod → Real
  integrationByParts :
    ∀ (vector : GeneralTangentVectorField period hPeriod)
      (variation : SmoothScalarField period hPeriod),
      (∫ point,
          metricVolumeDensity period hPeriod metric point (frame point) *
            scalarDifferential period hPeriod variation point (vector point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
        -(∫ point,
            metricVolumeDensity period hPeriod metric point (frame point) *
              variation point * divergence vector point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) +
          boundaryFlux vector variation

/-- Covariant Euler expression for the sign convention of the scalar action:
`- div (sharp (d phi)) - m² phi`. -/
def generalLorentzScalarEulerField
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (interface : GeneralLorentzScalarDivergenceBoundaryInterface period hPeriod
      metric frame)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  -interface.divergence
      (generalLorentzScalarGradient period hPeriod metric field) point -
    massSquared * field point

/-- Weak Euler pairing against one smooth scalar test variation. -/
def generalLorentzScalarEulerPairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (interface : GeneralLorentzScalarDivergenceBoundaryInterface period hPeriod
      metric frame)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod) : Real :=
  ∫ point,
      metricVolumeDensity period hPeriod metric point (frame point) *
        variation point *
          generalLorentzScalarEulerField period hPeriod metric interface
            massSquared field point
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Boundary term induced by the scalar gradient. -/
def generalLorentzScalarBoundaryFlux
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (interface : GeneralLorentzScalarDivergenceBoundaryInterface period hPeriod
      metric frame)
    (field variation : SmoothScalarField period hPeriod) : Real :=
  interface.boundaryFlux
    (generalLorentzScalarGradient period hPeriod metric field) variation

/-- The exact integrability pieces needed to separate kinetic, divergence,
and mass pairings. -/
structure GeneralLorentzScalarWeakEulerIntegrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (interface : GeneralLorentzScalarDivergenceBoundaryInterface period hPeriod
      metric frame)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod) : Prop where
  kinetic : Integrable
    (fun point =>
      metricVolumeDensity period hPeriod metric point (frame point) *
        scalarDifferential period hPeriod variation point
          (generalLorentzScalarGradient period hPeriod metric field point))
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  divergence : Integrable
    (fun point =>
      metricVolumeDensity period hPeriod metric point (frame point) *
        variation point * interface.divergence
          (generalLorentzScalarGradient period hPeriod metric field) point)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  potential : Integrable
    (fun point =>
      metricVolumeDensity period hPeriod metric point (frame point) *
        (massSquared * field point * variation point))
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- The weak covariant Euler equation tested against one variation. -/
def GeneralLorentzScalarWeakEulerEquation
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (interface : GeneralLorentzScalarDivergenceBoundaryInterface period hPeriod
      metric frame)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod) : Prop :=
  generalLorentzScalarEulerPairing period hPeriod metric interface massSquared
    field variation = 0

/-- Exact bridge from the already proved first variation to the weak Euler
pairing and the certified boundary flux. -/
theorem canonicalGeneralLorentzHolonomicScalarFirstVariation_eq_eulerPairing_add_boundaryFlux
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (interface : GeneralLorentzScalarDivergenceBoundaryInterface period hPeriod
      metric frame)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hIntegrable : GeneralLorentzScalarWeakEulerIntegrable period hPeriod
      metric interface massSquared field variation) :
    canonicalGeneralLorentzHolonomicScalarFirstVariation period hPeriod metric
        massSquared field variation frame =
      generalLorentzScalarEulerPairing period hPeriod metric interface
          massSquared field variation +
        generalLorentzScalarBoundaryFlux period hPeriod metric interface
          field variation := by
  unfold canonicalGeneralLorentzHolonomicScalarFirstVariation
  simp_rw [generalLorentzHolonomicScalarFirstVariation_eq_gradient period
    hPeriod metric massSquared field variation frame]
  rw [show (fun point =>
      metricVolumeDensity period hPeriod metric point (frame point) *
        (scalarDifferential period hPeriod variation point
            (generalLorentzScalarGradient period hPeriod metric field point) -
          massSquared * field point * variation point)) =
      (fun point =>
        metricVolumeDensity period hPeriod metric point (frame point) *
          scalarDifferential period hPeriod variation point
            (generalLorentzScalarGradient period hPeriod metric field point) -
        metricVolumeDensity period hPeriod metric point (frame point) *
          (massSquared * field point * variation point)) by
      funext point
      ring]
  rw [integral_sub hIntegrable.kinetic hIntegrable.potential]
  rw [interface.integrationByParts
    (generalLorentzScalarGradient period hPeriod metric field) variation]
  unfold generalLorentzScalarEulerPairing generalLorentzScalarEulerField
    generalLorentzScalarBoundaryFlux
  rw [show (fun point =>
      metricVolumeDensity period hPeriod metric point (frame point) *
        variation point *
          (-interface.divergence
              (generalLorentzScalarGradient period hPeriod metric field) point -
            massSquared * field point)) =
      (fun point =>
        -(metricVolumeDensity period hPeriod metric point (frame point) *
          variation point * interface.divergence
            (generalLorentzScalarGradient period hPeriod metric field) point) -
        metricVolumeDensity period hPeriod metric point (frame point) *
          (massSquared * field point * variation point)) by
      funext point
      ring]
  have hDivergenceNeg : Integrable
      (fun point =>
        -(metricVolumeDensity period hPeriod metric point (frame point) *
          variation point * interface.divergence
            (generalLorentzScalarGradient period hPeriod metric field) point))
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
    exact hIntegrable.divergence.neg.congr
      (Filter.Eventually.of_forall (fun point => rfl))
  have hEulerIntegral :
      (∫ point,
          -(metricVolumeDensity period hPeriod metric point (frame point) *
            variation point * interface.divergence
              (generalLorentzScalarGradient period hPeriod metric field) point) -
            metricVolumeDensity period hPeriod metric point (frame point) *
              (massSquared * field point * variation point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
        -(∫ point,
            metricVolumeDensity period hPeriod metric point (frame point) *
              variation point * interface.divergence
                (generalLorentzScalarGradient period hPeriod metric field) point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) -
          ∫ point,
            metricVolumeDensity period hPeriod metric point (frame point) *
              (massSquared * field point * variation point)
            ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
    calc
      _ = (∫ point,
            -(metricVolumeDensity period hPeriod metric point (frame point) *
              variation point * interface.divergence
                (generalLorentzScalarGradient period hPeriod metric field) point)
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) -
          ∫ point,
            metricVolumeDensity period hPeriod metric point (frame point) *
              (massSquared * field point * variation point)
            ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
        integral_sub hDivergenceNeg hIntegrable.potential
      _ = _ := by rw [integral_neg]
  rw [hEulerIntegral]
  ring

/-- With zero boundary flux, variational stationarity is exactly the weak
Euler equation for the same test variation. -/
theorem canonicalGeneralLorentzHolonomicScalarFirstVariation_eq_zero_iff_weakEuler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (interface : GeneralLorentzScalarDivergenceBoundaryInterface period hPeriod
      metric frame)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hIntegrable : GeneralLorentzScalarWeakEulerIntegrable period hPeriod
      metric interface massSquared field variation)
    (hFlux : generalLorentzScalarBoundaryFlux period hPeriod metric interface
      field variation = 0) :
    canonicalGeneralLorentzHolonomicScalarFirstVariation period hPeriod metric
          massSquared field variation frame = 0 ↔
      GeneralLorentzScalarWeakEulerEquation period hPeriod metric interface
        massSquared field variation := by
  rw [canonicalGeneralLorentzHolonomicScalarFirstVariation_eq_eulerPairing_add_boundaryFlux
    period hPeriod metric interface massSquared field variation hIntegrable,
    hFlux, add_zero]
  rfl

/-- A pointwise Euler solution implies every corresponding weak equation. -/
theorem weakEulerEquation_of_eulerField_eq_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (interface : GeneralLorentzScalarDivergenceBoundaryInterface period hPeriod
      metric frame)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hEuler : ∀ point,
      generalLorentzScalarEulerField period hPeriod metric interface
        massSquared field point = 0) :
    GeneralLorentzScalarWeakEulerEquation period hPeriod metric interface
      massSquared field variation := by
  unfold GeneralLorentzScalarWeakEulerEquation
    generalLorentzScalarEulerPairing
  simp_rw [hEuler]
  simp

/-- The actual action derivative vanishes under the weak Euler equation and
zero certified boundary flux. -/
theorem canonicalGeneralLorentzHolonomicScalarAction_line_hasDerivAt_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (interface : GeneralLorentzScalarDivergenceBoundaryInterface period hPeriod
      metric frame)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hAction : CanonicalGeneralLorentzScalarVariationIntegrable period hPeriod
      metric massSquared field variation frame)
    (hWeakIntegrable : GeneralLorentzScalarWeakEulerIntegrable period hPeriod
      metric interface massSquared field variation)
    (hWeak : GeneralLorentzScalarWeakEulerEquation period hPeriod metric
      interface massSquared field variation)
    (hFlux : generalLorentzScalarBoundaryFlux period hPeriod metric interface
      field variation = 0) :
    HasDerivAt
      (fun epsilon : Real =>
        canonicalGeneralLorentzHolonomicScalarAction period hPeriod metric
          massSquared (scalarFieldLine period hPeriod field variation epsilon)
          frame)
      0 0 := by
  have hFirstVariation :
      canonicalGeneralLorentzHolonomicScalarFirstVariation period hPeriod
        metric massSquared field variation frame = 0 :=
    (canonicalGeneralLorentzHolonomicScalarFirstVariation_eq_zero_iff_weakEuler
      period hPeriod metric interface massSquared field variation
      hWeakIntegrable hFlux).2 hWeak
  simpa [hFirstVariation] using
    canonicalGeneralLorentzHolonomicScalarAction_line_hasDerivAt period hPeriod
      metric massSquared field variation frame hAction

/-- Intrinsic D8 specialization of the general divergence/flux interface. -/
abbrev IntrinsicD8ScalarDivergenceBoundaryInterface :=
  GeneralLorentzScalarDivergenceBoundaryInterface period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
    (intrinsicPointwiseFrame period hPeriod)

/-- Canonical integrated first variation for the unconditional intrinsic D8
Lorentz metric and its certified pointwise frame. -/
def canonicalIntrinsicD8HolonomicScalarFirstVariation
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod) : Real :=
  canonicalGeneralLorentzHolonomicScalarFirstVariation period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared field
    variation (intrinsicPointwiseFrame period hPeriod)

@[simp]
theorem intrinsicD8_generalFirstVariation_eq
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalLorentzHolonomicScalarFirstVariation period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared field
        variation (intrinsicPointwiseFrame period hPeriod) point =
      intrinsicHolonomicScalarFirstVariation period hPeriod massSquared field
        variation point :=
  rfl

/-- The weak Euler plus boundary-flux decomposition specialized to D8. -/
theorem canonicalIntrinsicD8HolonomicScalarFirstVariation_eq_eulerPairing_add_boundaryFlux
    (interface : IntrinsicD8ScalarDivergenceBoundaryInterface period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hIntegrable : GeneralLorentzScalarWeakEulerIntegrable period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) interface massSquared
      field variation) :
    canonicalIntrinsicD8HolonomicScalarFirstVariation period hPeriod
        massSquared field variation =
      generalLorentzScalarEulerPairing period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) interface
          massSquared field variation +
        generalLorentzScalarBoundaryFlux period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) interface
          field variation := by
  exact
    canonicalGeneralLorentzHolonomicScalarFirstVariation_eq_eulerPairing_add_boundaryFlux
      period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      interface massSquared field variation hIntegrable

end

end P0EFTJanusMappingTorusGeneralLorentzMetricWeakScalarEuler4D
end JanusFormal
