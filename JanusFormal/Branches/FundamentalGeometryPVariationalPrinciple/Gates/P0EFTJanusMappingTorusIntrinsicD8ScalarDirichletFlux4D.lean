import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricWeakScalarEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeometricNormalJunction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D

/-!
# Intrinsic D8 scalar flux and Dirichlet cancellation

The existing differential-normal flux is paired here with the actual throat
trace of a scalar variation.  For the intrinsic D8 Lorentz metric it equals
the metric pairing of `sharp (d phi)` with the chosen differential-normal
representative.  Its integral uses the canonical nonzero throat measure.

Every exact homogeneous Dirichlet variation annihilates this concrete flux,
without an integrability or Stokes assumption.  This discharges the boundary
term in the weak scalar Euler gate whenever that gate's supplied boundary
functional is realized by this normal flux.  Constructing the divergence-side
Stokes identity and a canonical metric unit normal remain separate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicD8ScalarDirichletFlux4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarVariation4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricWeakScalarEuler4D
open P0EFTJanusMappingTorusGeometricNormalJunction4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

/-- Actual scalar boundary-flux density: the trace of the variation multiplies
the genuine differential-normal derivative of the bulk scalar. -/
def intrinsicD8ScalarNormalFluxDensity
    (splitting : DifferentialNormalSplitting period hPeriod)
    (field variation : SmoothScalarField period hPeriod)
    (normal : SmoothNormalTest period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  geometricNormalFlux period hPeriod splitting field point
    ((throatTrace period hPeriod Real variation point) • normal point)

theorem intrinsicD8ScalarNormalFluxDensity_apply
    (splitting : DifferentialNormalSplitting period hPeriod)
    (field variation : SmoothScalarField period hPeriod)
    (normal : SmoothNormalTest period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicD8ScalarNormalFluxDensity period hPeriod splitting field variation
        normal point =
      throatTrace period hPeriod Real variation point *
        geometricNormalFlux period hPeriod splitting field point
          (normal point) := by
  simp [intrinsicD8ScalarNormalFluxDensity, map_smul, smul_eq_mul]

/-- The two earlier scalar gates use definitionally identical manifold
differentials; this named bridge prevents namespace ambiguity below. -/
theorem globalScalarDifferential_eq_generalScalarDifferential
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    P0EFTJanusMappingTorusGlobalHolonomicScalar4D.scalarDifferential
        period hPeriod field point =
      P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D.scalarDifferential
        period hPeriod field point :=
  rfl

/-- For the intrinsic D8 metric the differential-normal flux is exactly
`g (sharp (d phi), n)` for the representative selected by the splitting. -/
theorem geometricNormalFlux_eq_intrinsicD8GradientPairing
    (splitting : DifferentialNormalSplitting period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (normal : SmoothNormalTest period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    geometricNormalFlux period hPeriod splitting field point (normal point) =
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod point)
        (generalLorentzScalarGradient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) field
          (fixedThroatQuotientInclusion period hPeriod point))
        (splitting.representative point
          (differentialNormalFiberEquiv period hPeriod point
            (normal point))) := by
  let base := fixedThroatQuotientInclusion period hPeriod point
  let representative := splitting.representative point
    (differentialNormalFiberEquiv period hPeriod point (normal point))
  have hFlat := metric_flat_generalLorentzScalarGradient period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) field base
  have hFlatApply := congrArg (fun covector => covector representative) hFlat
  rw [geometricNormalFlux_apply]
  calc
    _ = P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D.scalarDifferential
        period hPeriod field base representative := by
      rw [globalScalarDifferential_eq_generalScalarDifferential]
    _ = (intrinsicSmoothGeneralLorentzMetric period hPeriod).musical base
        (generalLorentzScalarGradient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) field base)
        representative := hFlatApply.symm
    _ = _ := by
      have hMusical := congrArg
        (fun current => current
          (generalLorentzScalarGradient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) field base)
          representative)
        ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical_eq_tensor
          base)
      simpa [base, representative] using hMusical

/-- Pointwise flux density written entirely as the trace times the intrinsic
metric-gradient normal pairing. -/
theorem intrinsicD8ScalarNormalFluxDensity_eq_gradientPairing
    (splitting : DifferentialNormalSplitting period hPeriod)
    (field variation : SmoothScalarField period hPeriod)
    (normal : SmoothNormalTest period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    intrinsicD8ScalarNormalFluxDensity period hPeriod splitting field variation
        normal point =
      throatTrace period hPeriod Real variation point *
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod point)
          (generalLorentzScalarGradient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) field
            (fixedThroatQuotientInclusion period hPeriod point))
          (splitting.representative point
            (differentialNormalFiberEquiv period hPeriod point
              (normal point))) := by
  rw [intrinsicD8ScalarNormalFluxDensity_apply,
    geometricNormalFlux_eq_intrinsicD8GradientPairing]

/-- Concrete integrated scalar flux on the actual D8 throat and its canonical
finite nonzero measure. -/
def canonicalIntrinsicD8ScalarNormalBoundaryFlux
    (splitting : DifferentialNormalSplitting period hPeriod)
    (field variation : SmoothScalarField period hPeriod)
    (normal : SmoothNormalTest period hPeriod) : Real :=
  ∫ point,
      intrinsicD8ScalarNormalFluxDensity period hPeriod splitting field
        variation normal point
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

theorem throatTrace_eq_zero_of_homogeneousDirichlet
    (variation : SmoothScalarField period hPeriod)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation) :
    throatTrace period hPeriod Real variation = 0 :=
  hDirichlet

theorem throatTrace_apply_eq_zero_of_homogeneousDirichlet
    (variation : SmoothScalarField period hPeriod)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation)
    (point : EffectiveThroat period hPeriod) :
    throatTrace period hPeriod Real variation point = 0 := by
  have hPoint := congrArg
    (fun current : SmoothThroatField period hPeriod Real => current point)
    (throatTrace_eq_zero_of_homogeneousDirichlet period hPeriod variation
      hDirichlet)
  have hZero : (0 : SmoothThroatField period hPeriod Real).toFun point = 0 :=
    rfl
  exact hPoint.trans hZero

/-- Homogeneous Dirichlet data kills the actual normal flux density pointwise,
for every splitting, scalar field, and smooth twisted normal test. -/
theorem intrinsicD8ScalarNormalFluxDensity_eq_zero_of_homogeneousDirichlet
    (splitting : DifferentialNormalSplitting period hPeriod)
    (field variation : SmoothScalarField period hPeriod)
    (normal : SmoothNormalTest period hPeriod)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation)
    (point : EffectiveThroat period hPeriod) :
    intrinsicD8ScalarNormalFluxDensity period hPeriod splitting field variation
      normal point = 0 := by
  rw [intrinsicD8ScalarNormalFluxDensity_apply,
    throatTrace_apply_eq_zero_of_homogeneousDirichlet period hPeriod variation
      hDirichlet point]
  simp

/-- Hence the canonical integrated physical throat flux vanishes without any
integrability hypothesis. -/
theorem canonicalIntrinsicD8ScalarNormalBoundaryFlux_eq_zero_of_homogeneousDirichlet
    (splitting : DifferentialNormalSplitting period hPeriod)
    (field variation : SmoothScalarField period hPeriod)
    (normal : SmoothNormalTest period hPeriod)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation) :
    canonicalIntrinsicD8ScalarNormalBoundaryFlux period hPeriod splitting field
      variation normal = 0 := by
  unfold canonicalIntrinsicD8ScalarNormalBoundaryFlux
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall
    (intrinsicD8ScalarNormalFluxDensity_eq_zero_of_homogeneousDirichlet
      period hPeriod splitting field variation normal hDirichlet)

/-- Exact compatibility statement saying that the abstract weak-Euler boundary
functional is realized by the concrete normal flux above. -/
def IntrinsicD8ScalarNormalBoundaryFluxRealization
    (interface : IntrinsicD8ScalarDivergenceBoundaryInterface period hPeriod)
    (splitting : DifferentialNormalSplitting period hPeriod)
    (normal : SmoothNormalTest period hPeriod) : Prop :=
  ∀ (field variation : SmoothScalarField period hPeriod),
    generalLorentzScalarBoundaryFlux period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) interface field
        variation =
      canonicalIntrinsicD8ScalarNormalBoundaryFlux period hPeriod splitting
        field variation normal

/-- The concrete Dirichlet theorem discharges the abstract zero-flux premise
as soon as the boundary functional has the displayed normal realization. -/
theorem intrinsicD8WeakEulerBoundaryFlux_eq_zero_of_homogeneousDirichlet
    (interface : IntrinsicD8ScalarDivergenceBoundaryInterface period hPeriod)
    (splitting : DifferentialNormalSplitting period hPeriod)
    (normal : SmoothNormalTest period hPeriod)
    (hRealization : IntrinsicD8ScalarNormalBoundaryFluxRealization period
      hPeriod interface splitting normal)
    (field variation : SmoothScalarField period hPeriod)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation) :
    generalLorentzScalarBoundaryFlux period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) interface field
      variation = 0 := by
  rw [hRealization field variation]
  exact
    canonicalIntrinsicD8ScalarNormalBoundaryFlux_eq_zero_of_homogeneousDirichlet
      period hPeriod splitting field variation normal hDirichlet

/-- For a concretely realized normal flux, the prior weak-Euler theorem now
gives an actual stationary action derivative for homogeneous Dirichlet test
variations. -/
theorem canonicalIntrinsicD8HolonomicScalarAction_line_hasDerivAt_zero_of_homogeneousDirichlet
    (interface : IntrinsicD8ScalarDivergenceBoundaryInterface period hPeriod)
    (splitting : DifferentialNormalSplitting period hPeriod)
    (normal : SmoothNormalTest period hPeriod)
    (hRealization : IntrinsicD8ScalarNormalBoundaryFluxRealization period
      hPeriod interface splitting normal)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hAction : CanonicalGeneralLorentzScalarVariationIntegrable period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared field
      variation (intrinsicPointwiseFrame period hPeriod))
    (hWeakIntegrable : GeneralLorentzScalarWeakEulerIntegrable period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) interface massSquared
      field variation)
    (hWeak : GeneralLorentzScalarWeakEulerEquation period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) interface massSquared
      field variation)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation) :
    HasDerivAt
      (fun epsilon : Real =>
        canonicalGeneralLorentzHolonomicScalarAction period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared
          (scalarFieldLine period hPeriod field variation epsilon)
          (intrinsicPointwiseFrame period hPeriod))
      0 0 := by
  apply canonicalGeneralLorentzHolonomicScalarAction_line_hasDerivAt_zero
    period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      interface massSquared field variation hAction hWeakIntegrable hWeak
  exact intrinsicD8WeakEulerBoundaryFlux_eq_zero_of_homogeneousDirichlet
    period hPeriod interface splitting normal hRealization field variation
      hDirichlet

end

end P0EFTJanusMappingTorusIntrinsicD8ScalarDirichletFlux4D
end JanusFormal
