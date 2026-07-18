import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicD8ScalarDirichletFlux4D

/-!
# Exact scalar Stokes contract for the intrinsic D8 normal flux

The weak scalar Euler interface is global on the four-dimensional quotient,
whereas the available normal flux is an integral on the one-sided throat.
Neither the latitude-fiber IPP nor the throat LL frame IPP identifies these
two different functionals.

This gate isolates the exact missing geometric input.  It asks for a
divergence satisfying Green's identity with the already constructed metric
normal pairing, then builds the abstract weak-Euler interface from that data.
Consequently the abstract boundary functional is definitionally the concrete
normal flux, and homogeneous Dirichlet data closes all downstream scalar
stationarity corollaries.  No divergence-free frame or global unit normal is
assumed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicD8ScalarNormalStokes4D

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
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarVariation4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricWeakScalarEuler4D
open P0EFTJanusMappingTorusGeometricNormalJunction4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusIntrinsicD8ScalarDirichletFlux4D

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

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

/-- Concrete boundary pairing for an arbitrary ambient tangent field.  The
normal remains a genuine section of the sign-clutched normal line. -/
def canonicalIntrinsicD8TangentNormalBoundaryFlux
    (splitting : DifferentialNormalSplitting period hPeriod)
    (vector : GeneralTangentVectorField period hPeriod)
    (variation : SmoothScalarField period hPeriod)
    (normal : SmoothNormalTest period hPeriod) : Real :=
  ∫ point,
      throatTrace period hPeriod Real variation point *
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod point)
          (vector (fixedThroatQuotientInclusion period hPeriod point))
          (splitting.representative point
            (differentialNormalFiberEquiv period hPeriod point
              (normal point)))
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- On the genuine metric gradient, the arbitrary-vector pairing is exactly
the concrete scalar normal flux constructed previously. -/
theorem canonicalIntrinsicD8TangentNormalBoundaryFlux_gradient_eq
    (splitting : DifferentialNormalSplitting period hPeriod)
    (field variation : SmoothScalarField period hPeriod)
    (normal : SmoothNormalTest period hPeriod) :
    canonicalIntrinsicD8TangentNormalBoundaryFlux period hPeriod splitting
        (generalLorentzScalarGradient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) field)
        variation normal =
      canonicalIntrinsicD8ScalarNormalBoundaryFlux period hPeriod splitting
        field variation normal := by
  unfold canonicalIntrinsicD8TangentNormalBoundaryFlux
    canonicalIntrinsicD8ScalarNormalBoundaryFlux
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    (intrinsicD8ScalarNormalFluxDensity_eq_gradientPairing period hPeriod
      splitting field variation normal point).symm

/-- Exact geometric formula needed to identify the boundary functional of an
already supplied weak-Euler interface.  It uses that interface's divergence
and replaces only its abstract boundary term by the concrete normal pairing. -/
def IntrinsicD8ScalarNormalStokesFormula
    (interface : IntrinsicD8ScalarDivergenceBoundaryInterface period hPeriod)
    (splitting : DifferentialNormalSplitting period hPeriod)
    (normal : SmoothNormalTest period hPeriod) : Prop :=
  ∀ (vector : GeneralTangentVectorField period hPeriod)
    (variation : SmoothScalarField period hPeriod),
    (∫ point,
        metricVolumeDensity period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) point
            (intrinsicPointwiseFrame period hPeriod point) *
          scalarDifferential period hPeriod variation point (vector point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      -(∫ point,
          metricVolumeDensity period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) point
              (intrinsicPointwiseFrame period hPeriod point) *
            variation point * interface.divergence vector point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) +
        canonicalIntrinsicD8TangentNormalBoundaryFlux period hPeriod
          splitting vector variation normal

/-- Comparing the interface IPP with the concrete Stokes formula uniquely
determines its boundary functional. -/
theorem boundaryFlux_eq_tangentNormalFlux_of_stokes
    (interface : IntrinsicD8ScalarDivergenceBoundaryInterface period hPeriod)
    (splitting : DifferentialNormalSplitting period hPeriod)
    (normal : SmoothNormalTest period hPeriod)
    (hStokes : IntrinsicD8ScalarNormalStokesFormula period hPeriod interface
      splitting normal)
    (vector : GeneralTangentVectorField period hPeriod)
    (variation : SmoothScalarField period hPeriod) :
    interface.boundaryFlux vector variation =
      canonicalIntrinsicD8TangentNormalBoundaryFlux period hPeriod splitting
        vector variation normal := by
  unfold IntrinsicD8ScalarNormalStokesFormula at hStokes
  have hAbstract := interface.integrationByParts vector variation
  have hConcrete := hStokes vector variation
  linarith

/-- Hence the single concrete Stokes formula discharges the older abstract
normal-flux realization predicate. -/
theorem intrinsicD8ScalarNormalBoundaryFluxRealization_of_stokes
    (interface : IntrinsicD8ScalarDivergenceBoundaryInterface period hPeriod)
    (splitting : DifferentialNormalSplitting period hPeriod)
    (normal : SmoothNormalTest period hPeriod)
    (hStokes : IntrinsicD8ScalarNormalStokesFormula period hPeriod interface
      splitting normal) :
    IntrinsicD8ScalarNormalBoundaryFluxRealization period hPeriod interface
      splitting normal := by
  intro field variation
  calc
    generalLorentzScalarBoundaryFlux period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) interface field
          variation =
        canonicalIntrinsicD8TangentNormalBoundaryFlux period hPeriod splitting
          (generalLorentzScalarGradient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) field)
          variation normal :=
      boundaryFlux_eq_tangentNormalFlux_of_stokes period hPeriod interface
        splitting normal hStokes
        (generalLorentzScalarGradient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) field)
        variation
    _ = canonicalIntrinsicD8ScalarNormalBoundaryFlux period hPeriod splitting
          field variation normal :=
      canonicalIntrinsicD8TangentNormalBoundaryFlux_gradient_eq period hPeriod
        splitting field variation normal

/-- The smallest missing global geometric input.  Besides the divergence
itself, its only field is Green's identity with the concrete throat pairing.
It does not claim that any weighted local frame is divergence-free. -/
structure IntrinsicD8ScalarNormalStokesContract
    (splitting : DifferentialNormalSplitting period hPeriod)
    (normal : SmoothNormalTest period hPeriod) where
  divergence : GeneralTangentVectorField period hPeriod →
    EffectiveQuotient period hPeriod → Real
  integrationByParts :
    ∀ (vector : GeneralTangentVectorField period hPeriod)
      (variation : SmoothScalarField period hPeriod),
      (∫ point,
          metricVolumeDensity period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) point
              (intrinsicPointwiseFrame period hPeriod point) *
            scalarDifferential period hPeriod variation point (vector point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
        -(∫ point,
            metricVolumeDensity period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod) point
                (intrinsicPointwiseFrame period hPeriod point) *
              variation point * divergence vector point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) +
          canonicalIntrinsicD8TangentNormalBoundaryFlux period hPeriod
            splitting vector variation normal

/-- The Stokes contract supplies the prior abstract interface with its
boundary functional fixed to the concrete metric-normal pairing. -/
def IntrinsicD8ScalarNormalStokesContract.toDivergenceBoundaryInterface
    {splitting : DifferentialNormalSplitting period hPeriod}
    {normal : SmoothNormalTest period hPeriod}
    (contract : IntrinsicD8ScalarNormalStokesContract period hPeriod splitting
      normal) :
    IntrinsicD8ScalarDivergenceBoundaryInterface period hPeriod where
  divergence := contract.divergence
  boundaryFlux := fun vector variation =>
    canonicalIntrinsicD8TangentNormalBoundaryFlux period hPeriod splitting
      vector variation normal
  integrationByParts := contract.integrationByParts

/-- The abstract scalar boundary functional is now identified exactly with
the previously constructed concrete normal flux. -/
theorem IntrinsicD8ScalarNormalStokesContract.boundaryFlux_eq_concrete
    {splitting : DifferentialNormalSplitting period hPeriod}
    {normal : SmoothNormalTest period hPeriod}
    (contract : IntrinsicD8ScalarNormalStokesContract period hPeriod splitting
      normal)
    (field variation : SmoothScalarField period hPeriod) :
    generalLorentzScalarBoundaryFlux period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (contract.toDivergenceBoundaryInterface period hPeriod) field
        variation =
      canonicalIntrinsicD8ScalarNormalBoundaryFlux period hPeriod splitting
        field variation normal := by
  exact canonicalIntrinsicD8TangentNormalBoundaryFlux_gradient_eq period
    hPeriod splitting field variation normal

/-- The contract therefore inhabits the older realization predicate. -/
theorem IntrinsicD8ScalarNormalStokesContract.toBoundaryFluxRealization
    {splitting : DifferentialNormalSplitting period hPeriod}
    {normal : SmoothNormalTest period hPeriod}
    (contract : IntrinsicD8ScalarNormalStokesContract period hPeriod splitting
      normal) :
    IntrinsicD8ScalarNormalBoundaryFluxRealization period hPeriod
      (contract.toDivergenceBoundaryInterface period hPeriod) splitting
      normal := by
  intro field variation
  exact contract.boundaryFlux_eq_concrete period hPeriod field variation

/-- Homogeneous Dirichlet data discharges the boundary functional of the
constructed global interface. -/
theorem IntrinsicD8ScalarNormalStokesContract.boundaryFlux_eq_zero_of_dirichlet
    {splitting : DifferentialNormalSplitting period hPeriod}
    {normal : SmoothNormalTest period hPeriod}
    (contract : IntrinsicD8ScalarNormalStokesContract period hPeriod splitting
      normal)
    (field variation : SmoothScalarField period hPeriod)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation) :
    generalLorentzScalarBoundaryFlux period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (contract.toDivergenceBoundaryInterface period hPeriod) field
        variation = 0 := by
  rw [contract.boundaryFlux_eq_concrete period hPeriod field variation]
  exact
    canonicalIntrinsicD8ScalarNormalBoundaryFlux_eq_zero_of_homogeneousDirichlet
      period hPeriod splitting field variation normal hDirichlet

/-- The covariant scalar first variation has the concrete flux, with no
remaining abstract-boundary identification premise. -/
theorem canonicalIntrinsicD8ScalarFirstVariation_eq_eulerPairing_add_normalFlux
    {splitting : DifferentialNormalSplitting period hPeriod}
    {normal : SmoothNormalTest period hPeriod}
    (contract : IntrinsicD8ScalarNormalStokesContract period hPeriod splitting
      normal)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hIntegrable : GeneralLorentzScalarWeakEulerIntegrable period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (contract.toDivergenceBoundaryInterface period hPeriod) massSquared
      field variation) :
    canonicalIntrinsicD8HolonomicScalarFirstVariation period hPeriod
        massSquared field variation =
      generalLorentzScalarEulerPairing period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          (contract.toDivergenceBoundaryInterface period hPeriod) massSquared
          field variation +
        canonicalIntrinsicD8ScalarNormalBoundaryFlux period hPeriod splitting
          field variation normal := by
  rw [canonicalIntrinsicD8HolonomicScalarFirstVariation_eq_eulerPairing_add_boundaryFlux
    period hPeriod (contract.toDivergenceBoundaryInterface period hPeriod)
      massSquared field variation hIntegrable]
  rw [contract.boundaryFlux_eq_concrete period hPeriod field variation]

/-- Under homogeneous Dirichlet data the same first variation is precisely
the covariant weak Euler pairing. -/
theorem canonicalIntrinsicD8ScalarFirstVariation_eq_eulerPairing_of_dirichlet
    {splitting : DifferentialNormalSplitting period hPeriod}
    {normal : SmoothNormalTest period hPeriod}
    (contract : IntrinsicD8ScalarNormalStokesContract period hPeriod splitting
      normal)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hIntegrable : GeneralLorentzScalarWeakEulerIntegrable period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (contract.toDivergenceBoundaryInterface period hPeriod) massSquared
      field variation)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation) :
    canonicalIntrinsicD8HolonomicScalarFirstVariation period hPeriod
        massSquared field variation =
      generalLorentzScalarEulerPairing period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (contract.toDivergenceBoundaryInterface period hPeriod) massSquared
        field variation := by
  rw [canonicalIntrinsicD8ScalarFirstVariation_eq_eulerPairing_add_normalFlux
    period hPeriod contract massSquared field variation hIntegrable,
    canonicalIntrinsicD8ScalarNormalBoundaryFlux_eq_zero_of_homogeneousDirichlet
      period hPeriod splitting field variation normal hDirichlet, add_zero]

/-- Dirichlet stationarity is equivalent to the weak covariant scalar Euler
equation for the interface constructed from the exact Stokes contract. -/
theorem canonicalIntrinsicD8ScalarFirstVariation_eq_zero_iff_weakEuler_of_dirichlet
    {splitting : DifferentialNormalSplitting period hPeriod}
    {normal : SmoothNormalTest period hPeriod}
    (contract : IntrinsicD8ScalarNormalStokesContract period hPeriod splitting
      normal)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hIntegrable : GeneralLorentzScalarWeakEulerIntegrable period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (contract.toDivergenceBoundaryInterface period hPeriod) massSquared
      field variation)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation) :
    canonicalIntrinsicD8HolonomicScalarFirstVariation period hPeriod
          massSquared field variation = 0 ↔
      GeneralLorentzScalarWeakEulerEquation period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (contract.toDivergenceBoundaryInterface period hPeriod) massSquared
        field variation := by
  rw [canonicalIntrinsicD8ScalarFirstVariation_eq_eulerPairing_of_dirichlet
    period hPeriod contract massSquared field variation hIntegrable hDirichlet]
  rfl

/-- The already differentiated intrinsic scalar action is stationary for a
weak Euler solution and homogeneous Dirichlet test variation. -/
theorem intrinsicD8ScalarAction_line_hasDerivAt_zero_of_normalStokes_dirichlet
    {splitting : DifferentialNormalSplitting period hPeriod}
    {normal : SmoothNormalTest period hPeriod}
    (contract : IntrinsicD8ScalarNormalStokesContract period hPeriod splitting
      normal)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (hAction : CanonicalGeneralLorentzScalarVariationIntegrable period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared field
      variation (intrinsicPointwiseFrame period hPeriod))
    (hWeakIntegrable : GeneralLorentzScalarWeakEulerIntegrable period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (contract.toDivergenceBoundaryInterface period hPeriod) massSquared
      field variation)
    (hWeak : GeneralLorentzScalarWeakEulerEquation period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (contract.toDivergenceBoundaryInterface period hPeriod) massSquared
      field variation)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation) :
    HasDerivAt
      (fun epsilon : Real =>
        canonicalGeneralLorentzHolonomicScalarAction period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared
          (scalarFieldLine period hPeriod field variation epsilon)
          (intrinsicPointwiseFrame period hPeriod))
      0 0 := by
  exact
    canonicalIntrinsicD8HolonomicScalarAction_line_hasDerivAt_zero_of_homogeneousDirichlet
      period hPeriod (contract.toDivergenceBoundaryInterface period hPeriod)
      splitting normal
      (contract.toBoundaryFluxRealization period hPeriod) massSquared field
      variation hAction hWeakIntegrable hWeak hDirichlet

end

end P0EFTJanusMappingTorusIntrinsicD8ScalarNormalStokes4D
end JanusFormal
