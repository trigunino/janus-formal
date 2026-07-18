import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVFunctionalVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D

/-!
# PT covariance of represented smooth spacetime BV functionals

The exact finite sheet-exchange laws are combined with the actual spacetime PT
pullback.  The already proved invariance of canonical Lorentz volume then gives
unconditional PT covariance of the integrated first variation, represented
ultralocal values and odd brackets, and the integrated CME.

The result concerns represented analytic ultralocal functionals on the constant
finite BV phase bundle.  It does not construct a bracket on arbitrary nonlocal
functionals or a completed infinite-dimensional field space.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVFunctionalPTCovariance4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVFunctionalVariation4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVPTCovariance4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVFunctionalVariation4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-! ## Exact fibre laws and integrated first variation -/

theorem smoothSpacetimeBVMasterFirstVariationDensity_pt
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
        (smoothSpacetimeBVPT period hPeriod field)
        (smoothSpacetimeBVPT period hPeriod variation) point =
      smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
        field variation (reflectedSpherePT period hPeriod point) := by
  rw [smoothSpacetimeBVMasterFirstVariationDensity_apply,
    smoothSpacetimeBVPT_apply, smoothSpacetimeBVPT_apply,
    smoothSpacetimeBVMasterFirstVariationDensity_apply]
  exact finiteMetricBVMasterFirstVariation_ptExchange
    (field (reflectedSpherePT period hPeriod point))
    (variation (reflectedSpherePT period hPeriod point))

theorem canonicalSmoothSpacetimeBVMasterFirstVariation_pt
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod
        (smoothSpacetimeBVPT period hPeriod field)
        (smoothSpacetimeBVPT period hPeriod variation) =
      canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod
        field variation := by
  unfold canonicalSmoothSpacetimeBVMasterFirstVariation
  calc
    (∫ point, smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
        (smoothSpacetimeBVPT period hPeriod field)
        (smoothSpacetimeBVPT period hPeriod variation) point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      ∫ point, smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
          field variation (reflectedSpherePT period hPeriod point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (smoothSpacetimeBVMasterFirstVariationDensity_pt period hPeriod
              field variation)
    _ = _ := intrinsicCanonicalLorentzVolumeMeasure_integral_pt period hPeriod
      (smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
        field variation)

/-! ## Represented ultralocal values -/

theorem smoothSpacetimeUltralocalBVFunctionalValueDensity_pt
    (functional : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (smoothUltralocalBVFunctionalPT functional).observable.value
        (smoothSpacetimeBVPT period hPeriod field point) =
      functional.observable.value
        (field (reflectedSpherePT period hPeriod point)) := by
  simp [smoothUltralocalBVFunctionalPT, finiteBVObservablePT,
    smoothSpacetimeBVPT_apply, finiteMetricBVPTExchange_involutive]

theorem canonicalSpacetimeUltralocalBVFunctionalValue_pt
    (functional : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    canonicalSpacetimeUltralocalBVFunctionalValue period hPeriod
        (smoothUltralocalBVFunctionalPT functional)
        (smoothSpacetimeBVPT period hPeriod field) =
      canonicalSpacetimeUltralocalBVFunctionalValue period hPeriod
        functional field := by
  unfold canonicalSpacetimeUltralocalBVFunctionalValue
  calc
    (∫ point, (smoothUltralocalBVFunctionalPT functional).observable.value
        (smoothSpacetimeBVPT period hPeriod field point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      ∫ point, functional.observable.value
          (field (reflectedSpherePT period hPeriod point))
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (smoothSpacetimeUltralocalBVFunctionalValueDensity_pt
              period hPeriod functional field)
    _ = _ := intrinsicCanonicalLorentzVolumeMeasure_integral_pt period hPeriod
      (fun point => functional.observable.value (field point))

/-! ## Represented ultralocal odd bracket and CME -/

theorem smoothSpacetimeUltralocalBVOddAntibracketDensity_pt
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    finiteBVOddAntibracket
        (smoothUltralocalBVFunctionalPT first).observable
        (smoothUltralocalBVFunctionalPT second).observable
        (smoothSpacetimeBVPT period hPeriod field point) =
      finiteBVOddAntibracket first.observable second.observable
        (field (reflectedSpherePT period hPeriod point)) := by
  change finiteBVOddAntibracket
      (finiteBVObservablePT first.observable)
      (finiteBVObservablePT second.observable)
      (smoothSpacetimeBVPT period hPeriod field point) = _
  rw [finiteBVOddAntibracket_pt_naturality]
  rw [smoothSpacetimeBVPT_apply,
    finiteMetricBVPTExchange_involutive]

theorem canonicalSpacetimeUltralocalBVOddAntibracket_pt
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    canonicalSpacetimeUltralocalBVOddAntibracket period hPeriod
        (smoothUltralocalBVFunctionalPT first)
        (smoothUltralocalBVFunctionalPT second)
        (smoothSpacetimeBVPT period hPeriod field) =
      canonicalSpacetimeUltralocalBVOddAntibracket period hPeriod
        first second field := by
  unfold canonicalSpacetimeUltralocalBVOddAntibracket
  calc
    (∫ point, finiteBVOddAntibracket
        (smoothUltralocalBVFunctionalPT first).observable
        (smoothUltralocalBVFunctionalPT second).observable
        (smoothSpacetimeBVPT period hPeriod field point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      ∫ point, finiteBVOddAntibracket first.observable second.observable
          (field (reflectedSpherePT period hPeriod point))
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (smoothSpacetimeUltralocalBVOddAntibracketDensity_pt
              period hPeriod first second field)
    _ = _ := intrinsicCanonicalLorentzVolumeMeasure_integral_pt period hPeriod
      (fun point => finiteBVOddAntibracket first.observable second.observable
        (field point))

/-- PT-stability of the integrated CME for the transported master functional
and the PT-transformed spacetime field. -/
theorem canonicalSmoothSpacetimeBV_ultralocal_integrated_CME_pt
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    canonicalSpacetimeUltralocalBVOddAntibracket period hPeriod
        (smoothUltralocalBVFunctionalPT
          smoothSpacetimeBVMasterUltralocalFunctional)
        (smoothUltralocalBVFunctionalPT
          smoothSpacetimeBVMasterUltralocalFunctional)
        (smoothSpacetimeBVPT period hPeriod field) = 0 := by
  rw [canonicalSpacetimeUltralocalBVOddAntibracket_pt period hPeriod]
  exact
    canonicalSmoothSpacetimeBV_ultralocal_integrated_classical_master_equation
      period hPeriod field

end
end P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVFunctionalPTCovariance4D
end JanusFormal
