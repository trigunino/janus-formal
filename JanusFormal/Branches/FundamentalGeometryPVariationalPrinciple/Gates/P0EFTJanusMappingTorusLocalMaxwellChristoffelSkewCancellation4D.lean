import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalMetricVolumeChristoffelTrace4D

/-! # Christoffel cancellation against the local Maxwell excitation -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalMaxwellChristoffelSkewCancellation4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators Manifold ContDiff Matrix
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusScalarStressLeviCivitaConnectionJet4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusLocalMaxwellStressVariation4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D
open P0EFTJanusProgramPRegularFrameHolonomicMaxwellDensityBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4
abbrev MetricDerivative4 :=
  P0EFTJanusScalarStressLeviCivitaConnectionJet4D.MetricDerivative4

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- A torsion-free Christoffel symbol contracts to zero with every skew
matrix in its two lower slots. -/
theorem leviCivitaChristoffel_skewContraction_eq_zero
    (metric : FixedSignMetric4) (dMetric : MetricDerivative4)
    (hMetricDerivative : ∀ derivative first second,
      dMetric derivative first second = dMetric derivative second first)
    (skew : Matrix4)
    (hSkew : ∀ first second, skew second first = -skew first second)
    (upper : Index4) :
    (∑ first : Index4, ∑ second : Index4,
      leviCivitaChristoffel metric dMetric upper first second *
        skew first second) = 0 := by
  let total := ∑ first : Index4, ∑ second : Index4,
    leviCivitaChristoffel metric dMetric upper first second * skew first second
  have hNeg : total = -total := by
    calc
      total = ∑ first : Index4, ∑ second : Index4,
          leviCivitaChristoffel metric dMetric upper second first *
            skew second first := by
        unfold total
        rw [Finset.sum_comm]
      _ = ∑ first : Index4, ∑ second : Index4,
          leviCivitaChristoffel metric dMetric upper first second *
            (-skew first second) := by
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro second _
        rw [leviCivitaChristoffel_torsionFree metric dMetric hMetricDerivative,
          hSkew]
      _ = -total := by
        unfold total
        simp only [mul_neg, Finset.sum_neg_distrib]
  change total = 0
  linarith

theorem regularHolonomicMaxwellExcitationField_skew
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Index4) :
    regularHolonomicMaxwellExcitationField period hPeriod metric potential patch
        component coordinate second first =
      -regularHolonomicMaxwellExcitationField period hPeriod metric potential
        patch component coordinate first second := by
  have hCurvature : ∀ first second,
      localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate second first =
        -localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate first second := by
    intro left right
    exact congrFun (congrFun
      (localGaugeCurvatureMatrix_transpose period hPeriod potential component
        patch coordinate) left) right
  have hSkew := maxwellExcitationAt_skew
    (localMetricVolumeFactor period hPeriod metric.metric patch coordinate)
    ((localMetricMatrix period hPeriod metric.metric patch coordinate)⁻¹)
    (localGaugeCurvatureMatrix period hPeriod potential component patch coordinate)
    hCurvature
  simpa [regularHolonomicMaxwellExcitationField, maxwellExcitationField,
    regularIntrinsicMaxwellLocalInverseField,
    regularIntrinsicMaxwellLocalCurvatureField] using
      congrFun (congrFun hSkew first) second

/-- The lower-index connection correction vanishes when contracted against
the holonomic Maxwell excitation. -/
theorem localLeviCivitaChristoffel_holonomicMaxwellExcitation_contraction_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (upper : Index4) :
    (∑ first : Index4, ∑ second : Index4,
      localLeviCivitaChristoffel period hPeriod metric.metric patch coordinate
          upper first second *
        regularHolonomicMaxwellExcitationField period hPeriod metric potential
          patch component coordinate first second) = 0 := by
  exact leviCivitaChristoffel_skewContraction_eq_zero
    (localFixedSignMetric period hPeriod metric.metric patch coordinate)
    (localMetricDerivative period hPeriod metric.metric patch coordinate)
    (fun derivative first second =>
      localMetricDerivative_symmetric period hPeriod metric.metric patch
        coordinate derivative first second)
    (regularHolonomicMaxwellExcitationField period hPeriod metric potential patch
      component coordinate)
    (regularHolonomicMaxwellExcitationField_skew period hPeriod metric potential
      component patch coordinate)
    upper

/-- Gate marker for the torsion-free/skew cancellation used in the Maxwell
density-divergence identity. -/
theorem local_maxwell_christoffel_skew_cancellation_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    ∀ (component : Fin 2)
        (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4) (upper : Index4),
      (∑ first : Index4, ∑ second : Index4,
        localLeviCivitaChristoffel period hPeriod metric.metric patch coordinate
            upper first second *
          regularHolonomicMaxwellExcitationField period hPeriod metric potential
            patch component coordinate first second) = 0 :=
  localLeviCivitaChristoffel_holonomicMaxwellExcitation_contraction_eq_zero
    period hPeriod metric potential

end
end P0EFTJanusMappingTorusLocalMaxwellChristoffelSkewCancellation4D
end JanusFormal
