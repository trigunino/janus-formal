import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceCharacterization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalDivergenceGluing4D

/-!
# First-order law of the regular-frame canonical divergence

The regular frame is used as an actual four-element basis.  Its smooth dual
coefficients extend the anholonomy-trace formula from basis vectors to every
smooth tangent field.  The resulting global operator is additive and obeys
the exact scalar Leibniz rule.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalDivergenceLaw4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameLeviCivitaTraceReduction4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceCharacterization4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Smooth coefficient of a tangent field in the genuine regular four-frame. -/
def regularFrameCanonicalCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (index : Index4) : SmoothScalarField period hPeriod :=
  generalMetricFiniteFrameCoefficient period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric vector index

@[simp]
theorem regularFrameCanonicalCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (index : Index4) (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalCoefficient period hPeriod metric vector index point =
      generalMetricFiniteFrameCoefficientAt period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric point index (vector point) :=
  rfl

theorem regularFrameCanonicalCoefficient_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : Index4) :
    regularFrameCanonicalCoefficient period hPeriod metric
        (0 : SmoothTangentField period hPeriod) index = 0 := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change generalMetricFiniteFrameCoefficientAt period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric point index 0 = 0
  simp

theorem regularFrameCanonicalCoefficient_add
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothTangentField period hPeriod)
    (index : Index4) :
    regularFrameCanonicalCoefficient period hPeriod metric (first + second)
        index =
      regularFrameCanonicalCoefficient period hPeriod metric first index +
        regularFrameCanonicalCoefficient period hPeriod metric second index := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change generalMetricFiniteFrameCoefficientAt period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric point index (first point + second point) = _
  rw [map_add]
  rfl

theorem regularFrameCanonicalCoefficient_smul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (scalar : SmoothScalarField period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (index : Index4) :
    regularFrameCanonicalCoefficient period hPeriod metric
        (smoothScalarSMulTangentField period hPeriod scalar vector) index =
      smoothScalarFieldMul period hPeriod scalar
        (regularFrameCanonicalCoefficient period hPeriod metric vector index) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change generalMetricFiniteFrameCoefficientAt period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric point index (scalar point • vector point) =
    scalar point *
      generalMetricFiniteFrameCoefficientAt period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric point index (vector point)
  rw [map_smul]
  rfl

/-- Regular-frame coefficients reconstruct every smooth tangent field. -/
theorem regularFrameCanonicalCoefficient_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    vector point = ∑ index : Index4,
      regularFrameCanonicalCoefficient period hPeriod metric vector index point •
        metric.frame index point := by
  change vector point = ∑ index : Fin 4,
    generalMetricFiniteFrameCoefficient period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric vector index point •
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric).vectorAt
        point index
  exact generalMetricFiniteFrame_reconstructs period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric vector point

/-- Reconstruction also reconstructs every scalar directional derivative. -/
theorem regularFrameCanonicalDirectionalDerivative_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (scalar : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    mvfderiv coverModelWithCorners scalar.toFun point (vector point) =
      ∑ index : Index4,
        regularFrameCanonicalCoefficient period hPeriod metric vector index point *
          frameDerivative period hPeriod Real
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            scalar point index := by
  rw [regularFrameCanonicalCoefficient_reconstructs period hPeriod metric
    vector point]
  simp only [map_sum, map_smul, smul_eq_mul, frameDerivative_eq_mfderiv]
  apply Finset.sum_congr rfl
  intro index _hIndex
  rfl

/-- Global extension of the basis anholonomy trace to arbitrary smooth
tangent fields. -/
def regularFrameAlgebraicCanonicalDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun := fun point => ∑ index : Index4,
    (frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameCanonicalCoefficient period hPeriod metric vector index)
        point index +
      regularFrameCanonicalCoefficient period hPeriod metric vector index point *
        regularFrameCanonicalDivergence period hPeriod metric index point)
  contMDiff_toFun := by
    apply ContMDiff.sum
    intro index _hIndex
    exact
      (frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (regularFrameCanonicalCoefficient period hPeriod metric vector index)
          index).contMDiff_toFun.add
        (smoothScalarFieldMul period hPeriod
          (regularFrameCanonicalCoefficient period hPeriod metric vector index)
          (regularFrameCanonicalDivergence period hPeriod metric index)
          ).contMDiff_toFun

@[simp]
theorem regularFrameAlgebraicCanonicalDivergence_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameAlgebraicCanonicalDivergence period hPeriod metric vector point =
      ∑ index : Index4,
        (frameDerivative period hPeriod Real
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            (regularFrameCanonicalCoefficient period hPeriod metric vector index)
            point index +
          regularFrameCanonicalCoefficient period hPeriod metric vector index
              point *
            regularFrameCanonicalDivergence period hPeriod metric index point) :=
  rfl

@[simp]
theorem regularFrameAlgebraicCanonicalDivergence_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    regularFrameAlgebraicCanonicalDivergence period hPeriod metric
        (0 : SmoothTangentField period hPeriod) = 0 := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [regularFrameAlgebraicCanonicalDivergence_apply]
  apply Finset.sum_eq_zero
  intro index _hIndex
  rw [regularFrameCanonicalCoefficient_zero period hPeriod metric index]
  rw [frameDerivative_eq_mfderiv]
  change mvfderiv coverModelWithCorners (fun _ => (0 : Real)) point
      ((regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric).vectorAt
        point index) + 0 * _ = 0
  rw [mvfderiv_const]
  simp

theorem regularFrameAlgebraicCanonicalDivergence_add
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothTangentField period hPeriod) :
    regularFrameAlgebraicCanonicalDivergence period hPeriod metric
        (first + second) =
      regularFrameAlgebraicCanonicalDivergence period hPeriod metric first +
        regularFrameAlgebraicCanonicalDivergence period hPeriod metric second := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [regularFrameAlgebraicCanonicalDivergence_apply]
  change _ =
    regularFrameAlgebraicCanonicalDivergence period hPeriod metric first point +
      regularFrameAlgebraicCanonicalDivergence period hPeriod metric second point
  rw [regularFrameAlgebraicCanonicalDivergence_apply,
    regularFrameAlgebraicCanonicalDivergence_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _hIndex
  rw [regularFrameCanonicalCoefficient_add period hPeriod metric first second
    index]
  rw [congrFun (congrFun
    (frameDerivative_add period hPeriod Real
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (regularFrameCanonicalCoefficient period hPeriod metric first index)
      (regularFrameCanonicalCoefficient period hPeriod metric second index))
    point) index]
  simp only [Pi.add_apply]
  let firstDerivative : Real :=
    frameDerivative period hPeriod Real
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (regularFrameCanonicalCoefficient period hPeriod metric first index)
      point index
  let secondDerivative : Real :=
    frameDerivative period hPeriod Real
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (regularFrameCanonicalCoefficient period hPeriod metric second index)
      point index
  let firstCoefficient : Real :=
    regularFrameCanonicalCoefficient period hPeriod metric first index point
  let secondCoefficient : Real :=
    regularFrameCanonicalCoefficient period hPeriod metric second index point
  let trace : Real :=
    regularFrameCanonicalDivergence period hPeriod metric index point
  change firstDerivative + secondDerivative +
      (firstCoefficient + secondCoefficient) * trace =
    (firstDerivative + firstCoefficient * trace) +
      (secondDerivative + secondCoefficient * trace)
  ring

/-- Additive presentation of the regular-frame divergence candidate. -/
def regularFrameAlgebraicCanonicalDivergenceAddMonoidHom
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothTangentField period hPeriod →+
      SmoothScalarField period hPeriod where
  toFun := regularFrameAlgebraicCanonicalDivergence period hPeriod metric
  map_zero' := regularFrameAlgebraicCanonicalDivergence_zero
    period hPeriod metric
  map_add' := regularFrameAlgebraicCanonicalDivergence_add
    period hPeriod metric

/-- Exact scalar Leibniz rule for the regular-frame divergence candidate. -/
theorem regularFrameAlgebraicCanonicalDivergence_smul_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (scalar : SmoothScalarField period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameAlgebraicCanonicalDivergence period hPeriod metric
        (smoothScalarSMulTangentField period hPeriod scalar vector) point =
      scalar point *
          regularFrameAlgebraicCanonicalDivergence period hPeriod metric vector
            point +
        mvfderiv coverModelWithCorners scalar.toFun point (vector point) := by
  rw [regularFrameAlgebraicCanonicalDivergence_apply,
    regularFrameAlgebraicCanonicalDivergence_apply]
  simp_rw [regularFrameCanonicalCoefficient_smul period hPeriod metric scalar
    vector]
  simp_rw [congrFun (congrFun
    (frameDerivative_mul period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) scalar
      (regularFrameCanonicalCoefficient period hPeriod metric vector _)) point) _]
  rw [regularFrameCanonicalDirectionalDerivative_reconstructs period hPeriod
    metric vector scalar point]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _hIndex
  change
    scalar point * _ + _ * _ +
        scalar point * _ * regularFrameCanonicalDivergence period hPeriod metric
          index point =
      scalar point * (_ + _ *
        regularFrameCanonicalDivergence period hPeriod metric index point) +
        _ * _
  ring

/-- Gate marker: the recollé regular-frame divergence has been extended to a
global first-order operator on all smooth tangent fields. -/
theorem regular_frame_canonical_divergence_law_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (scalar : SmoothScalarField period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameAlgebraicCanonicalDivergence period hPeriod metric
        (smoothScalarSMulTangentField period hPeriod scalar vector) point =
      scalar point *
          regularFrameAlgebraicCanonicalDivergence period hPeriod metric vector
            point +
        mvfderiv coverModelWithCorners scalar.toFun point (vector point) :=
  regularFrameAlgebraicCanonicalDivergence_smul_apply period hPeriod metric
    scalar vector point

end
end P0EFTJanusProgramPRegularFrameCanonicalDivergenceLaw4D
end JanusFormal
