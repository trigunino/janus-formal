import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameAnholonomicPalatini4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D

/-! # Concrete torsion-free Palatini jet for the C² metric chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2TorsionFreePalatiniJet4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2RicciConnectionVelocity4D
open P0EFTJanusProgramPRegularFrameAnholonomicPalatini4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The reconstructed base Christoffel coefficients satisfy the correct
torsion-free relation in the global regular frame. -/
theorem regularGeneralMetricC0Christoffel_zero_torsionFree
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (upper first second : Index4) :
    regularGeneralMetricC0Christoffel period hPeriod metric 0
          upper first second point -
        regularGeneralMetricC0Christoffel period hPeriod metric 0
          upper second first point =
      regularFrameStructureCoefficientContinuous period hPeriod metric
        first second upper point := by
  rcases canonicalTotalHolonomicAtlasCover_covers period hPeriod point with
    ⟨patch, _hPatch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let firstConnection := regularFrameLocalCovariantDerivativeVector
    period hPeriod metric patch first second coordinate
  let secondConnection := regularFrameLocalCovariantDerivativeVector
    period hPeriod metric patch second first coordinate
  rw [regularGeneralMetricC0Christoffel_zero_apply period hPeriod metric
      patch coordinate upper first second,
    regularGeneralMetricC0Christoffel_zero_apply period hPeriod metric
      patch coordinate upper second first]
  change basis.repr firstConnection upper - basis.repr secondConnection upper = _
  change (basis.repr firstConnection - basis.repr secondConnection) upper = _
  rw [← map_sub]
  have hTorsion := regularFrameLocalCovariantDerivative_torsion
    period hPeriod metric patch coordinate first second
  change firstConnection - secondConnection = _ at hTorsion
  rw [hTorsion]
  rw [regularFrameLocalLieBracket_eq_sum period hPeriod metric patch coordinate
    first second]
  rw [map_sum]
  simp_rw [map_smul]
  change (∑ current : Index4,
      regularFrameStructureCoefficient period hPeriod metric first second
          current (patch.coordinateMap coordinate) *
        basis.repr
          (pulledRegularFrameVector period hPeriod metric patch current
            coordinate) upper) = _
  have hCoordinateEntry (current : Index4) :
      basis.repr
          (pulledRegularFrameVector period hPeriod metric patch current
            coordinate) upper =
        if current = upper then 1 else 0 := by
    rw [← pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
      current]
    exact basis.repr_self_apply current upper
  simp_rw [hCoordinateEntry]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true,
    regularFrameStructureCoefficientContinuous_apply]

/-- The concrete connection jet from Gate482, now carrying its proved
torsion-free geometry. -/
def regularGeneralMetricC2TorsionFreeConnectionVariationJetAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    TorsionFreeRegularFrameConnectionVariationJet4 where
  toRegularFrameConnectionVariationJet4 :=
    regularGeneralMetricC2ConnectionVariationJetAt
      period hPeriod metric direction point
  connection_torsionFree := by
    intro upper first second
    exact regularGeneralMetricC0Christoffel_zero_torsionFree
      period hPeriod metric point upper first second

/-- The genuine C² Ricci velocity is the covariant Palatini derivative of
the genuine connection velocity in the regular frame. -/
theorem regularGeneralMetricC0RicciVelocityAt_eq_palatini
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod)
    (first second : Index4) :
    regularGeneralMetricC0RicciVelocityAt period hPeriod metric direction point
        first second =
      regularFramePalatiniRicciVelocity
        (regularGeneralMetricC2TorsionFreeConnectionVariationJetAt
          period hPeriod metric direction point) first second := by
  rw [regularGeneralMetricC0RicciVelocityAt_eq_connection]
  exact regularFrameRicciVelocityFromConnection_eq_palatini
    (regularGeneralMetricC2TorsionFreeConnectionVariationJetAt
      period hPeriod metric direction point) first second

/-- Gate marker for the concrete C² Palatini Ricci identity. -/
theorem regular_general_metric_c2_torsion_free_palatini_jet_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod)
    (first second : Index4) :
    regularGeneralMetricC0RicciVelocityAt period hPeriod metric direction point
        first second =
      regularFramePalatiniRicciVelocity
        (regularGeneralMetricC2TorsionFreeConnectionVariationJetAt
          period hPeriod metric direction point) first second :=
  regularGeneralMetricC0RicciVelocityAt_eq_palatini
    period hPeriod metric direction point first second

end
end P0EFTJanusProgramPRegularGeneralMetricC2TorsionFreePalatiniJet4D
end JanusFormal
