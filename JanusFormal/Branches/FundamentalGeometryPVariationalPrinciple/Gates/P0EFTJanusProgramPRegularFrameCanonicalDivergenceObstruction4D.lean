import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalDivergenceLaw4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D

/-!
# Finite obstruction to identifying the regular-frame divergence

The genuine regular frame has Kronecker canonical coefficients, so the
algebraic divergence candidate takes its prescribed anholonomy-trace value on
each frame vector.  The characterization by the ten canonical flows then
reduces equality with weak canonical divergence to exactly ten smooth scalar
residuals.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalDivergenceObstruction4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLinear4D
open P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceCharacterization4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLaw4D

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

/-- A regular-frame basis vector has the expected Kronecker canonical
coefficient. -/
@[simp]
theorem regularFrameCanonicalCoefficient_frame_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (column row : Index4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCanonicalCoefficient period hPeriod metric
        (metric.frame column) row point =
      if row = column then 1 else 0 := by
  rw [regularFrameCanonicalCoefficient_apply]
  rw [regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate]
  rw [metric.frame_eq_basisFun]
  simp [Pi.basisFun_apply, Pi.single_apply]

/-- Field-level Kronecker coefficient identity. -/
theorem regularFrameCanonicalCoefficient_frame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (column row : Index4) :
    regularFrameCanonicalCoefficient period hPeriod metric
        (metric.frame column) row =
      constantSmoothField period hPeriod Real
        (if row = column then 1 else 0) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact regularFrameCanonicalCoefficient_frame_apply period hPeriod metric
    column row point

/-- On a regular-frame basis vector, the extended operator is exactly the
recollé anholonomy trace used to define it. -/
theorem regularFrameAlgebraicCanonicalDivergence_frame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (column : Index4) :
    regularFrameAlgebraicCanonicalDivergence period hPeriod metric
        (metric.frame column) =
      regularFrameCanonicalDivergence period hPeriod metric column := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [regularFrameAlgebraicCanonicalDivergence_apply]
  simp_rw [regularFrameCanonicalCoefficient_frame period hPeriod metric column]
  simp [frameDerivative_eq_mfderiv, constantSmoothField, mvfderiv_const]

/-- The only remaining obstruction to the divergence identification: one
smooth scalar residual for each concrete canonical generator. -/
def regularFrameCanonicalGeneratorDivergenceResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : Fin 10) : SmoothScalarField period hPeriod :=
  regularFrameAlgebraicCanonicalDivergence period hPeriod metric
    (canonicalTenFlowVectorField period hPeriod index)

/-- Vanishing of the ten generator residuals equips the regular-frame
candidate with the canonical characterizing laws. -/
def regularFrameAlgebraicCanonicalDivergenceLaw
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGenerators : ∀ index : Fin 10,
      regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
        index = 0) :
    CanonicalTenFlowDivergenceLaw period hPeriod where
  operator := regularFrameAlgebraicCanonicalDivergenceAddMonoidHom
    period hPeriod metric
  leibniz := regularFrameAlgebraicCanonicalDivergence_smul_apply
    period hPeriod metric
  generator_zero := hGenerators

/-- The ten finite residual equations imply equality of the two global
first-order operators on every smooth tangent field. -/
theorem regularFrameAlgebraicCanonicalDivergence_eq_canonical_of_generator_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGenerators : ∀ index : Fin 10,
      regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
        index = 0) :
    regularFrameAlgebraicCanonicalDivergenceAddMonoidHom period hPeriod metric =
      canonicalTenFlowDivergenceAddMonoidHom period hPeriod metric :=
  (regularFrameAlgebraicCanonicalDivergenceLaw period hPeriod metric
      hGenerators).eq_canonical period hPeriod metric

/-- Consequently the recollé regular-frame trace agrees, on every basis
vector, with the weak canonical divergence. -/
theorem regularFrameCanonicalDivergence_eq_canonical_of_generator_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGenerators : ∀ index : Fin 10,
      regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
        index = 0)
    (column : Index4) :
    regularFrameCanonicalDivergence period hPeriod metric column =
      canonicalTenFlowDivergence period hPeriod metric
        (metric.frame column) := by
  have hOperator := congrArg
    (fun operator : SmoothTangentField period hPeriod →+
        SmoothScalarField period hPeriod => operator (metric.frame column))
    (regularFrameAlgebraicCanonicalDivergence_eq_canonical_of_generator_zero
      period hPeriod metric hGenerators)
  change regularFrameAlgebraicCanonicalDivergence period hPeriod metric
      (metric.frame column) =
    canonicalTenFlowDivergence period hPeriod metric
      (metric.frame column) at hOperator
  rw [regularFrameAlgebraicCanonicalDivergence_frame period hPeriod metric
    column] at hOperator
  exact hOperator

/-- Gate marker: the global divergence bridge is reduced without hidden
analytic assumptions to ten explicit smooth scalar equations. -/
theorem regular_frame_canonical_divergence_obstruction_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGenerators : ∀ index : Fin 10,
      regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
        index = 0) :
    regularFrameAlgebraicCanonicalDivergenceAddMonoidHom period hPeriod metric =
      canonicalTenFlowDivergenceAddMonoidHom period hPeriod metric :=
  regularFrameAlgebraicCanonicalDivergence_eq_canonical_of_generator_zero
    period hPeriod metric hGenerators

end
end P0EFTJanusProgramPRegularFrameCanonicalDivergenceObstruction4D
end JanusFormal
