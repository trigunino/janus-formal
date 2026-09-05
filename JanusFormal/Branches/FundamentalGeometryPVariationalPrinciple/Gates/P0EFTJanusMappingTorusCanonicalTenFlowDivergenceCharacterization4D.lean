import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLinear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D

/-!
# Algebraic characterization of canonical divergence

The smooth redundant dual reconstructs every tangent field from the ten
canonical generators.  Consequently additivity, Leibniz, and vanishing on
those generators uniquely determine divergence on every smooth field.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowDivergenceCharacterization4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLinear4D
open P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Exact reconstruction as a finite sum of smooth scalar multiples of the
ten packaged canonical generators. -/
theorem canonicalTenFlowVectorField_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    vector = ∑ index : Fin 10,
      smoothScalarSMulTangentField period hPeriod
        (canonicalTenFlowDualCoefficient period hPeriod metric vector index)
        (canonicalTenFlowVectorField period hPeriod index) := by
  apply ContMDiffSection.ext
  intro point
  change vector point = ∑ index : Fin 10,
    canonicalTenFlowDualCoefficient period hPeriod metric vector index point •
      canonicalTenFlowGeneratorAt period hPeriod point
        ((canonicalFlowIndexEquivFinTen).symm index)
  exact canonicalTenFlowDual_reconstructs period hPeriod metric vector point

/-- The three first-order laws which characterize canonical divergence on the
concrete ten-flow spanning family. -/
structure CanonicalTenFlowDivergenceLaw where
  operator : SmoothTangentField period hPeriod →+
    SmoothQuotientField period hPeriod Real
  leibniz : ∀ (scalar : SmoothQuotientField period hPeriod Real)
      (vector : SmoothTangentField period hPeriod)
      (point : EffectiveQuotient period hPeriod),
    operator (smoothScalarSMulTangentField period hPeriod scalar vector) point =
      scalar point * operator vector point +
        mvfderiv coverModelWithCorners scalar.toFun point (vector point)
  generator_zero : ∀ index : Fin 10,
    operator (canonicalTenFlowVectorField period hPeriod index) = 0

/-- The already constructed weak divergence satisfies the characterizing
laws. -/
def canonicalTenFlowDivergenceLaw
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CanonicalTenFlowDivergenceLaw period hPeriod where
  operator := canonicalTenFlowDivergenceAddMonoidHom period hPeriod metric
  leibniz := canonicalTenFlowDivergence_smul_apply period hPeriod metric
  generator_zero :=
    canonicalTenFlowDivergence_vectorField_eq_zero period hPeriod metric

/-- Two operators satisfying the three canonical laws agree on every smooth
tangent field. -/
theorem CanonicalTenFlowDivergenceLaw.operator_eq
    (first second : CanonicalTenFlowDivergenceLaw period hPeriod)
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    first.operator = second.operator := by
  ext vector point
  rw [canonicalTenFlowVectorField_reconstructs period hPeriod metric vector]
  rw [map_sum, map_sum]
  change
    (∑ index : Fin 10,
      first.operator
        (smoothScalarSMulTangentField period hPeriod
          (canonicalTenFlowDualCoefficient period hPeriod metric vector index)
          (canonicalTenFlowVectorField period hPeriod index)) point) =
    ∑ index : Fin 10,
      second.operator
        (smoothScalarSMulTangentField period hPeriod
          (canonicalTenFlowDualCoefficient period hPeriod metric vector index)
          (canonicalTenFlowVectorField period hPeriod index)) point
  apply Finset.sum_congr rfl
  intro index _hIndex
  rw [first.leibniz, second.leibniz]
  have hFirst := congrArg
    (fun field : SmoothQuotientField period hPeriod Real => field point)
    (first.generator_zero index)
  have hSecond := congrArg
    (fun field : SmoothQuotientField period hPeriod Real => field point)
    (second.generator_zero index)
  change first.operator
      (canonicalTenFlowVectorField period hPeriod index) point = 0 at hFirst
  change second.operator
      (canonicalTenFlowVectorField period hPeriod index) point = 0 at hSecond
  rw [hFirst, hSecond]

/-- Any operator obeying the canonical laws is the concrete ten-flow weak
divergence. -/
theorem CanonicalTenFlowDivergenceLaw.eq_canonical
    (law : CanonicalTenFlowDivergenceLaw period hPeriod)
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    law.operator = canonicalTenFlowDivergenceAddMonoidHom period hPeriod metric :=
  law.operator_eq period hPeriod
    (canonicalTenFlowDivergenceLaw period hPeriod metric) metric

/-- Gate marker: canonical divergence is uniquely fixed on all smooth
currents by additivity, Leibniz, and the ten geometric zero-divergence laws. -/
theorem canonical_ten_flow_divergence_characterization_gate
    (law : CanonicalTenFlowDivergenceLaw period hPeriod)
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    law.operator = canonicalTenFlowDivergenceAddMonoidHom period hPeriod metric :=
  law.eq_canonical period hPeriod metric

end
end P0EFTJanusMappingTorusCanonicalTenFlowDivergenceCharacterization4D
end JanusFormal
