import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameMetricCartanCoefficients4D

/-! A concrete canonical-volume adjoint pairing for the actual metric Cartan action. -/
namespace JanusFormal.P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)

def regularFrameCartanZeroth (first second direction : Fin 4) : SmoothScalarField period hPeriod :=
  canonicalFrameDerivativeSmooth period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) direction
    (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first second) -
  ∑ upper : Fin 4,
    (canonicalScalarMul period hPeriod
      (regularFrameStructureCoefficient period hPeriod reference direction first upper)
      (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor upper second) +
    canonicalScalarMul period hPeriod
      (regularFrameStructureCoefficient period hPeriod reference direction second upper)
      (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first upper))

theorem regularFrameCartanZeroth_apply (first second direction : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameCartanZeroth period hPeriod reference tensor first second direction point =
      frameDerivative period hPeriod Real (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
        (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first second) point direction -
      ∑ upper : Fin 4,
        (regularFrameStructureCoefficient period hPeriod reference direction first upper point *
          regularFrameSymmetricTensorCoefficient period hPeriod reference tensor upper second point +
        regularFrameStructureCoefficient period hPeriod reference direction second upper point *
          regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first upper point) := by
  simp only [regularFrameCartanZeroth, smoothScalarFieldSub_apply, canonicalScalar_sum_apply]
  rfl

def regularFrameCartanColumn (first second direction : Fin 4) :
    SmoothScalarField period hPeriod →ₗ[Real] SmoothScalarField period hPeriod :=
  canonicalFirstOrderColumn period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) first second
    (regularFrameCartanZeroth period hPeriod reference tensor first second direction)
    (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor direction second)
    (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first direction)

def regularFrameCartanColumnAdjoint (first second direction : Fin 4)
    (test : SmoothScalarField period hPeriod) : SmoothScalarField period hPeriod :=
  canonicalFirstOrderColumnAdjoint period hPeriod reference
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) first second
    (regularFrameCartanZeroth period hPeriod reference tensor first second direction)
    (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor direction second)
    (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first direction) test

/-- Exact first-order column decomposition of the intrinsic Cartan tensor. -/
theorem regularFrameCartan_eq_sum_columns
    (coefficients : Fin 4 → SmoothScalarField period hPeriod) (first second : Fin 4) :
    regularFrameSymmetricTensorCoefficient period hPeriod reference
      (smoothMetricCartanAction period hPeriod
        (regularFrameGhostFromCoefficients period hPeriod reference coefficients) tensor) first second =
      ∑ direction : Fin 4, regularFrameCartanColumn period hPeriod reference tensor first second direction
        (coefficients direction) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [smoothMetricCartanAction_regularFrameCoefficient, canonicalScalar_sum_apply]
  apply Finset.sum_congr rfl
  intro direction _
  change _ =
    regularFrameCartanZeroth period hPeriod reference tensor first second direction point *
        coefficients direction point +
      regularFrameSymmetricTensorCoefficient period hPeriod reference tensor direction second point *
        frameDerivative period hPeriod Real (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
          (coefficients direction) point first +
      regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first direction point *
        frameDerivative period hPeriod Real (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
          (coefficients direction) point second
  rw [regularFrameCartanZeroth_apply]
  simp only [mul_assoc, ← mul_add, ← Finset.mul_sum]
  ring

theorem regularFrameCartanColumn_pairing (first second direction : Fin 4)
    (field test : SmoothScalarField period hPeriod) :
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (regularFrameCartanColumn period hPeriod reference tensor first second direction field))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod field)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (regularFrameCartanColumnAdjoint period hPeriod reference tensor first second direction test)) :=
  canonicalFirstOrderColumn_pairing period hPeriod reference
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) first second _ _ _ field test

/-- The concrete formal-adjoint pairing holds for every actual smooth ghost. -/
theorem regularFrameCartan_actual_pairing
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (first second : Fin 4) (test : SmoothScalarField period hPeriod) :
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (regularFrameSymmetricTensorCoefficient period hPeriod reference
        (smoothMetricCartanAction period hPeriod ghost tensor) first second))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      ∑ direction : Fin 4,
        inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (regularFrameCartanGhostCoefficient period hPeriod reference ghost direction))
          (smoothToCanonicalPhysicalBulkL2 period hPeriod
            (regularFrameCartanColumnAdjoint period hPeriod reference tensor first second direction test)) := by
  rw [smoothMetricCartanAction_eq_reconstructedGhost period hPeriod reference ghost tensor,
    regularFrameCartan_eq_sum_columns, map_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro direction _
  exact regularFrameCartanColumn_pairing period hPeriod reference tensor first second direction _ test

end
end JanusFormal.P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
