import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderRowAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularFrameCartanClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameTensorL2Transport4D

/-! Explicit canonical-volume adjoint tests for the actual second-order Faddeev--Popov rows. -/
namespace JanusFormal.P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
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
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D


open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorTrace4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D

open P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
open P0EFTJanusProgramPT12FrameTensorL2Transport4D

open P0EFTJanusProgramPT12DeDonderRowAdjoint4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "RF" => regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference

def cartanRowAdjointTest (first second : Fin 4) (test : SmoothScalarField period hPeriod) :
    CartanGhostL2 period hPeriod :=
  WithLp.toLp 2 fun direction => smoothToCanonicalPhysicalBulkL2 period hPeriod
    (regularFrameCartanColumnAdjoint period hPeriod reference metric.tensor first second direction test)

theorem cartanRowAdjointTest_pairing (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (first second : Fin 4) (test : SmoothScalarField period hPeriod) :
    inner Real (tensorCoefficientsL2 period hPeriod RF
      (generalMetricFrameCoefficient period hPeriod RF (smoothMetricCartanAction period hPeriod ghost metric.tensor)))
      (tensorSingleTest period hPeriod RF first second test) =
    inner Real (regularFrameGhostL2 period hPeriod (regularFrameCartanGhostCoefficient period hPeriod reference ghost))
      (cartanRowAdjointTest period hPeriod reference metric first second test) := by
  rw [tensorSingleTest_pairing]
  exact regularFrameCartan_actual_pairing period hPeriod reference metric.tensor ghost first second test

def fpTraceAdjointTest (test : SmoothScalarField period hPeriod) : CartanGhostL2 period hPeriod :=
  ∑ row, ∑ column, cartanRowAdjointTest period hPeriod reference metric column row
    (canonicalScalarMul period hPeriod (finiteFrameInverseMetricCoefficient period hPeriod RF metric metric row column) test)

def fpCovariantAdjointTest (derivative first last : Fin 4) (test : SmoothScalarField period hPeriod) :
    CartanGhostL2 period hPeriod :=
  cartanRowAdjointTest period hPeriod reference metric first last
    (canonicalFrameDerivativeAdjoint period hPeriod reference RF derivative test) -
    (∑ index, cartanRowAdjointTest period hPeriod reference metric index last (canonicalScalarMul period hPeriod
      (finiteFrameKoszulChristoffelCoefficient period hPeriod RF metric metric index derivative first) test)) -
    ∑ index, cartanRowAdjointTest period hPeriod reference metric first index (canonicalScalarMul period hPeriod
      (finiteFrameKoszulChristoffelCoefficient period hPeriod RF metric metric index derivative last) test)

def fpRowAdjointTest (last : Fin 4) (test : SmoothScalarField period hPeriod) : CartanGhostL2 period hPeriod :=
  (∑ derivative, ∑ first, fpCovariantAdjointTest period hPeriod reference metric derivative first last
    (canonicalScalarMul period hPeriod (finiteFrameInverseMetricCoefficient period hPeriod RF metric metric derivative first) test)) -
    (1 / 2 : Real) • fpTraceAdjointTest period hPeriod reference metric
      (canonicalFrameDerivativeAdjoint period hPeriod reference RF last test)

theorem fpTraceAdjointTest_pairing (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (test : SmoothScalarField period hPeriod) :
    inner Real (tensorCoefficientsL2 period hPeriod RF
      (generalMetricFrameCoefficient period hPeriod RF (smoothMetricCartanAction period hPeriod ghost metric.tensor)))
      (deDonderTraceAdjoint period hPeriod RF metric test) =
    inner Real (regularFrameGhostL2 period hPeriod (regularFrameCartanGhostCoefficient period hPeriod reference ghost))
      (fpTraceAdjointTest period hPeriod reference metric test) := by
  simp only [deDonderTraceAdjoint, fpTraceAdjointTest, inner_sum, cartanRowAdjointTest_pairing]
  rfl

theorem fpCovariantAdjointTest_pairing (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (derivative first last : Fin 4) (test : SmoothScalarField period hPeriod) :
    inner Real (tensorCoefficientsL2 period hPeriod RF
      (generalMetricFrameCoefficient period hPeriod RF (smoothMetricCartanAction period hPeriod ghost metric.tensor)))
      (deDonderCovariantRowAdjoint period hPeriod RF metric reference derivative first last test) =
    inner Real (regularFrameGhostL2 period hPeriod (regularFrameCartanGhostCoefficient period hPeriod reference ghost))
      (fpCovariantAdjointTest period hPeriod reference metric derivative first last test) := by
  simp only [deDonderCovariantRowAdjoint, fpCovariantAdjointTest, inner_sub_right, inner_sum,
    cartanRowAdjointTest_pairing]
  rfl

def fpSmoothRow (ghost : CInfinityDiffeomorphismGhost period hPeriod) (last : Fin 4) :
    SmoothScalarField period hPeriod :=
  deDonderRow period hPeriod RF metric
    (generalMetricFrameCoefficient period hPeriod RF (smoothMetricCartanAction period hPeriod ghost metric.tensor)) last

theorem fpSmoothRow_actual (ghost : GlobalDiffeomorphismGhostField period hPeriod)
    (last : Fin 4) (point : EffectiveQuotient period hPeriod) :
    fpSmoothRow period hPeriod reference metric ghost.field last point =
      globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric ghost point
        (reference.frame last point) :=
  deDonderRow_actual period hPeriod RF metric _ point last

theorem fpSmoothRow_pairing (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (last : Fin 4) (test : SmoothScalarField period hPeriod) :
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod (fpSmoothRow period hPeriod reference metric ghost last))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (regularFrameGhostL2 period hPeriod (regularFrameCartanGhostCoefficient period hPeriod reference ghost))
      (fpRowAdjointTest period hPeriod reference metric last test) := by
  rw [fpSmoothRow, deDonderRow_pairing period hPeriod RF metric reference]
  simp only [deDonderRowAdjoint, fpRowAdjointTest, inner_sub_right, inner_sum, real_inner_smul_right,
    fpCovariantAdjointTest_pairing, fpTraceAdjointTest_pairing]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12FaddeevPopovAdjoint4D
