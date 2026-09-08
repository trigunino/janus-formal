import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2RiemannIntrinsicReconstruction4D

/-! # Canonically projected Ricci trace in a redundant finite frame -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2ProjectedRicciIntrinsic4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D
open P0EFTJanusMappingTorusCanonicalHolonomicScalarCurvatureNaturality4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D
open P0EFTJanusFiniteFrameC2ScalarCurvatureSmoothCoefficients4D
open P0EFTJanusFiniteFrameC2RiemannIntrinsicReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric metric : SmoothGeneralLorentzMetric period hPeriod)

/-- Canonical coefficient functional transported to a holonomic coordinate fiber. -/
def finiteFrameLocalCoefficientAt
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (index : Fin frame.count) : CoordinateVector →ₗ[Real] Real :=
  (generalMetricFiniteFrameCoefficientAt period hPeriod frame baseMetric
      (patch.coordinateMap coordinate) index).toLinearMap.comp
    ((Pi.basisFun Real (Fin 4)).equiv (patch.frame coordinate) (Equiv.refl (Fin 4))).toLinearMap

/-- The transported dual family reconstructs every coordinate vector. -/
theorem finiteFramePulledVector_reconstructs
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate vector : CoordinateVector) :
    vector = ∑ index : Fin frame.count,
      finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate index vector •
        finiteFramePulledVector period hPeriod frame patch index coordinate := by
  let e := (Pi.basisFun Real (Fin 4)).equiv (patch.frame coordinate) (Equiv.refl (Fin 4))
  have hVector (index : Fin frame.count) :
      e (finiteFramePulledVector period hPeriod frame patch index coordinate) =
        frame.vectorAt (patch.coordinateMap coordinate) index :=
    (coordinateMap_mfderiv_eq_frameEquiv period hPeriod patch coordinate _).symm.trans
      (coordinateMap_mfderiv_finiteFramePulledVector period hPeriod frame patch coordinate index)
  apply e.injective
  rw [map_sum]
  simp_rw [map_smul, hVector]
  change e vector = ∑ index : Fin frame.count,
    generalMetricFiniteFrameCoefficientAt period hPeriod frame baseMetric
        (patch.coordinateMap coordinate) index (e vector) •
      frame.vectorAt (patch.coordinateMap coordinate) index
  exact generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod frame baseMetric
    (patch.coordinateMap coordinate) (e vector)

private theorem trace_of_reconstruction
    {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    {ι : Type*} [Fintype ι]
    (vectors : ι → V) (coefficients : ι → V →ₗ[Real] Real)
    (reconstructs : ∀ vector, vector = ∑ i, coefficients i vector • vectors i)
    (operator : V →ₗ[Real] V) :
    LinearMap.trace Real V operator = ∑ i, coefficients i (operator (vectors i)) := by
  have hOperator : operator = ∑ i, (coefficients i).smulRight (operator (vectors i)) := by
    apply LinearMap.ext
    intro vector
    have h := congrArg operator (reconstructs vector)
    simpa only [LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul] using h
  have hTrace := congrArg (LinearMap.trace Real V) hOperator
  simpa only [map_sum, LinearMap.trace_smulRight] using hTrace

/-- Every coordinate endomorphism trace is computed by the transported redundant dual family. -/
theorem finiteFrameLocal_endomorphism_trace
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (operator : CoordinateVector →ₗ[Real] CoordinateVector) :
    LinearMap.trace Real CoordinateVector operator =
      ∑ index : Fin frame.count,
        finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate index
          (operator (finiteFramePulledVector period hPeriod frame patch index coordinate)) := by
  exact trace_of_reconstruction
    (finiteFramePulledVector period hPeriod frame patch · coordinate)
    (finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate)
    (finiteFramePulledVector_reconstructs period hPeriod frame baseMetric patch coordinate) operator

/-- Ricci coefficient with the canonical redundant-frame projection inserted before tracing. -/
def finiteFrameProjectedRicciCoefficientAt
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (first second : Fin frame.count) : Real :=
  ∑ traced : Fin frame.count,
    finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate traced
      (∑ upper : Fin frame.count,
        finiteFrameSmoothRiemannCoefficient period hPeriod frame baseMetric metric
              upper first traced second (patch.coordinateMap coordinate) •
          finiteFramePulledVector period hPeriod frame patch upper coordinate)

/-- The projected redundant Ricci coefficient is the intrinsic Ricci bilinear form. -/
theorem finiteFrameProjectedRicciCoefficientAt_eq_intrinsic
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (first second : Fin frame.count) :
    finiteFrameProjectedRicciCoefficientAt period hPeriod frame baseMetric metric patch coordinate
        first second =
      localRicciCurvatureVector period hPeriod metric patch coordinate
        (finiteFramePulledVector period hPeriod frame patch first coordinate)
        (finiteFramePulledVector period hPeriod frame patch second coordinate) := by
  unfold finiteFrameProjectedRicciCoefficientAt localRicciCurvatureVector
  rw [finiteFrameLocal_endomorphism_trace period hPeriod frame baseMetric patch coordinate]
  apply Finset.sum_congr rfl
  intro traced _
  rw [finiteFrameSmoothRiemann_reconstructs period hPeriod frame baseMetric metric patch coordinate
    first traced second]
  rfl

end
end P0EFTJanusFiniteFrameC2ProjectedRicciIntrinsic4D
end JanusFormal
