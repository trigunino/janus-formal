import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricBVThroatIntegrated4D

/-!
# Regularity of the intrinsic inverse-metric BV pairing

The pointwise inverse metric is expressed in each throat tangent
trivialization as the inverse of the local matrix-valued musical map.  Smooth
tensor sections give continuous local coefficients, inversion is continuous at
the everywhere-invertible intrinsic metric, and trace is a continuous
finite-dimensional linear functional.  Consequently every intrinsic pairing
density is continuous and hence integrable on the compact physical throat.

This closes the regularity contract for the represented ultralocal model.  It
does not construct derivative-dependent or general functional BV brackets.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicMetricBVThroatPairingRegularity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators Topology
open Bundle ContinuousLinearMap MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatIntegrated4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

private abbrev ModelTangent := ThroatCoverCoordinates

private abbrev ModelCotangent :=
  ModelTangent →L[Real] Real

private abbrev ModelEndomorphism :=
  ModelTangent →L[Real] ModelTangent

local instance throatTangentFiniteDimensional
    (point : EffectiveThroat period hPeriod) :
    FiniteDimensional Real (ThroatTangentFiber period hPeriod point) := by
  change FiniteDimensional Real ThroatCoverCoordinates
  infer_instance

/-! ## Local coordinate calculation -/

/-- Coefficients of a smooth covariant throat tensor in the tangent and dual
trivializations based at `anchor`. -/
private def throatTensorCoordinates
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveThroat period hPeriod) :
    ModelTangent →L[Real] ModelCotangent :=
  ContinuousLinearMap.inCoordinates ModelTangent
    (ThroatTangentFiber period hPeriod) ModelCotangent
    (ThroatCotangentFiber period hPeriod)
    anchor current anchor current (tensor.tensor current)

private theorem throatTensorCoordinates_continuousAt
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor : EffectiveThroat period hPeriod) :
    ContinuousAt
      (throatTensorCoordinates period hPeriod tensor anchor) anchor := by
  have hSmooth := tensor.tensor.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hSmooth
  exact hSmooth.2.continuousAt

private def intrinsicMetricCoordinates
    (anchor current : EffectiveThroat period hPeriod) :
    ModelTangent →L[Real] ModelCotangent :=
  throatTensorCoordinates period hPeriod
    (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1
    anchor current

private theorem intrinsicMetricCoordinates_isInvertible
    (anchor : EffectiveThroat period hPeriod) :
    (intrinsicMetricCoordinates period hPeriod anchor anchor).IsInvertible := by
  have hTangent : anchor ∈
      (trivializationAt ModelTangent
        (ThroatTangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelTangent
      (ThroatTangentFiber period hPeriod) anchor
  have hCotangent : anchor ∈
      (trivializationAt ModelCotangent
        (ThroatCotangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelCotangent
      (ThroatCotangentFiber period hPeriod) anchor
  have hFiber :
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor anchor =
        (intrinsicThroatMusical period hPeriod anchor :
          ThroatTangentFiber period hPeriod anchor →L[Real]
            ThroatCotangentFiber period hPeriod anchor) := by
    apply ContinuousLinearMap.ext
    intro vector
    exact (intrinsicThroatMusical_apply period hPeriod anchor vector).symm
  unfold intrinsicMetricCoordinates throatTensorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent, hFiber]
  exact isInvertible_equiv.comp
    (isInvertible_equiv.comp isInvertible_equiv)

/-- Local raised endomorphism obtained by inverting the metric coefficients. -/
private def raisedTensorCoordinates
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveThroat period hPeriod) : ModelEndomorphism :=
  (intrinsicMetricCoordinates period hPeriod anchor current).inverse.comp
    (throatTensorCoordinates period hPeriod tensor anchor current)

private theorem raisedTensorCoordinates_eq_inCoordinates
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveThroat period hPeriod)
    (hTangent : current ∈
      (trivializationAt ModelTangent
        (ThroatTangentFiber period hPeriod) anchor).baseSet)
    (hCotangent : current ∈
      (trivializationAt ModelCotangent
        (ThroatCotangentFiber period hPeriod) anchor).baseSet) :
    raisedTensorCoordinates period hPeriod tensor anchor current =
      ContinuousLinearMap.inCoordinates ModelTangent
        (ThroatTangentFiber period hPeriod) ModelTangent
        (ThroatTangentFiber period hPeriod)
        anchor current anchor current
        (raisedIntrinsicThroatTensorAt period hPeriod tensor current) := by
  have hFiber :
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor current =
        (intrinsicThroatMusical period hPeriod current :
          ThroatTangentFiber period hPeriod current →L[Real]
            ThroatCotangentFiber period hPeriod current) := by
    apply ContinuousLinearMap.ext
    intro vector
    exact (intrinsicThroatMusical_apply period hPeriod current vector).symm
  unfold raisedTensorCoordinates intrinsicMetricCoordinates
    throatTensorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent, hFiber,
    ContinuousLinearMap.inCoordinates_eq hTangent hCotangent,
    ContinuousLinearMap.inCoordinates_eq hTangent hTangent]
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearEquiv.symm_symm]
  apply ContinuousLinearMap.ext
  intro vector
  simp only [raisedIntrinsicThroatTensorAt, intrinsicThroatInverseMusical,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.symm_apply_apply]

private def modelTraceLinearMap : ModelEndomorphism →ₗ[Real] Real :=
  (LinearMap.trace Real ModelTangent).comp
    (ContinuousLinearMap.coeLM Real)

private def modelTrace : ModelEndomorphism →L[Real] Real :=
  LinearMap.toContinuousLinearMap modelTraceLinearMap

@[simp]
private theorem modelTrace_apply (endomorphism : ModelEndomorphism) :
    modelTrace endomorphism =
      LinearMap.trace Real ModelTangent endomorphism.toLinearMap :=
  rfl

private def modelIntrinsicThroatTensorPairing
    (first second : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveThroat period hPeriod) : Real :=
  modelTrace
    ((raisedTensorCoordinates period hPeriod first anchor current).comp
      (raisedTensorCoordinates period hPeriod second anchor current))

private theorem modelIntrinsicThroatTensorPairing_continuousAt
    (first second : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor : EffectiveThroat period hPeriod) :
    ContinuousAt
      (modelIntrinsicThroatTensorPairing period hPeriod first second anchor)
      anchor := by
  have hMetric : ContinuousAt
      (intrinsicMetricCoordinates period hPeriod anchor) anchor :=
    throatTensorCoordinates_continuousAt period hPeriod
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1 anchor
  have hInverse : ContinuousAt
      (fun current =>
        (intrinsicMetricCoordinates period hPeriod anchor current).inverse)
      anchor :=
    (intrinsicMetricCoordinates_isInvertible period hPeriod anchor
      |>.contDiffAt_map_inverse (n := ∞)).continuousAt.comp hMetric
  have hFirst := throatTensorCoordinates_continuousAt
    period hPeriod first anchor
  have hSecond := throatTensorCoordinates_continuousAt
    period hPeriod second anchor
  have hRaisedFirst := hInverse.clm_comp hFirst
  have hRaisedSecond := hInverse.clm_comp hSecond
  exact modelTrace.continuous.continuousAt.comp
    (hRaisedFirst.clm_comp hRaisedSecond)

private theorem intrinsicThroatTensorPairingAt_eq_model
    (first second : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveThroat period hPeriod)
    (hTangent : current ∈
      (trivializationAt ModelTangent
        (ThroatTangentFiber period hPeriod) anchor).baseSet)
    (hCotangent : current ∈
      (trivializationAt ModelCotangent
        (ThroatCotangentFiber period hPeriod) anchor).baseSet) :
    intrinsicThroatTensorPairingAt period hPeriod first second current =
      modelIntrinsicThroatTensorPairing period hPeriod
        first second anchor current := by
  rw [modelIntrinsicThroatTensorPairing,
    raisedTensorCoordinates_eq_inCoordinates period hPeriod first anchor current
      hTangent hCotangent,
    raisedTensorCoordinates_eq_inCoordinates period hPeriod second anchor current
      hTangent hCotangent]
  rw [modelTrace_apply]
  unfold intrinsicThroatTensorPairingAt
  let equivalence :=
    (trivializationAt ModelTangent
      (ThroatTangentFiber period hPeriod) anchor).continuousLinearEquivAt
        Real current hTangent
  have hTrace := LinearMap.trace_conj'
    ((raisedIntrinsicThroatTensorAt period hPeriod first current).toLinearMap *
      (raisedIntrinsicThroatTensorAt period hPeriod second current).toLinearMap)
    equivalence.toLinearEquiv
  rw [← hTrace]
  congr 1
  apply LinearMap.ext
  intro vector
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hTangent,
    ContinuousLinearMap.inCoordinates_eq hTangent hTangent]
  change equivalence
      (raisedIntrinsicThroatTensorAt period hPeriod first current
        (raisedIntrinsicThroatTensorAt period hPeriod second current
          (equivalence.symm vector))) =
    equivalence
      (raisedIntrinsicThroatTensorAt period hPeriod first current
        (equivalence.symm
          (equivalence
            (raisedIntrinsicThroatTensorAt period hPeriod second current
              (equivalence.symm vector)))))
  rw [equivalence.symm_apply_apply]

/-! ## Global continuity and unconditional integrability -/

theorem intrinsicThroatTensorPairingAt_continuous
    (first second : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    Continuous (fun point : EffectiveThroat period hPeriod =>
      intrinsicThroatTensorPairingAt period hPeriod first second point) := by
  rw [continuous_iff_continuousAt]
  intro anchor
  have hLocal := modelIntrinsicThroatTensorPairing_continuousAt
    period hPeriod first second anchor
  apply hLocal.congr_of_eventuallyEq
  have hTangent : ∀ᶠ current in 𝓝 anchor,
      current ∈ (trivializationAt ModelTangent
        (ThroatTangentFiber period hPeriod) anchor).baseSet :=
    (trivializationAt ModelTangent
      (ThroatTangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ModelTangent
          (ThroatTangentFiber period hPeriod) anchor)
  have hCotangent : ∀ᶠ current in 𝓝 anchor,
      current ∈ (trivializationAt ModelCotangent
        (ThroatCotangentFiber period hPeriod) anchor).baseSet :=
    (trivializationAt ModelCotangent
      (ThroatCotangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ModelCotangent
          (ThroatCotangentFiber period hPeriod) anchor)
  filter_upwards [hTangent, hCotangent] with current hTangent' hCotangent'
  exact intrinsicThroatTensorPairingAt_eq_model period hPeriod
    first second anchor current hTangent' hCotangent'

/-- The exact global continuity property consumed by the integrated gate. -/
abbrev IntrinsicThroatTensorPairPairingContinuous
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) : Prop :=
  Continuous (fun point : EffectiveThroat period hPeriod =>
    intrinsicThroatTensorPairPairingAt period hPeriod first second point)

theorem intrinsicThroatTensorPairPairingAt_continuous
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    IntrinsicThroatTensorPairPairingContinuous period hPeriod first second :=
  (intrinsicThroatTensorPairingAt_continuous period hPeriod first.1 second.1).add
    (intrinsicThroatTensorPairingAt_continuous period hPeriod first.2 second.2)

theorem intrinsicThroatInversePairingContinuityContract_proved :
    IntrinsicThroatInversePairingContinuityContract period hPeriod :=
  intrinsicThroatTensorPairPairingAt_continuous period hPeriod

theorem intrinsicThroatTensorPairPairingL1_unconditional
    (first second : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    IntrinsicThroatTensorPairPairingL1 period hPeriod first second :=
  intrinsicThroatTensorPairPairingL1_of_continuous period hPeriod first second
    (intrinsicThroatTensorPairPairingAt_continuous
      period hPeriod first second)

theorem intrinsicThroatContractibleMasterActionDensity_integrable_unconditional
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    Integrable
      (fun point : EffectiveThroat period hPeriod =>
        intrinsicThroatContractibleMasterActionAt period hPeriod phase point)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicThroatContractibleMasterActionDensity_integrable period hPeriod phase
    (intrinsicThroatTensorPairPairingL1_unconditional period hPeriod _ _)

theorem intrinsicThroatBVOddAntibracketDensity_integrable_unconditional
    (first second : IntrinsicThroatBVTraceObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    Integrable
      (fun point : EffectiveThroat period hPeriod =>
        intrinsicThroatBVOddAntibracketAt period hPeriod
          first second phase point)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicThroatBVOddAntibracketDensity_integrable period hPeriod
    first second phase
    (intrinsicThroatTensorPairPairingL1_unconditional period hPeriod _ _)
    (intrinsicThroatTensorPairPairingL1_unconditional period hPeriod _ _)

theorem canonicalIntrinsicThroatContractibleAntifieldAction_affine_expansion_unconditional
    (base variation : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (parameter : Real) :
    canonicalIntrinsicThroatContractibleAntifieldAction period hPeriod
        (smoothThroatGeneralMetricTensorPairAffineLine
          period hPeriod base variation parameter) =
      canonicalIntrinsicThroatContractibleAntifieldAction
          period hPeriod base +
        parameter * canonicalIntrinsicThroatTensorPairPairing
          period hPeriod base variation +
        parameter ^ 2 / 2 * canonicalIntrinsicThroatTensorPairPairing
          period hPeriod variation variation :=
  canonicalIntrinsicThroatContractibleAntifieldAction_affine_expansion
    period hPeriod base variation parameter
    (intrinsicThroatTensorPairPairingL1_unconditional period hPeriod _ _)
    (intrinsicThroatTensorPairPairingL1_unconditional period hPeriod _ _)
    (intrinsicThroatTensorPairPairingL1_unconditional period hPeriod _ _)

theorem canonicalIntrinsicThroatContractibleAntifieldAction_affine_hasDerivAt_unconditional
    (base variation : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    HasDerivAt
      (fun parameter : Real =>
        canonicalIntrinsicThroatContractibleAntifieldAction period hPeriod
          (smoothThroatGeneralMetricTensorPairAffineLine
            period hPeriod base variation parameter))
      (canonicalIntrinsicThroatTensorPairPairing
        period hPeriod base variation)
      0 :=
  canonicalIntrinsicThroatContractibleAntifieldAction_affine_hasDerivAt
    period hPeriod base variation
    (intrinsicThroatTensorPairPairingL1_unconditional period hPeriod _ _)
    (intrinsicThroatTensorPairPairingL1_unconditional period hPeriod _ _)
    (intrinsicThroatTensorPairPairingL1_unconditional period hPeriod _ _)

theorem canonicalIntrinsicThroatContractibleMasterAntifieldLine_hasDerivAt_unconditional
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (variation : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    HasDerivAt
      (canonicalIntrinsicThroatContractibleMasterAntifieldLine
        period hPeriod phase variation)
      (canonicalIntrinsicThroatTensorPairPairing period hPeriod
        ((intrinsicThroatContractibleMasterObservable
          period hPeriod).antifieldGradient phase) variation)
      0 :=
  canonicalIntrinsicThroatContractibleMasterAntifieldLine_hasDerivAt
    period hPeriod phase variation
    (intrinsicThroatTensorPairPairingL1_unconditional period hPeriod _ _)
    (intrinsicThroatTensorPairPairingL1_unconditional period hPeriod _ _)
    (intrinsicThroatTensorPairPairingL1_unconditional period hPeriod _ _)

end

end P0EFTJanusMappingTorusIntrinsicMetricBVThroatPairingRegularity4D
end JanusFormal
