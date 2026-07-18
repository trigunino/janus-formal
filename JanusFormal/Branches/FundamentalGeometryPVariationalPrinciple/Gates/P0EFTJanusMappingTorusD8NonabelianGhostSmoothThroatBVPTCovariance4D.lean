import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVFunctionalVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalLLCovariance4D

/-!
# PT covariance of the ultralocal throat BV sector

The actual throat PT involution is combined with exchange of the two positive
metric sheets.  The resulting action on smooth finite-phase BV fields is an
involution, commutes with BRST, preserves the master density fibrewise, and is
natural for the represented ultralocal odd bracket.

Integrated invariance is proved from exactly one explicit contract: the
existing canonical throat volume must be preserved by the actual throat PT
measurable equivalence.  No stronger or hidden measure claim is made.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVPTCovariance4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusD8NonabelianGhostPositiveMetricThroatBV4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVFunctionalVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

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

/-! ## Finite metric-sheet exchange -/

/-- Exchange of the two positive metric sheets, leaving the diagonal index
fixed. -/
def positiveMetricCoordinatePTEquiv :
    PositiveMetricCoordinate ≃ PositiveMetricCoordinate where
  toFun coordinate := (Fin.rev coordinate.1, coordinate.2)
  invFun coordinate := (Fin.rev coordinate.1, coordinate.2)
  left_inv coordinate := by
    rcases coordinate with ⟨sheet, component⟩
    simp
  right_inv coordinate := by
    rcases coordinate with ⟨sheet, component⟩
    simp

/-- The CE slot is not exchanged by PT. -/
def finiteMetricCEIndexPTEquiv :
    FiniteMetricCEIndex ≃ FiniteMetricCEIndex :=
  positiveMetricCoordinatePTEquiv.prodCongr (Equiv.refl (Fin 2))

@[simp]
theorem positiveMetricCoordinatePT_involutive
    (coordinate : PositiveMetricCoordinate) :
    positiveMetricCoordinatePTEquiv
        (positiveMetricCoordinatePTEquiv coordinate) = coordinate :=
  positiveMetricCoordinatePTEquiv.left_inv coordinate

@[simp]
theorem finiteMetricCEIndexPT_involutive
    (index : FiniteMetricCEIndex) :
    finiteMetricCEIndexPTEquiv (finiteMetricCEIndexPTEquiv index) = index :=
  finiteMetricCEIndexPTEquiv.left_inv index

/-- Orthogonal reindexing of the finite CE field by metric-sheet exchange. -/
def finiteMetricCEPTExchange :
    FiniteMetricCEField →ₗ[Real] FiniteMetricCEField where
  toFun field index := field (finiteMetricCEIndexPTEquiv index)
  map_add' first second := by
    funext index
    rfl
  map_smul' scalar field := by
    funext index
    rfl

@[simp]
theorem finiteMetricCEPTExchange_apply
    (field : FiniteMetricCEField) (index : FiniteMetricCEIndex) :
    finiteMetricCEPTExchange field index =
      field (finiteMetricCEIndexPTEquiv index) :=
  rfl

@[simp]
theorem finiteMetricCEPTExchange_involutive
    (field : FiniteMetricCEField) :
    finiteMetricCEPTExchange (finiteMetricCEPTExchange field) = field := by
  funext index
  simp

theorem finiteMetricCEPTExchange_commutes_differential
    (field : FiniteMetricCEField) :
    finiteMetricCEPTExchange (finiteMetricCEDifferential field) =
      finiteMetricCEDifferential (finiteMetricCEPTExchange field) := by
  funext index
  by_cases hSlot : index.2 = 0 <;>
    simp [finiteMetricCEPTExchange, finiteMetricCEIndexPTEquiv,
      finiteMetricCEDifferential, hSlot]

theorem finiteMetricCEPTExchange_commutes_transpose
    (field : FiniteMetricCEField) :
    finiteMetricCEPTExchange (finiteMetricCETranspose field) =
      finiteMetricCETranspose (finiteMetricCEPTExchange field) := by
  funext index
  by_cases hSlot : index.2 = 0 <;>
    simp [finiteMetricCEPTExchange, finiteMetricCEIndexPTEquiv,
      finiteMetricCETranspose, hSlot]

/-- The Euclidean finite pairing is invariant under sheet exchange. -/
theorem finiteMetricDot_ptExchange
    (first second : FiniteMetricCEField) :
    finiteMetricDot (finiteMetricCEPTExchange first)
        (finiteMetricCEPTExchange second) =
      finiteMetricDot first second := by
  change (∑ coordinate : PositiveMetricCoordinate, ∑ slot : Fin 2,
      first (positiveMetricCoordinatePTEquiv coordinate, slot) *
        second (positiveMetricCoordinatePTEquiv coordinate, slot)) =
    ∑ coordinate : PositiveMetricCoordinate, ∑ slot : Fin 2,
      first (coordinate, slot) * second (coordinate, slot)
  exact positiveMetricCoordinatePTEquiv.sum_comp
    (fun coordinate => ∑ slot : Fin 2,
      first (coordinate, slot) * second (coordinate, slot))

/-- Sheet exchange on the shifted finite BV cotangent. -/
def finiteMetricBVPTExchange :
    FiniteMetricBVPhase →ₗ[Real] FiniteMetricBVPhase :=
  finiteMetricCEPTExchange.prodMap finiteMetricCEPTExchange

@[simp]
theorem finiteMetricBVPTExchange_involutive
    (phase : FiniteMetricBVPhase) :
    finiteMetricBVPTExchange (finiteMetricBVPTExchange phase) = phase := by
  apply Prod.ext
  · exact finiteMetricCEPTExchange_involutive phase.1
  · exact finiteMetricCEPTExchange_involutive phase.2

theorem finiteMetricBVPTExchange_commutes_BRST
    (phase : FiniteMetricBVPhase) :
    finiteMetricBVPTExchange (finiteMetricBVBRST phase) =
      finiteMetricBVBRST (finiteMetricBVPTExchange phase) := by
  apply Prod.ext
  · exact finiteMetricCEPTExchange_commutes_differential phase.1
  · exact finiteMetricCEPTExchange_commutes_transpose phase.2

theorem finiteMetricBVMasterAction_ptExchange
    (phase : FiniteMetricBVPhase) :
    finiteMetricBVMasterAction (finiteMetricBVPTExchange phase) =
      finiteMetricBVMasterAction phase := by
  change finiteMetricDot (finiteMetricCEPTExchange phase.2)
      (finiteMetricCEDifferential (finiteMetricCEPTExchange phase.1)) =
    finiteMetricDot phase.2 (finiteMetricCEDifferential phase.1)
  rw [← finiteMetricCEPTExchange_commutes_differential]
  exact finiteMetricDot_ptExchange phase.2
    (finiteMetricCEDifferential phase.1)

theorem finiteMetricBVMasterFirstVariation_ptExchange
    (phase variation : FiniteMetricBVPhase) :
    finiteMetricBVMasterFirstVariation
        (finiteMetricBVPTExchange phase)
        (finiteMetricBVPTExchange variation) =
      finiteMetricBVMasterFirstVariation phase variation := by
  rw [finiteMetricBVMasterFirstVariation_eq_BRST,
    finiteMetricBVMasterFirstVariation_eq_BRST]
  rw [← finiteMetricBVPTExchange_commutes_BRST]
  change finiteMetricDot
        (finiteMetricCEPTExchange (finiteMetricBVBRST phase).2)
        (finiteMetricCEPTExchange variation.1) +
      finiteMetricDot
        (finiteMetricCEPTExchange (finiteMetricBVBRST phase).1)
        (finiteMetricCEPTExchange variation.2) = _
  rw [finiteMetricDot_ptExchange, finiteMetricDot_ptExchange]

/-! ## PT on actual smooth throat BV fields -/

private def finiteMetricBVPTExchangeContinuous :
    FiniteMetricBVPhase →L[Real] FiniteMetricBVPhase :=
  LinearMap.toContinuousLinearMap finiteMetricBVPTExchange

private def finiteMetricCEPTExchangeContinuous :
    FiniteMetricCEField →L[Real] FiniteMetricCEField :=
  LinearMap.toContinuousLinearMap finiteMetricCEPTExchange

/-- Actual throat PT pullback combined with exchange of the two metric sheets. -/
def smoothFiniteMetricBVPT
    (field : SmoothFiniteMetricBVField period hPeriod) :
    SmoothFiniteMetricBVField period hPeriod where
  toFun point := finiteMetricBVPTExchange
    (field (fixedThroatPT period hPeriod point))
  contMDiff_toFun :=
    finiteMetricBVPTExchangeContinuous.contDiff.contMDiff.comp
      (field.contMDiff_toFun.comp
        ((fixedThroatPT_contMDiff period hPeriod).of_le (by simp)))

@[simp]
theorem smoothFiniteMetricBVPT_apply
    (field : SmoothFiniteMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    smoothFiniteMetricBVPT period hPeriod field point =
      finiteMetricBVPTExchange
        (field (fixedThroatPT period hPeriod point)) :=
  rfl

@[simp]
theorem smoothFiniteMetricBVPT_involutive
    (field : SmoothFiniteMetricBVField period hPeriod) :
    smoothFiniteMetricBVPT period hPeriod
        (smoothFiniteMetricBVPT period hPeriod field) = field := by
  apply SmoothThroatField.ext period hPeriod FiniteMetricBVPhase
  intro point
  simp

/-- The actual PT/exchange involution is a chain map for throat BRST. -/
theorem smoothFiniteMetricBVPT_commutes_BRST
    (field : SmoothFiniteMetricBVField period hPeriod) :
    smoothFiniteMetricBVPT period hPeriod
        (smoothThroatBVBRST period hPeriod field) =
      smoothThroatBVBRST period hPeriod
        (smoothFiniteMetricBVPT period hPeriod field) := by
  apply SmoothThroatField.ext period hPeriod FiniteMetricBVPhase
  intro point
  exact finiteMetricBVPTExchange_commutes_BRST
    (field (fixedThroatPT period hPeriod point))

theorem smoothThroatBVMasterDensity_pt
    (field : SmoothFiniteMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    smoothThroatBVMasterDensity period hPeriod
        (smoothFiniteMetricBVPT period hPeriod field) point =
      smoothThroatBVMasterDensity period hPeriod field
        (fixedThroatPT period hPeriod point) := by
  rw [smoothThroatBVMasterDensity_apply,
    smoothFiniteMetricBVPT_apply,
    smoothThroatBVMasterDensity_apply]
  exact finiteMetricBVMasterAction_ptExchange
    (field (fixedThroatPT period hPeriod point))

theorem smoothThroatBVMasterFirstVariationDensity_pt
    (field variation : SmoothFiniteMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    smoothThroatBVMasterFirstVariationDensity period hPeriod
        (smoothFiniteMetricBVPT period hPeriod field)
        (smoothFiniteMetricBVPT period hPeriod variation) point =
      smoothThroatBVMasterFirstVariationDensity period hPeriod
        field variation (fixedThroatPT period hPeriod point) := by
  rw [smoothThroatBVMasterFirstVariationDensity_apply,
    smoothFiniteMetricBVPT_apply, smoothFiniteMetricBVPT_apply,
    smoothThroatBVMasterFirstVariationDensity_apply]
  exact finiteMetricBVMasterFirstVariation_ptExchange
    (field (fixedThroatPT period hPeriod point))
    (variation (fixedThroatPT period hPeriod point))

/-! ## The single canonical-measure contract -/

/-- Exact remaining measure contract for unconditional integrated PT
invariance of the canonical throat action. -/
abbrev CanonicalThroatPTMeasureInvariant : Prop :=
  MeasurePreserving (fixedThroatPTMeasurableEquiv period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

theorem canonicalSmoothThroatBVMasterAction_pt
    (hPT : CanonicalThroatPTMeasureInvariant period hPeriod)
    (field : SmoothFiniteMetricBVField period hPeriod) :
    canonicalSmoothThroatBVMasterAction period hPeriod
        (smoothFiniteMetricBVPT period hPeriod field) =
      canonicalSmoothThroatBVMasterAction period hPeriod field := by
  unfold canonicalSmoothThroatBVMasterAction
  calc
    (∫ point, smoothThroatBVMasterDensity period hPeriod
        (smoothFiniteMetricBVPT period hPeriod field) point
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point, smoothThroatBVMasterDensity period hPeriod field
          (fixedThroatPT period hPeriod point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (smoothThroatBVMasterDensity_pt period hPeriod field)
    _ = _ := hPT.integral_comp'
      (smoothThroatBVMasterDensity period hPeriod field)

theorem canonicalSmoothThroatBVMasterFirstVariation_pt
    (hPT : CanonicalThroatPTMeasureInvariant period hPeriod)
    (field variation : SmoothFiniteMetricBVField period hPeriod) :
    canonicalSmoothThroatBVMasterFirstVariation period hPeriod
        (smoothFiniteMetricBVPT period hPeriod field)
        (smoothFiniteMetricBVPT period hPeriod variation) =
      canonicalSmoothThroatBVMasterFirstVariation period hPeriod
        field variation := by
  unfold canonicalSmoothThroatBVMasterFirstVariation
  calc
    (∫ point, smoothThroatBVMasterFirstVariationDensity period hPeriod
        (smoothFiniteMetricBVPT period hPeriod field)
        (smoothFiniteMetricBVPT period hPeriod variation) point
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point, smoothThroatBVMasterFirstVariationDensity period hPeriod
          field variation (fixedThroatPT period hPeriod point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (smoothThroatBVMasterFirstVariationDensity_pt period hPeriod
              field variation)
    _ = _ := hPT.integral_comp'
      (smoothThroatBVMasterFirstVariationDensity period hPeriod field variation)

/-! ## Naturality of represented ultralocal observables -/

/-- PT/exchange transport of a finite canonical observable. -/
def finiteBVObservablePT (observable : FiniteBVObservable) :
    FiniteBVObservable where
  parity := observable.parity
  value phase := observable.value (finiteMetricBVPTExchange phase)
  fieldGradient phase := finiteMetricCEPTExchange
    (observable.fieldGradient (finiteMetricBVPTExchange phase))
  antifieldGradient phase := finiteMetricCEPTExchange
    (observable.antifieldGradient (finiteMetricBVPTExchange phase))

theorem finiteBVOddAntibracket_pt_naturality
    (first second : FiniteBVObservable)
    (phase : FiniteMetricBVPhase) :
    finiteBVOddAntibracket (finiteBVObservablePT first)
        (finiteBVObservablePT second) phase =
      finiteBVOddAntibracket first second
        (finiteMetricBVPTExchange phase) := by
  unfold finiteBVOddAntibracket finiteBVObservablePT
  rw [finiteMetricDot_ptExchange, finiteMetricDot_ptExchange]

/-- PT transport preserves the analytic ultralocal functional class. -/
def smoothUltralocalBVFunctionalPT
    (functional : SmoothUltralocalBVFunctional) :
    SmoothUltralocalBVFunctional where
  observable := finiteBVObservablePT functional.observable
  value_contDiff := functional.value_contDiff.comp
    finiteMetricBVPTExchangeContinuous.contDiff
  fieldGradient_contDiff :=
    finiteMetricCEPTExchangeContinuous.contDiff.comp
      (functional.fieldGradient_contDiff.comp
        finiteMetricBVPTExchangeContinuous.contDiff)
  antifieldGradient_contDiff :=
    finiteMetricCEPTExchangeContinuous.contDiff.comp
      (functional.antifieldGradient_contDiff.comp
        finiteMetricBVPTExchangeContinuous.contDiff)

theorem smoothUltralocalBVOddAntibracket_pt_pointwise
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    finiteBVOddAntibracket
        (smoothUltralocalBVFunctionalPT first).observable
        (smoothUltralocalBVFunctionalPT second).observable
        (smoothFiniteMetricBVPT period hPeriod field point) =
      finiteBVOddAntibracket first.observable second.observable
        (field (fixedThroatPT period hPeriod point)) := by
  change finiteBVOddAntibracket
      (finiteBVObservablePT first.observable)
      (finiteBVObservablePT second.observable)
      (smoothFiniteMetricBVPT period hPeriod field point) = _
  rw [finiteBVOddAntibracket_pt_naturality]
  rw [smoothFiniteMetricBVPT_apply,
    finiteMetricBVPTExchange_involutive]

theorem canonicalUltralocalBVFunctionalValue_pt
    (hPT : CanonicalThroatPTMeasureInvariant period hPeriod)
    (functional : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVField period hPeriod) :
    canonicalUltralocalBVFunctionalValue period hPeriod
        (smoothUltralocalBVFunctionalPT functional)
        (smoothFiniteMetricBVPT period hPeriod field) =
      canonicalUltralocalBVFunctionalValue period hPeriod functional field := by
  unfold canonicalUltralocalBVFunctionalValue
  calc
    (∫ point, (smoothUltralocalBVFunctionalPT functional).observable.value
        (smoothFiniteMetricBVPT period hPeriod field point)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point, functional.observable.value
          (field (fixedThroatPT period hPeriod point))
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          filter_upwards [] with point
          simp [smoothUltralocalBVFunctionalPT, finiteBVObservablePT]
    _ = _ := hPT.integral_comp'
      (fun point => functional.observable.value (field point))

/-- Integrated naturality of the canonical represented ultralocal odd
bracket. -/
theorem canonicalUltralocalBVOddAntibracket_pt
    (hPT : CanonicalThroatPTMeasureInvariant period hPeriod)
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVField period hPeriod) :
    canonicalUltralocalBVOddAntibracket period hPeriod
        (smoothUltralocalBVFunctionalPT first)
        (smoothUltralocalBVFunctionalPT second)
        (smoothFiniteMetricBVPT period hPeriod field) =
      canonicalUltralocalBVOddAntibracket period hPeriod
        first second field := by
  unfold canonicalUltralocalBVOddAntibracket
  calc
    (∫ point, finiteBVOddAntibracket
        (smoothUltralocalBVFunctionalPT first).observable
        (smoothUltralocalBVFunctionalPT second).observable
        (smoothFiniteMetricBVPT period hPeriod field point)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point, finiteBVOddAntibracket first.observable second.observable
          (field (fixedThroatPT period hPeriod point))
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (smoothUltralocalBVOddAntibracket_pt_pointwise period hPeriod
              first second field)
    _ = _ := hPT.integral_comp'
      (fun point => finiteBVOddAntibracket first.observable second.observable
        (field point))

/-- The integrated CME is stable under the transported PT master functional
and PT field. -/
theorem canonicalSmoothThroatBV_integrated_CME_pt
    (hPT : CanonicalThroatPTMeasureInvariant period hPeriod)
    (field : SmoothFiniteMetricBVField period hPeriod) :
    canonicalUltralocalBVOddAntibracket period hPeriod
        (smoothUltralocalBVFunctionalPT
          smoothThroatBVMasterUltralocalFunctional)
        (smoothUltralocalBVFunctionalPT
          smoothThroatBVMasterUltralocalFunctional)
        (smoothFiniteMetricBVPT period hPeriod field) = 0 := by
  rw [canonicalUltralocalBVOddAntibracket_pt period hPeriod hPT]
  exact canonicalSmoothThroatBV_integrated_classical_master_equation
    period hPeriod field

end
end P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVPTCovariance4D
end JanusFormal
