import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwellLocalBoxWeakStrong4D

/-! # Maxwell weak--strong reduction with a local reference density -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwellLocalDensityWeakStrong4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusMappingTorusLocalPalatiniBoxStokes4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D
open P0EFTJanusProgramPRegularFrameMaxwellWeightedEulerBoundary4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwellLocalBoxStokes4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwellLocalBoxWeakStrong4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev FaceCoordinate3 := Fin 3 → Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- A smooth positive Radon--Nikodym density in a holonomic coordinate chart. -/
structure SmoothPositiveReferenceDensity4 where
  toFun : Vector4 → Real
  contDiff_toFun : ContDiff Real ∞ toFun
  positive : ∀ coordinate, 0 < toFun coordinate

instance : CoeFun SmoothPositiveReferenceDensity4 (fun _ => Vector4 → Real) :=
  ⟨SmoothPositiveReferenceDensity4.toFun⟩

/-- Boundary current multiplied by the local density of the reference
measure. -/
def regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) : Vector4 → Vector4 :=
  fun coordinate => density coordinate •
    regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric potential
      variation component patch coordinate

theorem regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent_contDiff
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent period hPeriod
        density metric potential variation component patch) :=
  density.contDiff_toFun.smul
    (regularIntrinsicMaxwellLocalBoundaryCurrent_contDiff period hPeriod metric
      potential variation component patch)

/-- Ordinary divergence of the density-weighted boundary current. -/
def regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ first : Index4,
    fderiv Real
        (regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent period hPeriod
          density metric potential variation component patch)
        coordinate (Pi.single first 1) first

/-- The derivative-of-density term required by the product rule. -/
def regularIntrinsicMaxwellLocalReferenceDensityCorrection
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ first : Index4,
    fderiv Real density coordinate (Pi.single first 1) *
      regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric
        potential variation component patch coordinate first

/-- Exact coordinate product rule for the reference density. -/
theorem regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence_eq
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence period hPeriod
        density metric potential variation component patch coordinate =
      density coordinate *
          regularIntrinsicMaxwellLocalBoundaryDivergence period hPeriod metric
            potential variation component patch coordinate +
        regularIntrinsicMaxwellLocalReferenceDensityCorrection period hPeriod
          density metric potential variation component patch coordinate := by
  let current := regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod
    metric potential variation component patch
  have hDensity : DifferentiableAt Real density coordinate :=
    density.contDiff_toFun.differentiable (by simp) coordinate
  have hCurrent : DifferentiableAt Real current coordinate :=
    (regularIntrinsicMaxwellLocalBoundaryCurrent_contDiff period hPeriod metric
      potential variation component patch).differentiable (by simp) coordinate
  have hDerivative (first : Index4) :
      fderiv Real (fun currentCoordinate =>
          density currentCoordinate • current currentCoordinate) coordinate
          (Pi.single first 1) first =
        density coordinate *
            fderiv Real current coordinate (Pi.single first 1) first +
          fderiv Real density coordinate (Pi.single first 1) *
            current coordinate first := by
    change fderiv Real (density.toFun • current) coordinate
      (Pi.single first 1) first = _
    have hProduct := fderiv_smul hDensity hCurrent
    have hApplied := congrArg
      (fun derivativeMap : Vector4 →L[Real] Vector4 =>
        derivativeMap (Pi.single first 1)) hProduct
    have hComponent := congrArg (fun value : Vector4 => value first) hApplied
    simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hComponent
  unfold regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence
    regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent
    regularIntrinsicMaxwellLocalBoundaryDivergence
    regularIntrinsicMaxwellLocalReferenceDensityCorrection
  change
    (∑ first : Index4,
      fderiv Real (fun currentCoordinate =>
          density currentCoordinate • current currentCoordinate) coordinate
        (Pi.single first 1) first) = _
  simp_rw [hDerivative]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The corrected strong pairing selected after pulling the reference measure
back to coordinates. -/
def regularFrameMaxwellReferenceDensityStrongPairing
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  density coordinate *
      regularFrameMaxwellStrongPairing period hPeriod metric potential variation
        component patch coordinate +
    regularIntrinsicMaxwellLocalReferenceDensityCorrection period hPeriod
      density metric potential variation component patch coordinate

/-- Pulling the action density through a nonconstant coordinate measure adds
exactly the derivative-of-density correction to the strong residual. -/
theorem density_mul_regularMaxwellFirstVariationField_eq_corrected_sub_divergence
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    density coordinate *
        regularMaxwellFirstVariationField period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation)
          (patch.coordinateMap coordinate) =
      ∑ component : Fin 2,
        (regularFrameMaxwellReferenceDensityStrongPairing period hPeriod density
            metric potential variation component patch coordinate -
          regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence period
            hPeriod density metric potential variation component patch
            coordinate) := by
  rw [regularMaxwellFirstVariationField_eq_strong_sub_analyticDivergence period
    hPeriod metric potential variation patch coordinate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _
  rw [regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence_eq]
  unfold regularFrameMaxwellReferenceDensityStrongPairing
  ring

theorem regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence_integrableOn
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    IntegrableOn
      (regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence period hPeriod
        density metric potential variation component patch)
      (Icc box.lower box.upper) := by
  have hCurrent :=
    regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent_contDiff period
      hPeriod density metric potential variation component patch
  have hDerivative : Continuous (fun coordinate =>
      fderiv Real
        (regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent period hPeriod
          density metric potential variation component patch) coordinate) :=
    hCurrent.continuous_fderiv (by simp)
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact Continuous.continuousOn (by
    unfold regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence
    fun_prop)

/-- Stokes for the density-weighted Maxwell current. -/
theorem integral_regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence_eq_faces
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    (∫ coordinate in Icc box.lower box.upper,
      regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence period hPeriod
        density metric potential variation component patch coordinate) =
      ∑ index : Index4,
        ((∫ face in
              Icc (box.lower ∘ index.succAbove)
                (box.upper ∘ index.succAbove),
            regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent period hPeriod
              density metric potential variation component patch
                (index.insertNth (box.upper index) face) index) -
          ∫ face in
              Icc (box.lower ∘ index.succAbove)
                (box.upper ∘ index.succAbove),
            regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent period hPeriod
              density metric potential variation component patch
                (index.insertNth (box.lower index) face) index) := by
  let current := regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent period
    hPeriod density metric potential variation component patch
  let derivative : Vector4 → Vector4 →L[Real] Vector4 :=
    fun coordinate => fderiv Real current coordinate
  have hCurrent : ContDiff Real ∞ current :=
    regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent_contDiff period
      hPeriod density metric potential variation component patch
  have hStokes :=
    MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
      box.lower box.upper box.lower_le_upper current derivative ∅
      Set.countable_empty hCurrent.continuous.continuousOn
      (fun coordinate _ =>
        (hCurrent.differentiable (by simp) coordinate).hasFDerivAt)
      (regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence_integrableOn
        period hPeriod density metric potential variation component patch box)
  simpa [current, derivative,
    regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence] using hStokes

/-- Dirichlet test data annihilate the density-weighted boundary divergence. -/
theorem integral_regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence_eq_zero
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4)
    (boundary : RegularIntrinsicMaxwellLocalBoxDirichlet period hPeriod
      variation patch box)
    (component : Fin 2) :
    (∫ coordinate in Icc box.lower box.upper,
      regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence period hPeriod
        density metric potential variation component patch coordinate) = 0 := by
  rw [integral_regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence_eq_faces]
  apply Finset.sum_eq_zero
  intro index _
  have hFront (face : FaceCoordinate3) :
      regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent period hPeriod
          density metric potential variation component patch
            (index.insertNth (box.upper index) face) index = 0 := by
    unfold regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent
    change density.toFun _ *
      regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric
        potential variation component patch
          (index.insertNth (box.upper index) face) index = 0
    rw [regularIntrinsicMaxwellLocalBoundaryCurrent_front_eq_zero period hPeriod
      metric potential variation patch box boundary component index face]
    simp
  have hBack (face : FaceCoordinate3) :
      regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent period hPeriod
          density metric potential variation component patch
            (index.insertNth (box.lower index) face) index = 0 := by
    unfold regularIntrinsicMaxwellLocalDensitizedBoundaryCurrent
    change density.toFun _ *
      regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric
        potential variation component patch
          (index.insertNth (box.lower index) face) index = 0
    rw [regularIntrinsicMaxwellLocalBoundaryCurrent_back_eq_zero period hPeriod
      metric potential variation patch box boundary component index face]
    simp
  simp_rw [hFront, hBack]
  simp

theorem regularFrameMaxwellReferenceDensityStrongPairing_integrableOn
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    IntegrableOn
      (regularFrameMaxwellReferenceDensityStrongPairing period hPeriod density
        metric potential variation component patch)
      (Icc box.lower box.upper) := by
  have hDensity : Continuous density := density.contDiff_toFun.continuous
  have hDensityDerivative : Continuous (fun coordinate =>
      fderiv Real density coordinate) :=
    density.contDiff_toFun.continuous_fderiv (by simp)
  have hCurrent :=
    regularIntrinsicMaxwellLocalBoundaryCurrent_contDiff period hPeriod metric
      potential variation component patch
  have hStrong : Continuous (fun coordinate =>
      regularFrameMaxwellStrongPairing period hPeriod metric potential variation
        component patch coordinate) :=
    (regularIntrinsicMaxwellLocalEulerPairing_continuous period hPeriod metric
      potential variation component patch).congr (fun coordinate =>
        regularIntrinsicMaxwellEulerPairing_eq_weightedStrongPairing period
          hPeriod metric potential variation component patch coordinate)
  have hCorrection : Continuous (fun coordinate =>
      ∑ first : Index4,
        fderiv Real density coordinate (Pi.single first 1) *
          regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric
            potential variation component patch coordinate first) := by
    apply continuous_finsetSum
    intro first _
    exact (hDensityDerivative.clm_apply continuous_const).mul
      ((continuous_apply first).comp hCurrent.continuous)
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact ((hDensity.mul hStrong).add hCorrection).continuousOn

/-- Correct local weak--strong identity for a nonconstant smooth reference
density. -/
theorem integral_density_mul_regularMaxwellFirstVariationField_eq_correctedStrong
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4)
    (boundary : RegularIntrinsicMaxwellLocalBoxDirichlet period hPeriod
      variation patch box) :
    (∫ coordinate in Icc box.lower box.upper,
      density coordinate *
        regularMaxwellFirstVariationField period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation)
          (patch.coordinateMap coordinate)) =
      ∫ coordinate in Icc box.lower box.upper,
        ∑ component : Fin 2,
          regularFrameMaxwellReferenceDensityStrongPairing period hPeriod
            density metric potential variation component patch coordinate := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun coordinate =>
    density_mul_regularMaxwellFirstVariationField_eq_corrected_sub_divergence
      period hPeriod density metric potential variation patch coordinate)]
  calc
    (∫ coordinate in Icc box.lower box.upper,
      ∑ component : Fin 2,
        (regularFrameMaxwellReferenceDensityStrongPairing period hPeriod density
            metric potential variation component patch coordinate -
          regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence period
            hPeriod density metric potential variation component patch
            coordinate)) =
        ∑ component : Fin 2,
          ∫ coordinate in Icc box.lower box.upper,
            (regularFrameMaxwellReferenceDensityStrongPairing period hPeriod
                density metric potential variation component patch coordinate -
              regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence period
                hPeriod density metric potential variation component patch
                coordinate) := by
      rw [integral_finsetSum]
      intro component _
      exact
        (regularFrameMaxwellReferenceDensityStrongPairing_integrableOn period
          hPeriod density metric potential variation component patch box).sub
          (regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence_integrableOn
            period hPeriod density metric potential variation component patch
              box)
    _ = ∑ component : Fin 2,
          ((∫ coordinate in Icc box.lower box.upper,
              regularFrameMaxwellReferenceDensityStrongPairing period hPeriod
                density metric potential variation component patch coordinate) -
            ∫ coordinate in Icc box.lower box.upper,
              regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence period
                hPeriod density metric potential variation component patch
                coordinate) := by
      apply Finset.sum_congr rfl
      intro component _
      rw [integral_sub
        (regularFrameMaxwellReferenceDensityStrongPairing_integrableOn period
          hPeriod density metric potential variation component patch box)
        (regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence_integrableOn
          period hPeriod density metric potential variation component patch box)]
    _ = ∑ component : Fin 2,
          ∫ coordinate in Icc box.lower box.upper,
            regularFrameMaxwellReferenceDensityStrongPairing period hPeriod
              density metric potential variation component patch coordinate := by
      apply Finset.sum_congr rfl
      intro component _
      rw [integral_regularIntrinsicMaxwellLocalDensitizedBoundaryDivergence_eq_zero
        period hPeriod density metric potential variation patch box boundary
          component, sub_zero]
    _ = ∫ coordinate in Icc box.lower box.upper,
          ∑ component : Fin 2,
            regularFrameMaxwellReferenceDensityStrongPairing period hPeriod
              density metric potential variation component patch coordinate := by
      symm
      rw [integral_finsetSum]
      intro component _
      exact regularFrameMaxwellReferenceDensityStrongPairing_integrableOn period
        hPeriod density metric potential variation component patch box

/-- Gate marker: the missing local reference-measure correction is explicit
and its densitized boundary flux vanishes under Dirichlet data. -/
theorem regular_general_metric_c2_smooth_maxwell_local_density_weak_strong_gate
    (density : SmoothPositiveReferenceDensity4)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4)
    (boundary : RegularIntrinsicMaxwellLocalBoxDirichlet period hPeriod
      variation patch box) :
    (∫ coordinate in Icc box.lower box.upper,
      density coordinate *
        regularMaxwellFirstVariationField period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation)
          (patch.coordinateMap coordinate)) =
      ∫ coordinate in Icc box.lower box.upper,
        ∑ component : Fin 2,
          regularFrameMaxwellReferenceDensityStrongPairing period hPeriod
            density metric potential variation component patch coordinate :=
  integral_density_mul_regularMaxwellFirstVariationField_eq_correctedStrong
    period hPeriod density metric potential variation patch box boundary

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwellLocalDensityWeakStrong4D
end JanusFormal
