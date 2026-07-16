import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1LocalizedTransitionBound4D

/-!
# Intrinsic patch coordinates and the variable preferred-chart diagonal

The actual finite generators have smooth coordinates in each fixed tangent
trivialization.  Mathlib also proves continuity of tangent coordinate changes
when both chart centres are fixed.  The current raw holonomic density instead
uses the preferred chart centred at the evaluation point itself.

This gate proves the intrinsic and fixed-centre statements unconditionally,
identifies the raw coefficient with the diagonal transition
`p ↦ tangentCoordChange anchor p p`, and reduces energy domination to
continuity of precisely that diagonal scalar projection.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1IntrinsicPatchCoordinates4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FixedLocalEnergyReduction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1LocalizedTransitionBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

private abbrev fixedTangentTrivialization
    (patch : FiniteTangentGeneratorPatch period hPeriod) :=
  trivializationAt CoverCoordinates
    (TangentSpace coverModelWithCorners) patch.1

/-- The public finite patch is exactly the base set of its fixed tangent
trivialization. -/
theorem finiteTangentGeneratorOpenPatch_eq_fixedTrivialization_baseSet
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    finiteTangentGeneratorOpenPatch period hPeriod patch =
      (fixedTangentTrivialization period hPeriod patch).baseSet := by
  rfl

/-- Equivalently, the finite patch is the source of the preferred base chart
at its fixed anchor. -/
theorem finiteTangentGeneratorOpenPatch_eq_chart_source
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    finiteTangentGeneratorOpenPatch period hPeriod patch =
      (chartAt CoverModel patch.1).source := by
  rfl

/-- Coordinates of one actual localized generator in the fixed tangent
trivialization attached to that generator's patch. -/
def finiteFixedTrivializationCoordinate
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod) : CoverCoordinates :=
  (fixedTangentTrivialization period hPeriod index.1
    ⟨point,
      (finiteSmoothTangentFrame period hPeriod).vectorAt point
        (finiteTangentGeneratorIndexEquivFin period hPeriod index)⟩).2

/-- Fixed-trivialization coordinates of each implemented generator are
smooth on its whole open patch. -/
theorem finiteFixedTrivializationCoordinate_contMDiffOn
    (index : FiniteTangentGeneratorIndex period hPeriod) :
    ContMDiffOn coverModelWithCorners 𝓘(Real, CoverCoordinates) ∞
      (fun point : EffectiveQuotient period hPeriod =>
        finiteFixedTrivializationCoordinate period hPeriod point index)
      (finiteTangentGeneratorOpenPatch period hPeriod index.1) := by
  rw [finiteTangentGeneratorOpenPatch_eq_fixedTrivialization_baseSet]
  have hSection :=
    (finiteSmoothTangentFrame period hPeriod).contMDiff_vector
      (finiteTangentGeneratorIndexEquivFin period hPeriod index)
  have hCoordinates :=
    (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
      (fixedTangentTrivialization period hPeriod index.1)).mp
        hSection.contMDiffOn
  simpa [finiteFixedTrivializationCoordinate] using hCoordinates

/-- Hence these intrinsic coordinates are continuous on the compact closed
support actually used by the partition. -/
theorem finiteFixedTrivializationCoordinate_continuousOn
    (index : FiniteTangentGeneratorIndex period hPeriod) :
    ContinuousOn
      (fun point : EffectiveQuotient period hPeriod =>
        finiteFixedTrivializationCoordinate period hPeriod point index)
      (finiteTangentGeneratorClosedPatch period hPeriod index.1) :=
  (finiteFixedTrivializationCoordinate_contMDiffOn
    period hPeriod index).continuousOn.mono
      (finiteTangentGeneratorClosedPatch_subset_openPatch
        period hPeriod index.1)

/-- Scalar components of the intrinsic fixed-trivialization coordinates. -/
def finiteFixedTrivializationCoefficient
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod)
    (coordinate : Fin 4) : Real :=
  holonomicVectorCoefficient
    (finiteFixedTrivializationCoordinate period hPeriod point index) coordinate

theorem finiteFixedTrivializationCoefficient_continuousOn
    (index : FiniteTangentGeneratorIndex period hPeriod)
    (coordinate : Fin 4) :
    ContinuousOn
      (fun point : EffectiveQuotient period hPeriod =>
        finiteFixedTrivializationCoefficient period hPeriod point index
          coordinate)
      (finiteTangentGeneratorClosedPatch period hPeriod index.1) := by
  have hCoordinate := finiteFixedTrivializationCoordinate_continuousOn
    period hPeriod index
  refine Fin.cases ?_ (fun spatial => ?_) coordinate
  · simpa [finiteFixedTrivializationCoefficient,
      holonomicVectorCoefficient, Function.comp_def] using hCoordinate.snd
  · simpa [finiteFixedTrivializationCoefficient,
      holonomicVectorCoefficient, Function.comp_def] using
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => Real) spatial).continuousOn.comp
        hCoordinate.fst fun _ _ => Set.mem_univ _

/-- Apply a tangent coordinate change with a fixed target chart centre to the
intrinsic fixed-patch coordinates. -/
def finiteFixedTargetTransitionCoefficient
    (target : EffectiveQuotient period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod)
    (coordinate : Fin 4) : Real :=
  holonomicVectorCoefficient
    (tangentCoordChange coverModelWithCorners index.1.1 target point
      (finiteFixedTrivializationCoordinate period hPeriod point index))
    coordinate

/-- Mathlib closes every transition problem with two fixed chart centres. -/
theorem finiteFixedTargetTransitionCoefficient_continuousOn
    (target : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod)
    (coordinate : Fin 4) :
    ContinuousOn
      (fun point : EffectiveQuotient period hPeriod =>
        finiteFixedTargetTransitionCoefficient period hPeriod target point
          index coordinate)
      (finiteTangentGeneratorClosedPatch period hPeriod index.1 ∩
        (chartAt CoverModel target).source) := by
  let domain := finiteTangentGeneratorClosedPatch period hPeriod index.1 ∩
    (chartAt CoverModel target).source
  have hTransition : ContinuousOn
      (tangentCoordChange coverModelWithCorners index.1.1 target) domain := by
    apply (continuousOn_tangentCoordChange (I := coverModelWithCorners)
      index.1.1 target).mono
    intro point hPoint
    refine ⟨?_, ?_⟩
    · rw [extChartAt_source,
        ← finiteTangentGeneratorOpenPatch_eq_chart_source period hPeriod]
      exact finiteTangentGeneratorClosedPatch_subset_openPatch
        period hPeriod index.1 hPoint.1
    · rw [extChartAt_source]
      exact hPoint.2
  have hFixed : ContinuousOn
      (fun point : EffectiveQuotient period hPeriod =>
        finiteFixedTrivializationCoordinate period hPeriod point index)
      domain :=
    (finiteFixedTrivializationCoordinate_continuousOn
      period hPeriod index).mono Set.inter_subset_left
  have hApplied := hTransition.clm_apply hFixed
  change ContinuousOn
    (fun point : EffectiveQuotient period hPeriod =>
      holonomicVectorCoefficient
        (tangentCoordChange coverModelWithCorners index.1.1 target point
          (finiteFixedTrivializationCoordinate period hPeriod point index))
        coordinate) domain
  refine Fin.cases ?_ (fun spatial => ?_) coordinate
  · simpa [holonomicVectorCoefficient, Function.comp_def] using hApplied.snd
  · simpa [holonomicVectorCoefficient, Function.comp_def] using
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => Real) spatial).continuousOn.comp
        hApplied.fst fun _ _ => Set.mem_univ _

/-- The remaining diagonal transition uses the evaluation point itself as
the target chart centre. -/
def finiteVariablePreferredTransitionCoefficient
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod)
    (coordinate : Fin 4) : Real :=
  holonomicVectorCoefficient
    (tangentCoordChange coverModelWithCorners index.1.1 point point
      (finiteFixedTrivializationCoordinate period hPeriod point index))
    coordinate

set_option backward.isDefEq.respectTransparency false in
/-- On its patch, changing the fixed-trivialization coordinate back to the
preferred chart at the evaluation point recovers the raw tangent vector. -/
theorem finiteVariablePreferredTransition_eq_vector
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod)
    (hPoint : point ∈
      finiteTangentGeneratorOpenPatch period hPeriod index.1) :
    tangentCoordChange coverModelWithCorners index.1.1 point point
        (finiteFixedTrivializationCoordinate period hPeriod point index) =
      (finiteSmoothTangentFrame period hPeriod).vectorAt point
        (finiteTangentGeneratorIndexEquivFin period hPeriod index) := by
  have hChart : point ∈ (chartAt CoverModel index.1.1).source := by
    rw [← finiteTangentGeneratorOpenPatch_eq_chart_source period hPeriod]
    exact hPoint
  have hChartExt : point ∈
      (extChartAt coverModelWithCorners index.1.1).source := by
    rw [extChartAt_source]
    exact hChart
  have hSelfExt : point ∈
      (extChartAt coverModelWithCorners point).source := by
    rw [extChartAt_source]
    exact mem_chart_source CoverModel point
  let vector := (finiteSmoothTangentFrame period hPeriod).vectorAt point
    (finiteTangentGeneratorIndexEquivFin period hPeriod index)
  have hFixed :
      finiteFixedTrivializationCoordinate period hPeriod point index =
        tangentCoordChange coverModelWithCorners point index.1.1 point vector := by
    unfold finiteFixedTrivializationCoordinate
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
      (R := Real) (fixedTangentTrivialization period hPeriod index.1)
        hChart vector]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hChart]
    rfl
  rw [hFixed]
  calc
    tangentCoordChange coverModelWithCorners index.1.1 point point
        (tangentCoordChange coverModelWithCorners point index.1.1 point vector) =
      tangentCoordChange coverModelWithCorners point point point vector := by
        exact tangentCoordChange_comp (I := coverModelWithCorners)
          (w := point) (x := index.1.1) (y := point) (z := point)
          (v := vector)
          ⟨⟨hSelfExt, hChartExt⟩, hSelfExt⟩
    _ = vector := tangentCoordChange_self
      (I := coverModelWithCorners) hSelfExt

/-- The raw coefficient in the existing action is exactly the diagonal
variable-centre transition coefficient. -/
theorem finiteLocalizedHolonomicCoefficient_eq_variableTransition
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod)
    (coordinate : Fin 4)
    (hPoint : point ∈
      finiteTangentGeneratorClosedPatch period hPeriod index.1) :
    finiteLocalizedHolonomicCoefficient period hPeriod point index coordinate =
      finiteVariablePreferredTransitionCoefficient period hPeriod point index
        coordinate := by
  have hOpen := finiteTangentGeneratorClosedPatch_subset_openPatch
    period hPeriod index.1 hPoint
  unfold finiteLocalizedHolonomicCoefficient
    smoothFrameHolonomicCoefficient
    finiteVariablePreferredTransitionCoefficient
  rw [finiteVariablePreferredTransition_eq_vector
    period hPeriod point index hOpen]

/-- Exact residual regularity after all intrinsic and fixed-centre continuity
has been discharged.  Mathlib's `continuousOn_tangentCoordChange` cannot be
applied directly because its target centre is fixed, whereas this one is
`point`. -/
structure FiniteVariablePreferredTransitionContinuity : Prop where
  continuousOn_transition : ∀
      (index : FiniteTangentGeneratorIndex period hPeriod)
      (coordinate : Fin 4),
    ContinuousOn
      (fun point : EffectiveQuotient period hPeriod =>
        finiteVariablePreferredTransitionCoefficient period hPeriod point
          index coordinate)
      (finiteTangentGeneratorClosedPatch period hPeriod index.1)

/-- The diagonal transition regularity is sufficient for the localized raw
coefficient regularity used by the energy comparison. -/
def FiniteVariablePreferredTransitionContinuity.toLocalizedCoefficientContinuity
    (regularity : FiniteVariablePreferredTransitionContinuity
      period hPeriod) :
    FiniteLocalizedHolonomicCoefficientContinuity period hPeriod where
  continuousOn_coefficient index coordinate :=
    (regularity.continuousOn_transition index coordinate).congr
      (fun point hPoint =>
        finiteLocalizedHolonomicCoefficient_eq_variableTransition
          period hPeriod point index coordinate hPoint)

/-- Thus this exact variable-chart diagonal contract is the remaining
continuity input to the existing fixed-local energy domination route. -/
def FiniteVariablePreferredTransitionContinuity.toEnergyDomination
    (regularity : FiniteVariablePreferredTransitionContinuity
      period hPeriod)
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    StaticScalarFixedLocalEnergyDomination period hPeriod data :=
  FiniteLocalizedHolonomicCoefficientContinuity.toEnergyDomination
    period hPeriod
      (regularity.toLocalizedCoefficientContinuity period hPeriod) data

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1IntrinsicPatchCoordinates4D
end JanusFormal
