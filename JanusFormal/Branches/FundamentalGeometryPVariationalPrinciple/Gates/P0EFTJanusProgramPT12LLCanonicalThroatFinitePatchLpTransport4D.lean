import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchVolumeComparison4D
import RellichKondrachov.MeasureTheory.Function.LpSpace.ChangeMeasureLeSmul
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Finite-patch `L²` transport on the canonical throat

The proved two-sided comparison between canonical throat volume and chart
Lebesgue volume gives bounded transport between ambient Euclidean `L²`,
canonical patch coordinates, and the measured throat patch.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchLpTransport4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D
open P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchVolumeComparison4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat :=
  MappingTorus (throatData period hPeriod)
private abbrev Patch :=
  FiniteThroatGeneratorPatch period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance canonicalThroatChartHilbertMeasurableSpace :
    MeasurableSpace CanonicalThroatChartHilbertCoordinates :=
  borel CanonicalThroatChartHilbertCoordinates

local instance canonicalThroatChartHilbertBorelSpace :
    BorelSpace CanonicalThroatChartHilbertCoordinates where
  measurable_eq := rfl


universe u

variable {Fiber : Type u}
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev PatchCoordinateLp
    (patch : Patch period hPeriod) :=
  Lp Fiber (2 : ENNReal)
    (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
      period hPeriod patch)

private abbrev PatchRestrictedLebesgueLp
    (patch : Patch period hPeriod) :=
  Lp Fiber (2 : ENNReal)
    ((volume : Measure CanonicalThroatChartHilbertCoordinates).restrict
      (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch))

private abbrev PatchSourceLp
    (patch : Patch period hPeriod) :=
  Lp Fiber (2 : ENNReal)
    (finiteThroatGeneratorPatchCanonicalSourceMeasure
      period hPeriod patch)

/-- Generic-fiber restriction from ambient Lebesgue `L²` to canonical
coordinate `L²` on one patch. -/
def finiteThroatGeneratorPatchAmbientToCoordinateLp
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalThroatChartHilbertCoordinates) →L[Real]
      PatchCoordinateLp (Fiber := Fiber) period hPeriod patch := by
  let restrictToPatch :
      Lp Fiber (2 : ENNReal)
          (volume : Measure CanonicalThroatChartHilbertCoordinates) →L[Real]
        PatchRestrictedLebesgueLp
          (Fiber := Fiber) period hPeriod patch :=
    MeasureTheory.Lp.changeMeasureL
      (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
      (ν := (volume :
        Measure CanonicalThroatChartHilbertCoordinates).restrict
          (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal)) (c := 1)
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (volume :
            Measure CanonicalThroatChartHilbertCoordinates).restrict
              (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch) ≤
            volume))
      (by simp)
  let changeToCanonical :
      PatchRestrictedLebesgueLp
          (Fiber := Fiber) period hPeriod patch →L[Real]
        PatchCoordinateLp (Fiber := Fiber) period hPeriod patch :=
    MeasureTheory.Lp.changeMeasureL
      (μ := (volume :
        Measure CanonicalThroatChartHilbertCoordinates).restrict
          (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch))
      (ν := finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch)
      (E := Fiber) (p := (2 : ENNReal))
      comparison.canonicalBound_ne_top
      comparison.canonical_le_lebesgue
      (by simp)
  exact changeToCanonical.comp restrictToPatch

/-- Generic-fiber transport from canonical coordinate `L²` to ambient
Lebesgue `L²`, by bounded measure change and extension by zero. -/
def finiteThroatGeneratorPatchCoordinateToAmbientLp
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    PatchCoordinateLp (Fiber := Fiber) period hPeriod patch →L[Real]
      Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalThroatChartHilbertCoordinates) := by
  let changeToLebesgue :
      PatchCoordinateLp (Fiber := Fiber) period hPeriod patch →L[Real]
        PatchRestrictedLebesgueLp
          (Fiber := Fiber) period hPeriod patch :=
    MeasureTheory.Lp.changeMeasureL
      (μ := finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch)
      (ν := (volume :
        Measure CanonicalThroatChartHilbertCoordinates).restrict
          (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal))
      comparison.lebesgueBound_ne_top
      comparison.lebesgue_le_canonical
      (by simp)
  exact
    (MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
      (E := Fiber) (p := (2 : ENNReal))
      (s := finiteThroatGeneratorPatchHilbertSupport period hPeriod patch)
      (finiteThroatGeneratorPatchHilbertSupport_measurable
        period hPeriod patch)).toContinuousLinearMap.comp
      changeToLebesgue

/-- Generic-fiber exact pullback from canonical coordinates to the measured
quotient patch. -/
def finiteThroatGeneratorPatchCoordinateToSourceLp
    (patch : Patch period hPeriod) :
    PatchCoordinateLp (Fiber := Fiber) period hPeriod patch →ₗᵢ[Real]
      PatchSourceLp (Fiber := Fiber) period hPeriod patch :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ
    (𝕜 := Real) (E := Fiber) (p := (2 : ENNReal))
    (μ := finiteThroatGeneratorPatchCanonicalSourceMeasure
      period hPeriod patch)
    (μb := finiteThroatGeneratorPatchCanonicalCoordinateMeasure
      period hPeriod patch)
    (f := finiteThroatGeneratorPatchHilbertCoordinate period hPeriod patch)
    (finiteThroatGeneratorPatchHilbertCoordinate_measurePreserving
      period hPeriod patch)

/-- Ambient Euclidean `L²` pulled back to the canonical quotient patch. -/
def finiteThroatGeneratorPatchAmbientToSourceLp
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalThroatChartHilbertCoordinates) →L[Real]
      PatchSourceLp (Fiber := Fiber) period hPeriod patch :=
  (finiteThroatGeneratorPatchCoordinateToSourceLp
      (Fiber := Fiber) period hPeriod patch).toContinuousLinearMap.comp
    (finiteThroatGeneratorPatchAmbientToCoordinateLp
      (Fiber := Fiber) period hPeriod patch comparison)

theorem finiteThroatGeneratorPatchAmbientToCoordinateLp_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field :
      Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalThroatChartHilbertCoordinates)) :
    (finiteThroatGeneratorPatchAmbientToCoordinateLp
        (Fiber := Fiber) period hPeriod patch comparison field :
      CanonicalThroatChartHilbertCoordinates → Fiber) =ᵐ[
        finiteThroatGeneratorPatchCanonicalCoordinateMeasure
          period hPeriod patch]
      field := by
  let restricted :=
    MeasureTheory.Lp.changeMeasureL
      (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
      (ν := (volume :
        Measure CanonicalThroatChartHilbertCoordinates).restrict
          (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal)) (c := 1)
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (volume :
            Measure CanonicalThroatChartHilbertCoordinates).restrict
              (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch) ≤
            volume))
      (by simp) field
  have hRestricted :
      (restricted : CanonicalThroatChartHilbertCoordinates → Fiber) =ᵐ[
        (volume :
          Measure CanonicalThroatChartHilbertCoordinates).restrict
            (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch)]
        field :=
    MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq
      (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
      (ν := (volume :
        Measure CanonicalThroatChartHilbertCoordinates).restrict
          (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal))
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (volume :
            Measure CanonicalThroatChartHilbertCoordinates).restrict
              (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch) ≤
            volume))
      (by simp) field
  have hChanged :
      (MeasureTheory.Lp.changeMeasureL
          (μ := (volume :
            Measure CanonicalThroatChartHilbertCoordinates).restrict
              (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch))
          (ν := finiteThroatGeneratorPatchCanonicalCoordinateMeasure
            period hPeriod patch)
          (E := Fiber) (p := (2 : ENNReal))
          comparison.canonicalBound_ne_top
          comparison.canonical_le_lebesgue
          (by simp) restricted :
        CanonicalThroatChartHilbertCoordinates → Fiber) =ᵐ[
          finiteThroatGeneratorPatchCanonicalCoordinateMeasure
            period hPeriod patch]
        restricted :=
    MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq
      comparison.canonicalBound_ne_top
      comparison.canonical_le_lebesgue
      (by simp) restricted
  have hAbsolute :
      finiteThroatGeneratorPatchCanonicalCoordinateMeasure
          period hPeriod patch ≪
        (volume :
          Measure CanonicalThroatChartHilbertCoordinates).restrict
            (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch) :=
    Measure.absolutelyContinuous_of_le_smul
      comparison.canonical_le_lebesgue
  exact
    (show
      (MeasureTheory.Lp.changeMeasureL
          (μ := (volume :
            Measure CanonicalThroatChartHilbertCoordinates).restrict
              (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch))
          (ν := finiteThroatGeneratorPatchCanonicalCoordinateMeasure
            period hPeriod patch)
          (E := Fiber) (p := (2 : ENNReal))
          comparison.canonicalBound_ne_top
          comparison.canonical_le_lebesgue
          (by simp) restricted :
        CanonicalThroatChartHilbertCoordinates → Fiber) =ᵐ[
          finiteThroatGeneratorPatchCanonicalCoordinateMeasure
            period hPeriod patch] field from
      hChanged.trans (hAbsolute.ae_eq hRestricted))

theorem finiteThroatGeneratorPatchCoordinateToAmbientLp_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field : PatchCoordinateLp
      (Fiber := Fiber) period hPeriod patch) :
    (finiteThroatGeneratorPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison field :
      CanonicalThroatChartHilbertCoordinates → Fiber) =ᵐ[volume]
      (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch).indicator
        fun coordinate => field coordinate := by
  let changed :=
    MeasureTheory.Lp.changeMeasureL
      (μ := finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch)
      (ν := (volume :
        Measure CanonicalThroatChartHilbertCoordinates).restrict
          (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal))
      comparison.lebesgueBound_ne_top
      comparison.lebesgue_le_canonical
      (by simp) field
  have hChanged :
      (changed : CanonicalThroatChartHilbertCoordinates → Fiber) =ᵐ[
        (volume :
          Measure CanonicalThroatChartHilbertCoordinates).restrict
            (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch)]
        field :=
    MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq
      comparison.lebesgueBound_ne_top
      comparison.lebesgue_le_canonical
      (by simp) field
  have hChangedOn :
      ∀ᵐ coordinate ∂(volume :
          Measure CanonicalThroatChartHilbertCoordinates),
        coordinate ∈
            finiteThroatGeneratorPatchHilbertSupport period hPeriod patch →
          changed coordinate = field coordinate :=
    (ae_restrict_iff'
      (finiteThroatGeneratorPatchHilbertSupport_measurable
        period hPeriod patch)).1 hChanged
  have hExtended :
      ((MeasureTheory.Lp.extendByZeroₗᵢ
          (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
          (E := Fiber) (p := (2 : ENNReal))
          (s := finiteThroatGeneratorPatchHilbertSupport period hPeriod patch)
          (finiteThroatGeneratorPatchHilbertSupport_measurable
            period hPeriod patch)) changed :
        CanonicalThroatChartHilbertCoordinates → Fiber) =ᵐ[volume]
      (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch).indicator
        fun coordinate => changed coordinate :=
    MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq
      (finiteThroatGeneratorPatchHilbertSupport_measurable
        period hPeriod patch) changed
  change
    ((MeasureTheory.Lp.extendByZeroₗᵢ
        (μ := (volume : Measure CanonicalThroatChartHilbertCoordinates))
        (E := Fiber) (p := (2 : ENNReal))
        (s := finiteThroatGeneratorPatchHilbertSupport period hPeriod patch)
        (finiteThroatGeneratorPatchHilbertSupport_measurable
          period hPeriod patch)) changed :
      CanonicalThroatChartHilbertCoordinates → Fiber) =ᵐ[volume]
      (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch).indicator
        fun coordinate => field coordinate
  filter_upwards [hExtended, hChangedOn] with coordinate hExtended hChanged
  rw [hExtended]
  by_cases hCoordinate :
      coordinate ∈ finiteThroatGeneratorPatchHilbertSupport period hPeriod patch
  · simp [Set.indicator_of_mem hCoordinate, hChanged hCoordinate]
  · simp [Set.indicator_of_notMem hCoordinate]

theorem finiteThroatGeneratorPatchAmbientToSourceLp_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field :
      Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalThroatChartHilbertCoordinates)) :
    (finiteThroatGeneratorPatchAmbientToSourceLp
        (Fiber := Fiber) period hPeriod patch comparison field :
      FiniteThroatGeneratorPatchDomain period hPeriod patch → Fiber) =ᵐ[
        finiteThroatGeneratorPatchCanonicalSourceMeasure period hPeriod patch]
      fun point =>
        field
          (finiteThroatGeneratorPatchHilbertCoordinate
            period hPeriod patch point) := by
  let coordinateField :=
    finiteThroatGeneratorPatchAmbientToCoordinateLp
      (Fiber := Fiber) period hPeriod patch comparison field
  have hPull :
      (finiteThroatGeneratorPatchCoordinateToSourceLp
          (Fiber := Fiber) period hPeriod patch coordinateField :
        FiniteThroatGeneratorPatchDomain period hPeriod patch → Fiber) =ᵐ[
          finiteThroatGeneratorPatchCanonicalSourceMeasure period hPeriod patch]
        fun point =>
          coordinateField
            (finiteThroatGeneratorPatchHilbertCoordinate
              period hPeriod patch point) :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving
      coordinateField
      (finiteThroatGeneratorPatchHilbertCoordinate_measurePreserving
        period hPeriod patch)
  have hCoordinate :=
    finiteThroatGeneratorPatchAmbientToCoordinateLp_coeFn_ae_eq
      (Fiber := Fiber) period hPeriod patch comparison field
  have hCoordinatePull :=
    (finiteThroatGeneratorPatchHilbertCoordinate_measurePreserving
      period hPeriod patch).quasiMeasurePreserving.ae_eq_comp
        hCoordinate
  exact hPull.trans hCoordinatePull

/-- Canonical chart pullback is nonsingular with respect to ambient
Lebesgue volume, by the proved two-sided finite volume comparison. -/
def finiteThroatGeneratorPatchHilbertCoordinateQuasiMeasurePreserving
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    Measure.QuasiMeasurePreserving
      (finiteThroatGeneratorPatchHilbertCoordinate period hPeriod patch)
      (finiteThroatGeneratorPatchCanonicalSourceMeasure period hPeriod patch)
      (volume : Measure CanonicalThroatChartHilbertCoordinates) where
  measurable :=
    (finiteThroatGeneratorPatchHilbertCoordinate_measurePreserving
      period hPeriod patch).measurable
  absolutelyContinuous := by
    rw [(finiteThroatGeneratorPatchHilbertCoordinate_measurePreserving
      period hPeriod patch).map_eq]
    exact
      (Measure.absolutelyContinuous_of_le_smul
        comparison.canonical_le_lebesgue).trans
        Measure.absolutelyContinuous_restrict

theorem finiteThroatGeneratorPatchCoordinateReconstruction
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field :
      Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalThroatChartHilbertCoordinates))
    (hZero :
      ∀ᵐ coordinate ∂(volume :
          Measure CanonicalThroatChartHilbertCoordinates),
        coordinate ∉ finiteThroatGeneratorPatchHilbertSupport
            period hPeriod patch →
          field coordinate = 0) :
    finiteThroatGeneratorPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison
        (finiteThroatGeneratorPatchAmbientToCoordinateLp
          (Fiber := Fiber) period hPeriod patch comparison field) =
      field := by
  apply Lp.ext
  let coordinateField :=
    finiteThroatGeneratorPatchAmbientToCoordinateLp
      (Fiber := Fiber) period hPeriod patch comparison field
  have hOutput :=
    finiteThroatGeneratorPatchCoordinateToAmbientLp_coeFn_ae_eq
      (Fiber := Fiber) period hPeriod patch comparison coordinateField
  have hCoordinate :=
    finiteThroatGeneratorPatchAmbientToCoordinateLp_coeFn_ae_eq
      (Fiber := Fiber) period hPeriod patch comparison field
  have hLebesgueAbsolute :
      (volume :
          Measure CanonicalThroatChartHilbertCoordinates).restrict
            (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch) ≪
        finiteThroatGeneratorPatchCanonicalCoordinateMeasure
          period hPeriod patch :=
    Measure.absolutelyContinuous_of_le_smul
      comparison.lebesgue_le_canonical
  have hCoordinateRestricted :
      (coordinateField :
          CanonicalThroatChartHilbertCoordinates → Fiber) =ᵐ[
        (volume :
          Measure CanonicalThroatChartHilbertCoordinates).restrict
            (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch)]
        field :=
    hLebesgueAbsolute.ae_eq hCoordinate
  have hCoordinateOn :
      ∀ᵐ coordinate ∂(volume :
          Measure CanonicalThroatChartHilbertCoordinates),
        coordinate ∈ finiteThroatGeneratorPatchHilbertSupport
            period hPeriod patch →
          coordinateField coordinate = field coordinate :=
    (ae_restrict_iff'
      (finiteThroatGeneratorPatchHilbertSupport_measurable
        period hPeriod patch)).1 hCoordinateRestricted
  filter_upwards [hOutput, hCoordinateOn, hZero]
    with coordinate hOutput hCoordinate hZero
  rw [hOutput]
  by_cases hSupport :
      coordinate ∈ finiteThroatGeneratorPatchHilbertSupport period hPeriod patch
  · simp [Set.indicator_of_mem hSupport, hCoordinate hSupport]
  · simp [Set.indicator_of_notMem hSupport, hZero hSupport]

/-- An ambient field supported on one patch is norm-controlled by its exact
canonical-source pullback. -/
theorem finiteThroatGeneratorPatchAmbient_norm_le_source_norm_of_support
    (patch : Patch period hPeriod)
    (comparison :
      FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field :
      Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalThroatChartHilbertCoordinates))
    (hZero :
      ∀ᵐ coordinate ∂(volume :
          Measure CanonicalThroatChartHilbertCoordinates),
        coordinate ∉ finiteThroatGeneratorPatchHilbertSupport
            period hPeriod patch →
          field coordinate = 0) :
    ‖field‖ ≤
      ‖finiteThroatGeneratorPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison‖ *
        ‖finiteThroatGeneratorPatchAmbientToSourceLp
          (Fiber := Fiber) period hPeriod patch comparison field‖ := by
  let coordinateField :=
    finiteThroatGeneratorPatchAmbientToCoordinateLp
      (Fiber := Fiber) period hPeriod patch comparison field
  have hReconstruction :=
    finiteThroatGeneratorPatchCoordinateReconstruction
      (Fiber := Fiber) period hPeriod patch comparison field hZero
  have hIsometry :
      ‖finiteThroatGeneratorPatchCoordinateToSourceLp
          (Fiber := Fiber) period hPeriod patch coordinateField‖ =
        ‖coordinateField‖ :=
    (finiteThroatGeneratorPatchCoordinateToSourceLp
      (Fiber := Fiber) period hPeriod patch).norm_map coordinateField
  calc
    ‖field‖ =
      ‖finiteThroatGeneratorPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison coordinateField‖ :=
      congrArg norm hReconstruction.symm
    _ ≤
      ‖finiteThroatGeneratorPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison‖ *
        ‖coordinateField‖ :=
      (finiteThroatGeneratorPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison).le_opNorm
          coordinateField
    _ =
      ‖finiteThroatGeneratorPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison‖ *
        ‖finiteThroatGeneratorPatchAmbientToSourceLp
          (Fiber := Fiber) period hPeriod patch comparison field‖ := by
      rw [← hIsometry]
      rfl

/-- The patch subtype inclusion preserves the pulled-back canonical volume. -/
def finiteThroatGeneratorPatchSubtypeMeasurePreserving
    (patch : Patch period hPeriod) :
    MeasurePreserving
      (Subtype.val :
        FiniteThroatGeneratorPatchDomain period hPeriod patch →
          EffectiveThroat period hPeriod)
      (finiteThroatGeneratorPatchCanonicalSourceMeasure period hPeriod patch)
      ((intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
        (finiteThroatGeneratorClosedPatch period hPeriod patch)) where
  measurable := measurable_subtype_coe
  map_eq :=
    finiteThroatGeneratorPatchCanonicalSourceMeasure_map_subtype
      period hPeriod patch

/-- Restriction of an ambient throat `L²` field to one measured patch. -/
def finiteThroatGeneratorPatchRestrictQuotientLp
    (patch : Patch period hPeriod) :
    Lp Fiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) →L[Real]
      PatchSourceLp (Fiber := Fiber) period hPeriod patch := by
  let restrictToPatch :
      Lp Fiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) →L[Real]
        Lp Fiber (2 : ENNReal)
          ((intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
            (finiteThroatGeneratorClosedPatch
              period hPeriod patch)) :=
    MeasureTheory.Lp.changeMeasureL
      (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (ν := (intrinsicCanonicalThroatVolumeMeasure
        period hPeriod).restrict
          (finiteThroatGeneratorClosedPatch period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal)) (c := 1)
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (intrinsicCanonicalThroatVolumeMeasure
            period hPeriod).restrict
              (finiteThroatGeneratorClosedPatch period hPeriod patch) ≤
            intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      (by simp)
  exact
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ
      (𝕜 := Real) (E := Fiber) (p := (2 : ENNReal))
      (f := Subtype.val)
      (finiteThroatGeneratorPatchSubtypeMeasurePreserving
        period hPeriod patch)).toContinuousLinearMap.comp
      restrictToPatch

theorem finiteThroatGeneratorPatchRestrictQuotientLp_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (field :
      Lp Fiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
    (finiteThroatGeneratorPatchRestrictQuotientLp
        (Fiber := Fiber) period hPeriod patch field :
      FiniteThroatGeneratorPatchDomain period hPeriod patch → Fiber) =ᵐ[
        finiteThroatGeneratorPatchCanonicalSourceMeasure period hPeriod patch]
      fun point => field point.1 := by
  let restricted :=
    MeasureTheory.Lp.changeMeasureL
      (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (ν := (intrinsicCanonicalThroatVolumeMeasure
        period hPeriod).restrict
          (finiteThroatGeneratorClosedPatch period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal)) (c := 1)
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (intrinsicCanonicalThroatVolumeMeasure
            period hPeriod).restrict
              (finiteThroatGeneratorClosedPatch period hPeriod patch) ≤
            intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      (by simp) field
  have hRestricted :
      (restricted :
        EffectiveThroat period hPeriod → Fiber) =ᵐ[
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
            (finiteThroatGeneratorClosedPatch period hPeriod patch)]
        field :=
    MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (intrinsicCanonicalThroatVolumeMeasure
            period hPeriod).restrict
              (finiteThroatGeneratorClosedPatch period hPeriod patch) ≤
            intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      (by simp) field
  have hPull :
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ
          (𝕜 := Real) (E := Fiber) (p := (2 : ENNReal))
          (f := Subtype.val)
          (finiteThroatGeneratorPatchSubtypeMeasurePreserving
            period hPeriod patch) restricted :
        FiniteThroatGeneratorPatchDomain period hPeriod patch → Fiber) =ᵐ[
          finiteThroatGeneratorPatchCanonicalSourceMeasure period hPeriod patch]
        fun point => restricted point.1 :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving
      restricted
      (finiteThroatGeneratorPatchSubtypeMeasurePreserving
        period hPeriod patch)
  have hRestrictedPull :=
    (finiteThroatGeneratorPatchSubtypeMeasurePreserving
      period hPeriod patch).quasiMeasurePreserving.ae_eq_comp
        hRestricted
  exact hPull.trans hRestrictedPull

/-- Exact pullback from quotient volume restricted to a patch into the
canonical patch subtype. -/
def finiteThroatGeneratorPatchRestrictedQuotientToSourceL2
    (patch : Patch period hPeriod) :
    Lp Real (2 : ENNReal)
        ((intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
          (finiteThroatGeneratorClosedPatch period hPeriod patch)) →ₗᵢ[Real]
      PatchSourceLp (Fiber := Real) period hPeriod patch :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ
    (𝕜 := Real) (E := Real) (p := (2 : ENNReal))
    (f := Subtype.val)
    (finiteThroatGeneratorPatchSubtypeMeasurePreserving
      period hPeriod patch)

/-- Extension from a measured quotient patch to global throat `L²`.
The adjoint reverses the exact subtype pullback; extension by zero then
restores the ambient throat domain. -/
def finiteThroatGeneratorPatchSourceToQuotientL2
    (patch : Patch period hPeriod) :
    PatchSourceLp (Fiber := Real) period hPeriod patch →L[Real]
      Lp Real (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (E := Real) (p := (2 : ENNReal))
      (s := finiteThroatGeneratorClosedPatch period hPeriod patch)
      (finiteThroatGeneratorClosedPatch_isClosed
        period hPeriod patch).measurableSet).toContinuousLinearMap.comp
    (finiteThroatGeneratorPatchRestrictedQuotientToSourceL2
      period hPeriod patch).toContinuousLinearMap.adjoint

theorem finiteThroatGeneratorPatchSourceToQuotientL2_pullback
    (patch : Patch period hPeriod)
    (field :
      Lp Real (2 : ENNReal)
        ((intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
          (finiteThroatGeneratorClosedPatch period hPeriod patch))) :
    finiteThroatGeneratorPatchSourceToQuotientL2 period hPeriod patch
        (finiteThroatGeneratorPatchRestrictedQuotientToSourceL2
          period hPeriod patch field) =
      (MeasureTheory.Lp.extendByZeroₗᵢ
        (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (E := Real) (p := (2 : ENNReal))
        (s := finiteThroatGeneratorClosedPatch period hPeriod patch)
        (finiteThroatGeneratorClosedPatch_isClosed
          period hPeriod patch).measurableSet) field := by
  change
    (MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (E := Real) (p := (2 : ENNReal))
      (s := finiteThroatGeneratorClosedPatch period hPeriod patch)
      (finiteThroatGeneratorClosedPatch_isClosed
        period hPeriod patch).measurableSet)
      ((finiteThroatGeneratorPatchRestrictedQuotientToSourceL2
          period hPeriod patch).toContinuousLinearMap.adjoint
        ((finiteThroatGeneratorPatchRestrictedQuotientToSourceL2
          period hPeriod patch) field)) =
    _
  have hAdjoint :=
    congrArg
      (fun operator =>
        operator field)
      (finiteThroatGeneratorPatchRestrictedQuotientToSourceL2
        period hPeriod patch).adjoint_comp_self
  congr 1
end
end P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchLpTransport4D
end JanusFormal
