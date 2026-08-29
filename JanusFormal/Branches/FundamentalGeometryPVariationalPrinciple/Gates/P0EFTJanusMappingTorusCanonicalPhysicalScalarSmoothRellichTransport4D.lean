import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEuclideanRellichCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchRellichReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchVolumeComparison4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalScalarGradientDifferentialBridge4D
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Smooth finite-chart transport for physical Rellich compactness

The partition weight on one tangent-generator patch is multiplied by a
smooth physical scalar and written in the fixed Hilbert chart.  Extension by
zero is `C¹_c`, because the weight has compact support strictly inside the
chart source.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothRellichTransport4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEuclideanRellichCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchRellichReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchVolumeComparison4D
open P0EFTJanusMappingTorusLocalScalarGradientDifferentialBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)
private abbrev Patch :=
  FiniteTangentGeneratorPatch period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) :=
  borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalChartHilbertMeasurableSpace :
    MeasurableSpace CanonicalChartHilbertCoordinates :=
  borel CanonicalChartHilbertCoordinates

local instance canonicalChartHilbertBorelSpace :
    BorelSpace CanonicalChartHilbertCoordinates where
  measurable_eq := rfl

universe u

variable {Fiber : Type u}
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev PatchCoordinateLp
    (patch : Patch period hPeriod) :=
  Lp Fiber (2 : ENNReal)
    (finiteTangentPatchCanonicalCoordinateMeasure
      period hPeriod patch)

private abbrev PatchRestrictedLebesgueLp
    (patch : Patch period hPeriod) :=
  Lp Fiber (2 : ENNReal)
    ((volume : Measure CanonicalChartHilbertCoordinates).restrict
      (finiteTangentPatchHilbertSupport period hPeriod patch))

private abbrev PatchSourceLp
    (patch : Patch period hPeriod) :=
  Lp Fiber (2 : ENNReal)
    (finiteTangentPatchCanonicalSourceMeasure
      period hPeriod patch)

/-- Generic-fiber restriction from ambient Lebesgue `L²` to canonical
coordinate `L²` on one patch. -/
def finiteTangentPatchAmbientToCoordinateLp
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalChartHilbertCoordinates) →L[Real]
      PatchCoordinateLp (Fiber := Fiber) period hPeriod patch := by
  let restrictToPatch :
      Lp Fiber (2 : ENNReal)
          (volume : Measure CanonicalChartHilbertCoordinates) →L[Real]
        PatchRestrictedLebesgueLp
          (Fiber := Fiber) period hPeriod patch :=
    MeasureTheory.Lp.changeMeasureL
      (μ := (volume : Measure CanonicalChartHilbertCoordinates))
      (ν := (volume :
        Measure CanonicalChartHilbertCoordinates).restrict
          (finiteTangentPatchHilbertSupport period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal)) (c := 1)
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (volume :
            Measure CanonicalChartHilbertCoordinates).restrict
              (finiteTangentPatchHilbertSupport period hPeriod patch) ≤
            volume))
      (by simp)
  let changeToCanonical :
      PatchRestrictedLebesgueLp
          (Fiber := Fiber) period hPeriod patch →L[Real]
        PatchCoordinateLp (Fiber := Fiber) period hPeriod patch :=
    MeasureTheory.Lp.changeMeasureL
      (μ := (volume :
        Measure CanonicalChartHilbertCoordinates).restrict
          (finiteTangentPatchHilbertSupport period hPeriod patch))
      (ν := finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch)
      (E := Fiber) (p := (2 : ENNReal))
      comparison.canonicalBound_ne_top
      comparison.canonical_le_lebesgue
      (by simp)
  exact changeToCanonical.comp restrictToPatch

/-- Generic-fiber transport from canonical coordinate `L²` to ambient
Lebesgue `L²`, by bounded measure change and extension by zero. -/
def finiteTangentPatchCoordinateToAmbientLp
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    PatchCoordinateLp (Fiber := Fiber) period hPeriod patch →L[Real]
      Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalChartHilbertCoordinates) := by
  let changeToLebesgue :
      PatchCoordinateLp (Fiber := Fiber) period hPeriod patch →L[Real]
        PatchRestrictedLebesgueLp
          (Fiber := Fiber) period hPeriod patch :=
    MeasureTheory.Lp.changeMeasureL
      (μ := finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch)
      (ν := (volume :
        Measure CanonicalChartHilbertCoordinates).restrict
          (finiteTangentPatchHilbertSupport period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal))
      comparison.lebesgueBound_ne_top
      comparison.lebesgue_le_canonical
      (by simp)
  exact
    (MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := (volume : Measure CanonicalChartHilbertCoordinates))
      (E := Fiber) (p := (2 : ENNReal))
      (s := finiteTangentPatchHilbertSupport period hPeriod patch)
      (finiteTangentPatchHilbertSupport_measurable
        period hPeriod patch)).toContinuousLinearMap.comp
      changeToLebesgue

/-- Generic-fiber exact pullback from canonical coordinates to the measured
quotient patch. -/
def finiteTangentPatchCoordinateToSourceLp
    (patch : Patch period hPeriod) :
    PatchCoordinateLp (Fiber := Fiber) period hPeriod patch →ₗᵢ[Real]
      PatchSourceLp (Fiber := Fiber) period hPeriod patch :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ
    (𝕜 := Real) (E := Fiber) (p := (2 : ENNReal))
    (μ := finiteTangentPatchCanonicalSourceMeasure
      period hPeriod patch)
    (μb := finiteTangentPatchCanonicalCoordinateMeasure
      period hPeriod patch)
    (f := finiteTangentPatchHilbertCoordinate period hPeriod patch)
    (finiteTangentPatchHilbertCoordinate_measurePreserving
      period hPeriod patch)

/-- Ambient Euclidean `L²` pulled back to the canonical quotient patch. -/
def finiteTangentPatchAmbientToSourceLp
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalChartHilbertCoordinates) →L[Real]
      PatchSourceLp (Fiber := Fiber) period hPeriod patch :=
  (finiteTangentPatchCoordinateToSourceLp
      (Fiber := Fiber) period hPeriod patch).toContinuousLinearMap.comp
    (finiteTangentPatchAmbientToCoordinateLp
      (Fiber := Fiber) period hPeriod patch comparison)

theorem finiteTangentPatchAmbientToCoordinateLp_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field :
      Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalChartHilbertCoordinates)) :
    (finiteTangentPatchAmbientToCoordinateLp
        (Fiber := Fiber) period hPeriod patch comparison field :
      CanonicalChartHilbertCoordinates → Fiber) =ᵐ[
        finiteTangentPatchCanonicalCoordinateMeasure
          period hPeriod patch]
      field := by
  let restricted :=
    MeasureTheory.Lp.changeMeasureL
      (μ := (volume : Measure CanonicalChartHilbertCoordinates))
      (ν := (volume :
        Measure CanonicalChartHilbertCoordinates).restrict
          (finiteTangentPatchHilbertSupport period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal)) (c := 1)
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (volume :
            Measure CanonicalChartHilbertCoordinates).restrict
              (finiteTangentPatchHilbertSupport period hPeriod patch) ≤
            volume))
      (by simp) field
  have hRestricted :
      (restricted : CanonicalChartHilbertCoordinates → Fiber) =ᵐ[
        (volume :
          Measure CanonicalChartHilbertCoordinates).restrict
            (finiteTangentPatchHilbertSupport period hPeriod patch)]
        field :=
    MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq
      (μ := (volume : Measure CanonicalChartHilbertCoordinates))
      (ν := (volume :
        Measure CanonicalChartHilbertCoordinates).restrict
          (finiteTangentPatchHilbertSupport period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal))
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (volume :
            Measure CanonicalChartHilbertCoordinates).restrict
              (finiteTangentPatchHilbertSupport period hPeriod patch) ≤
            volume))
      (by simp) field
  have hChanged :
      (MeasureTheory.Lp.changeMeasureL
          (μ := (volume :
            Measure CanonicalChartHilbertCoordinates).restrict
              (finiteTangentPatchHilbertSupport period hPeriod patch))
          (ν := finiteTangentPatchCanonicalCoordinateMeasure
            period hPeriod patch)
          (E := Fiber) (p := (2 : ENNReal))
          comparison.canonicalBound_ne_top
          comparison.canonical_le_lebesgue
          (by simp) restricted :
        CanonicalChartHilbertCoordinates → Fiber) =ᵐ[
          finiteTangentPatchCanonicalCoordinateMeasure
            period hPeriod patch]
        restricted :=
    MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq
      comparison.canonicalBound_ne_top
      comparison.canonical_le_lebesgue
      (by simp) restricted
  have hAbsolute :
      finiteTangentPatchCanonicalCoordinateMeasure
          period hPeriod patch ≪
        (volume :
          Measure CanonicalChartHilbertCoordinates).restrict
            (finiteTangentPatchHilbertSupport period hPeriod patch) :=
    Measure.absolutelyContinuous_of_le_smul
      comparison.canonical_le_lebesgue
  exact
    (show
      (MeasureTheory.Lp.changeMeasureL
          (μ := (volume :
            Measure CanonicalChartHilbertCoordinates).restrict
              (finiteTangentPatchHilbertSupport period hPeriod patch))
          (ν := finiteTangentPatchCanonicalCoordinateMeasure
            period hPeriod patch)
          (E := Fiber) (p := (2 : ENNReal))
          comparison.canonicalBound_ne_top
          comparison.canonical_le_lebesgue
          (by simp) restricted :
        CanonicalChartHilbertCoordinates → Fiber) =ᵐ[
          finiteTangentPatchCanonicalCoordinateMeasure
            period hPeriod patch] field from
      hChanged.trans (hAbsolute.ae_eq hRestricted))

theorem finiteTangentPatchCoordinateToAmbientLp_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field : PatchCoordinateLp
      (Fiber := Fiber) period hPeriod patch) :
    (finiteTangentPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison field :
      CanonicalChartHilbertCoordinates → Fiber) =ᵐ[volume]
      (finiteTangentPatchHilbertSupport period hPeriod patch).indicator
        fun coordinate => field coordinate := by
  let changed :=
    MeasureTheory.Lp.changeMeasureL
      (μ := finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch)
      (ν := (volume :
        Measure CanonicalChartHilbertCoordinates).restrict
          (finiteTangentPatchHilbertSupport period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal))
      comparison.lebesgueBound_ne_top
      comparison.lebesgue_le_canonical
      (by simp) field
  have hChanged :
      (changed : CanonicalChartHilbertCoordinates → Fiber) =ᵐ[
        (volume :
          Measure CanonicalChartHilbertCoordinates).restrict
            (finiteTangentPatchHilbertSupport period hPeriod patch)]
        field :=
    MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq
      comparison.lebesgueBound_ne_top
      comparison.lebesgue_le_canonical
      (by simp) field
  have hChangedOn :
      ∀ᵐ coordinate ∂(volume :
          Measure CanonicalChartHilbertCoordinates),
        coordinate ∈
            finiteTangentPatchHilbertSupport period hPeriod patch →
          changed coordinate = field coordinate :=
    (ae_restrict_iff'
      (finiteTangentPatchHilbertSupport_measurable
        period hPeriod patch)).1 hChanged
  have hExtended :
      ((MeasureTheory.Lp.extendByZeroₗᵢ
          (μ := (volume : Measure CanonicalChartHilbertCoordinates))
          (E := Fiber) (p := (2 : ENNReal))
          (s := finiteTangentPatchHilbertSupport period hPeriod patch)
          (finiteTangentPatchHilbertSupport_measurable
            period hPeriod patch)) changed :
        CanonicalChartHilbertCoordinates → Fiber) =ᵐ[volume]
      (finiteTangentPatchHilbertSupport period hPeriod patch).indicator
        fun coordinate => changed coordinate :=
    MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq
      (finiteTangentPatchHilbertSupport_measurable
        period hPeriod patch) changed
  change
    ((MeasureTheory.Lp.extendByZeroₗᵢ
        (μ := (volume : Measure CanonicalChartHilbertCoordinates))
        (E := Fiber) (p := (2 : ENNReal))
        (s := finiteTangentPatchHilbertSupport period hPeriod patch)
        (finiteTangentPatchHilbertSupport_measurable
          period hPeriod patch)) changed :
      CanonicalChartHilbertCoordinates → Fiber) =ᵐ[volume]
      (finiteTangentPatchHilbertSupport period hPeriod patch).indicator
        fun coordinate => field coordinate
  filter_upwards [hExtended, hChangedOn] with coordinate hExtended hChanged
  rw [hExtended]
  by_cases hCoordinate :
      coordinate ∈ finiteTangentPatchHilbertSupport period hPeriod patch
  · simp [Set.indicator_of_mem hCoordinate, hChanged hCoordinate]
  · simp [Set.indicator_of_notMem hCoordinate]

theorem finiteTangentPatchAmbientToSourceLp_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field :
      Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalChartHilbertCoordinates)) :
    (finiteTangentPatchAmbientToSourceLp
        (Fiber := Fiber) period hPeriod patch comparison field :
      FiniteTangentPatchDomain period hPeriod patch → Fiber) =ᵐ[
        finiteTangentPatchCanonicalSourceMeasure period hPeriod patch]
      fun point =>
        field
          (finiteTangentPatchHilbertCoordinate
            period hPeriod patch point) := by
  let coordinateField :=
    finiteTangentPatchAmbientToCoordinateLp
      (Fiber := Fiber) period hPeriod patch comparison field
  have hPull :
      (finiteTangentPatchCoordinateToSourceLp
          (Fiber := Fiber) period hPeriod patch coordinateField :
        FiniteTangentPatchDomain period hPeriod patch → Fiber) =ᵐ[
          finiteTangentPatchCanonicalSourceMeasure period hPeriod patch]
        fun point =>
          coordinateField
            (finiteTangentPatchHilbertCoordinate
              period hPeriod patch point) :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving
      coordinateField
      (finiteTangentPatchHilbertCoordinate_measurePreserving
        period hPeriod patch)
  have hCoordinate :=
    finiteTangentPatchAmbientToCoordinateLp_coeFn_ae_eq
      (Fiber := Fiber) period hPeriod patch comparison field
  have hCoordinatePull :=
    (finiteTangentPatchHilbertCoordinate_measurePreserving
      period hPeriod patch).quasiMeasurePreserving.ae_eq_comp
        hCoordinate
  exact hPull.trans hCoordinatePull

/-- Canonical chart pullback is nonsingular with respect to ambient
Lebesgue volume, by the proved two-sided finite volume comparison. -/
def finiteTangentPatchHilbertCoordinateQuasiMeasurePreserving
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    Measure.QuasiMeasurePreserving
      (finiteTangentPatchHilbertCoordinate period hPeriod patch)
      (finiteTangentPatchCanonicalSourceMeasure period hPeriod patch)
      (volume : Measure CanonicalChartHilbertCoordinates) where
  measurable :=
    (finiteTangentPatchHilbertCoordinate_measurePreserving
      period hPeriod patch).measurable
  absolutelyContinuous := by
    rw [(finiteTangentPatchHilbertCoordinate_measurePreserving
      period hPeriod patch).map_eq]
    exact
      (Measure.absolutelyContinuous_of_le_smul
        comparison.canonical_le_lebesgue).trans
        Measure.absolutelyContinuous_restrict

theorem finiteTangentPatchCoordinateReconstruction
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field :
      Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalChartHilbertCoordinates))
    (hZero :
      ∀ᵐ coordinate ∂(volume :
          Measure CanonicalChartHilbertCoordinates),
        coordinate ∉ finiteTangentPatchHilbertSupport
            period hPeriod patch →
          field coordinate = 0) :
    finiteTangentPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison
        (finiteTangentPatchAmbientToCoordinateLp
          (Fiber := Fiber) period hPeriod patch comparison field) =
      field := by
  apply Lp.ext
  let coordinateField :=
    finiteTangentPatchAmbientToCoordinateLp
      (Fiber := Fiber) period hPeriod patch comparison field
  have hOutput :=
    finiteTangentPatchCoordinateToAmbientLp_coeFn_ae_eq
      (Fiber := Fiber) period hPeriod patch comparison coordinateField
  have hCoordinate :=
    finiteTangentPatchAmbientToCoordinateLp_coeFn_ae_eq
      (Fiber := Fiber) period hPeriod patch comparison field
  have hLebesgueAbsolute :
      (volume :
          Measure CanonicalChartHilbertCoordinates).restrict
            (finiteTangentPatchHilbertSupport period hPeriod patch) ≪
        finiteTangentPatchCanonicalCoordinateMeasure
          period hPeriod patch :=
    Measure.absolutelyContinuous_of_le_smul
      comparison.lebesgue_le_canonical
  have hCoordinateRestricted :
      (coordinateField :
          CanonicalChartHilbertCoordinates → Fiber) =ᵐ[
        (volume :
          Measure CanonicalChartHilbertCoordinates).restrict
            (finiteTangentPatchHilbertSupport period hPeriod patch)]
        field :=
    hLebesgueAbsolute.ae_eq hCoordinate
  have hCoordinateOn :
      ∀ᵐ coordinate ∂(volume :
          Measure CanonicalChartHilbertCoordinates),
        coordinate ∈ finiteTangentPatchHilbertSupport
            period hPeriod patch →
          coordinateField coordinate = field coordinate :=
    (ae_restrict_iff'
      (finiteTangentPatchHilbertSupport_measurable
        period hPeriod patch)).1 hCoordinateRestricted
  filter_upwards [hOutput, hCoordinateOn, hZero]
    with coordinate hOutput hCoordinate hZero
  rw [hOutput]
  by_cases hSupport :
      coordinate ∈ finiteTangentPatchHilbertSupport period hPeriod patch
  · simp [Set.indicator_of_mem hSupport, hCoordinate hSupport]
  · simp [Set.indicator_of_notMem hSupport, hZero hSupport]

/-- An ambient field supported on one patch is norm-controlled by its exact
canonical-source pullback. -/
theorem finiteTangentPatchAmbient_norm_le_source_norm_of_support
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field :
      Lp Fiber (2 : ENNReal)
        (volume : Measure CanonicalChartHilbertCoordinates))
    (hZero :
      ∀ᵐ coordinate ∂(volume :
          Measure CanonicalChartHilbertCoordinates),
        coordinate ∉ finiteTangentPatchHilbertSupport
            period hPeriod patch →
          field coordinate = 0) :
    ‖field‖ ≤
      ‖finiteTangentPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison‖ *
        ‖finiteTangentPatchAmbientToSourceLp
          (Fiber := Fiber) period hPeriod patch comparison field‖ := by
  let coordinateField :=
    finiteTangentPatchAmbientToCoordinateLp
      (Fiber := Fiber) period hPeriod patch comparison field
  have hReconstruction :=
    finiteTangentPatchCoordinateReconstruction
      (Fiber := Fiber) period hPeriod patch comparison field hZero
  have hIsometry :
      ‖finiteTangentPatchCoordinateToSourceLp
          (Fiber := Fiber) period hPeriod patch coordinateField‖ =
        ‖coordinateField‖ :=
    (finiteTangentPatchCoordinateToSourceLp
      (Fiber := Fiber) period hPeriod patch).norm_map coordinateField
  calc
    ‖field‖ =
      ‖finiteTangentPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison coordinateField‖ :=
      congrArg norm hReconstruction.symm
    _ ≤
      ‖finiteTangentPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison‖ *
        ‖coordinateField‖ :=
      (finiteTangentPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison).le_opNorm
          coordinateField
    _ =
      ‖finiteTangentPatchCoordinateToAmbientLp
        (Fiber := Fiber) period hPeriod patch comparison‖ *
        ‖finiteTangentPatchAmbientToSourceLp
          (Fiber := Fiber) period hPeriod patch comparison field‖ := by
      rw [← hIsometry]
      rfl

/-- The patch subtype inclusion preserves the pulled-back canonical volume. -/
def finiteTangentPatchSubtypeMeasurePreserving
    (patch : Patch period hPeriod) :
    MeasurePreserving
      (Subtype.val :
        FiniteTangentPatchDomain period hPeriod patch →
          EffectiveQuotient period hPeriod)
      (finiteTangentPatchCanonicalSourceMeasure period hPeriod patch)
      ((intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
        (finiteTangentGeneratorClosedPatch period hPeriod patch)) where
  measurable := measurable_subtype_coe
  map_eq :=
    finiteTangentPatchCanonicalSourceMeasure_map_subtype
      period hPeriod patch

/-- Restriction of an ambient quotient `L²` field to one measured patch. -/
def finiteTangentPatchRestrictQuotientLp
    (patch : Patch period hPeriod) :
    Lp Fiber (2 : ENNReal)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) →L[Real]
      PatchSourceLp (Fiber := Fiber) period hPeriod patch := by
  let restrictToPatch :
      Lp Fiber (2 : ENNReal)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) →L[Real]
        Lp Fiber (2 : ENNReal)
          ((intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
            (finiteTangentGeneratorClosedPatch
              period hPeriod patch)) :=
    MeasureTheory.Lp.changeMeasureL
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (ν := (intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).restrict
          (finiteTangentGeneratorClosedPatch period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal)) (c := 1)
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod).restrict
              (finiteTangentGeneratorClosedPatch period hPeriod patch) ≤
            intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
      (by simp)
  exact
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ
      (𝕜 := Real) (E := Fiber) (p := (2 : ENNReal))
      (f := Subtype.val)
      (finiteTangentPatchSubtypeMeasurePreserving
        period hPeriod patch)).toContinuousLinearMap.comp
      restrictToPatch

theorem finiteTangentPatchRestrictQuotientLp_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (field :
      Lp Fiber (2 : ENNReal)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) :
    (finiteTangentPatchRestrictQuotientLp
        (Fiber := Fiber) period hPeriod patch field :
      FiniteTangentPatchDomain period hPeriod patch → Fiber) =ᵐ[
        finiteTangentPatchCanonicalSourceMeasure period hPeriod patch]
      fun point => field point.1 := by
  let restricted :=
    MeasureTheory.Lp.changeMeasureL
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (ν := (intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).restrict
          (finiteTangentGeneratorClosedPatch period hPeriod patch))
      (E := Fiber) (p := (2 : ENNReal)) (c := 1)
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod).restrict
              (finiteTangentGeneratorClosedPatch period hPeriod patch) ≤
            intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
      (by simp) field
  have hRestricted :
      (restricted :
        EffectiveQuotient period hPeriod → Fiber) =ᵐ[
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
            (finiteTangentGeneratorClosedPatch period hPeriod patch)]
        field :=
    MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod).restrict
              (finiteTangentGeneratorClosedPatch period hPeriod patch) ≤
            intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
      (by simp) field
  have hPull :
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ
          (𝕜 := Real) (E := Fiber) (p := (2 : ENNReal))
          (f := Subtype.val)
          (finiteTangentPatchSubtypeMeasurePreserving
            period hPeriod patch) restricted :
        FiniteTangentPatchDomain period hPeriod patch → Fiber) =ᵐ[
          finiteTangentPatchCanonicalSourceMeasure period hPeriod patch]
        fun point => restricted point.1 :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving
      restricted
      (finiteTangentPatchSubtypeMeasurePreserving
        period hPeriod patch)
  have hRestrictedPull :=
    (finiteTangentPatchSubtypeMeasurePreserving
      period hPeriod patch).quasiMeasurePreserving.ae_eq_comp
        hRestricted
  exact hPull.trans hRestrictedPull

/-- Exact pullback from quotient volume restricted to a patch into the
canonical patch subtype. -/
def finiteTangentPatchRestrictedQuotientToSourceL2
    (patch : Patch period hPeriod) :
    Lp Real (2 : ENNReal)
        ((intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
          (finiteTangentGeneratorClosedPatch period hPeriod patch)) →ₗᵢ[Real]
      PatchSourceLp (Fiber := Real) period hPeriod patch :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ
    (𝕜 := Real) (E := Real) (p := (2 : ENNReal))
    (f := Subtype.val)
    (finiteTangentPatchSubtypeMeasurePreserving
      period hPeriod patch)

/-- Extension from a measured quotient patch to global physical `L²`.
The adjoint reverses the exact subtype pullback; extension by zero then
restores the ambient quotient domain. -/
def finiteTangentPatchSourceToQuotientL2
    (patch : Patch period hPeriod) :
    PatchSourceLp (Fiber := Real) period hPeriod patch →L[Real]
      Lp Real (2 : ENNReal)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (E := Real) (p := (2 : ENNReal))
      (s := finiteTangentGeneratorClosedPatch period hPeriod patch)
      (finiteTangentGeneratorClosedPatch_isClosed
        period hPeriod patch).measurableSet).toContinuousLinearMap.comp
    (finiteTangentPatchRestrictedQuotientToSourceL2
      period hPeriod patch).toContinuousLinearMap.adjoint

theorem finiteTangentPatchSourceToQuotientL2_pullback
    (patch : Patch period hPeriod)
    (field :
      Lp Real (2 : ENNReal)
        ((intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
          (finiteTangentGeneratorClosedPatch period hPeriod patch))) :
    finiteTangentPatchSourceToQuotientL2 period hPeriod patch
        (finiteTangentPatchRestrictedQuotientToSourceL2
          period hPeriod patch field) =
      (MeasureTheory.Lp.extendByZeroₗᵢ
        (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        (E := Real) (p := (2 : ENNReal))
        (s := finiteTangentGeneratorClosedPatch period hPeriod patch)
        (finiteTangentGeneratorClosedPatch_isClosed
          period hPeriod patch).measurableSet) field := by
  change
    (MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (E := Real) (p := (2 : ENNReal))
      (s := finiteTangentGeneratorClosedPatch period hPeriod patch)
      (finiteTangentGeneratorClosedPatch_isClosed
        period hPeriod patch).measurableSet)
      ((finiteTangentPatchRestrictedQuotientToSourceL2
          period hPeriod patch).toContinuousLinearMap.adjoint
        ((finiteTangentPatchRestrictedQuotientToSourceL2
          period hPeriod patch) field)) =
    _
  have hAdjoint :=
    congrArg
      (fun operator =>
        operator field)
      (finiteTangentPatchRestrictedQuotientToSourceL2
        period hPeriod patch).adjoint_comp_self
  congr 1

/-- Fixed Hilbert basis corresponding to the model basis used by the
partition-weighted tangent generators. -/
def finiteTangentGeneratorHilbertBasis :
    Module.Basis FiniteTangentGeneratorBasisIndex Real
      CanonicalChartHilbertCoordinates :=
  finiteGeneratorModelBasisBasis.map
    canonicalChartHilbertEquivCoverCoordinates.symm.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The selected derivative coordinates of the global first jet, assembled
as the coordinate differential on one fixed patch. -/
def finiteTangentPatchJetCoordinateDifferential
    (patch : Patch period hPeriod) :
    (Fin (finiteSmoothTangentFrame period hPeriod).count → Real) →ₗ[Real]
      (CanonicalChartHilbertCoordinates →L[Real] Real) where
  toFun derivatives :=
    ((finiteTangentGeneratorHilbertBasis.constr Real fun basisIndex =>
      derivatives
        (finiteTangentGeneratorIndexEquivFin period hPeriod
          (patch, basisIndex))).toContinuousLinearMap)
  map_add' first second := by
    apply ContinuousLinearMap.coe_injective
    apply finiteTangentGeneratorHilbertBasis.ext
    intro basisIndex
    change
      (finiteTangentGeneratorHilbertBasis.constr Real fun index =>
        (first + second)
          (finiteTangentGeneratorIndexEquivFin period hPeriod
            (patch, index)))
          (finiteTangentGeneratorHilbertBasis basisIndex) =
        (finiteTangentGeneratorHilbertBasis.constr Real fun index =>
          first (finiteTangentGeneratorIndexEquivFin period hPeriod
            (patch, index)))
            (finiteTangentGeneratorHilbertBasis basisIndex) +
          (finiteTangentGeneratorHilbertBasis.constr Real fun index =>
            second (finiteTangentGeneratorIndexEquivFin period hPeriod
              (patch, index)))
              (finiteTangentGeneratorHilbertBasis basisIndex)
    rw [finiteTangentGeneratorHilbertBasis.constr_basis,
      finiteTangentGeneratorHilbertBasis.constr_basis,
      finiteTangentGeneratorHilbertBasis.constr_basis]
    rfl
  map_smul' scalar derivatives := by
    apply ContinuousLinearMap.coe_injective
    apply finiteTangentGeneratorHilbertBasis.ext
    intro basisIndex
    change
      (finiteTangentGeneratorHilbertBasis.constr Real fun index =>
        (scalar • derivatives)
          (finiteTangentGeneratorIndexEquivFin period hPeriod
            (patch, index)))
          (finiteTangentGeneratorHilbertBasis basisIndex) =
        scalar *
          (finiteTangentGeneratorHilbertBasis.constr Real fun index =>
            derivatives
              (finiteTangentGeneratorIndexEquivFin period hPeriod
                (patch, index)))
            (finiteTangentGeneratorHilbertBasis basisIndex)
    rw [finiteTangentGeneratorHilbertBasis.constr_basis,
      finiteTangentGeneratorHilbertBasis.constr_basis]
    rfl

theorem finiteTangentPatchJetCoordinateDifferential_basis
    (patch : Patch period hPeriod)
    (derivatives :
      Fin (finiteSmoothTangentFrame period hPeriod).count → Real)
    (basisIndex : FiniteTangentGeneratorBasisIndex) :
    finiteTangentPatchJetCoordinateDifferential period hPeriod patch
        derivatives
        (finiteTangentGeneratorHilbertBasis basisIndex) =
      derivatives
        (finiteTangentGeneratorIndexEquivFin period hPeriod
          (patch, basisIndex)) := by
  change
    (finiteTangentGeneratorHilbertBasis.constr Real fun index =>
      derivatives
        (finiteTangentGeneratorIndexEquivFin period hPeriod
          (patch, index)))
        (finiteTangentGeneratorHilbertBasis basisIndex) =
      derivatives
        (finiteTangentGeneratorIndexEquivFin period hPeriod
          (patch, basisIndex))
  exact finiteTangentGeneratorHilbertBasis.constr_basis Real _ basisIndex

/-- Open Hilbert-coordinate target of one fixed quotient chart. -/
def finiteTangentPatchHilbertChartTarget
    (patch : Patch period hPeriod) :
    Set CanonicalChartHilbertCoordinates :=
  canonicalChartHilbertEquivCoverCoordinates ⁻¹'
    (extChartAt coverModelWithCorners patch.1).target

theorem finiteTangentPatchHilbertChartTarget_isOpen
    (patch : Patch period hPeriod) :
    IsOpen (finiteTangentPatchHilbertChartTarget
      period hPeriod patch) :=
  (isOpen_extChartAt_target patch.1).preimage
    canonicalChartHilbertEquivCoverCoordinates.continuous

/-- Inverse fixed chart, written on the ambient Hilbert coordinate model. -/
def finiteTangentPatchHilbertInverse
    (patch : Patch period hPeriod)
    (coordinate : CanonicalChartHilbertCoordinates) :
    EffectiveQuotient period hPeriod :=
  (extChartAt coverModelWithCorners patch.1).symm
    (canonicalChartHilbertEquivCoverCoordinates coordinate)

theorem finiteTangentPatchHilbertInverse_coordinate
    (patch : Patch period hPeriod)
    (point : FiniteTangentPatchDomain period hPeriod patch) :
    finiteTangentPatchHilbertInverse period hPeriod patch
        (finiteTangentPatchHilbertCoordinate
          period hPeriod patch point) =
      point.1 := by
  unfold finiteTangentPatchHilbertInverse
  rw [show canonicalChartHilbertEquivCoverCoordinates
      (finiteTangentPatchHilbertCoordinate
        period hPeriod patch point) =
        extChartAt coverModelWithCorners patch.1 point.1 by
    simp [finiteTangentPatchHilbertCoordinate]]
  apply (extChartAt coverModelWithCorners patch.1).left_inv
  rw [extChartAt_source,
    ← finiteTangentGeneratorOpenPatch_eq_chartAt_source
      period hPeriod patch]
  exact finiteTangentGeneratorClosedPatch_subset_openPatch
    period hPeriod patch point.2

theorem finiteTangentPatchHilbertInverse_contMDiffAt
    (patch : Patch period hPeriod)
    {coordinate : CanonicalChartHilbertCoordinates}
    (hCoordinate :
      coordinate ∈ finiteTangentPatchHilbertChartTarget
        period hPeriod patch) :
    ContMDiffAt
      (modelWithCornersSelf Real CanonicalChartHilbertCoordinates)
      coverModelWithCorners ∞
      (finiteTangentPatchHilbertInverse period hPeriod patch)
      coordinate := by
  have hEquiv :
      ContMDiffAt
        (modelWithCornersSelf Real CanonicalChartHilbertCoordinates)
        (modelWithCornersSelf Real CoverCoordinates) ∞
        canonicalChartHilbertEquivCoverCoordinates coordinate :=
    canonicalChartHilbertEquivCoverCoordinates.contDiff.contDiffAt.contMDiffAt
  have hInverse :
      ContMDiffAt
        (modelWithCornersSelf Real CoverCoordinates)
        coverModelWithCorners ∞
        (extChartAt coverModelWithCorners patch.1).symm
        (canonicalChartHilbertEquivCoverCoordinates coordinate) :=
    (contMDiffWithinAt_extChartAt_symm_target
      patch.1 hCoordinate).contMDiffAt
        ((isOpen_extChartAt_target patch.1).mem_nhds hCoordinate)
  exact hInverse.comp coordinate hEquiv

set_option backward.isDefEq.respectTransparency false in
theorem finiteTangentPatchHilbertInverse_mfderiv_basis
    (patch : Patch period hPeriod)
    (point : FiniteTangentPatchDomain period hPeriod patch)
    (basisIndex : FiniteTangentGeneratorBasisIndex) :
    mfderiv
        (modelWithCornersSelf Real CanonicalChartHilbertCoordinates)
        coverModelWithCorners
        (finiteTangentPatchHilbertInverse period hPeriod patch)
        (finiteTangentPatchHilbertCoordinate
          period hPeriod patch point)
        (finiteTangentGeneratorHilbertBasis basisIndex) =
      finiteTangentGeneratorLocalVector
        period hPeriod patch basisIndex point.1 := by
  let coordinate :=
    finiteTangentPatchHilbertCoordinate period hPeriod patch point
  let coverCoordinate :=
    extChartAt coverModelWithCorners patch.1 point.1
  have hPointOpen :
      point.1 ∈ finiteTangentGeneratorOpenPatch
        period hPeriod patch :=
    finiteTangentGeneratorClosedPatch_subset_openPatch
      period hPeriod patch point.2
  have hTarget :
      coverCoordinate ∈
        (extChartAt coverModelWithCorners patch.1).target := by
    apply (extChartAt coverModelWithCorners patch.1).map_source
    rw [extChartAt_source,
      ← finiteTangentGeneratorOpenPatch_eq_chartAt_source
        period hPeriod patch]
    exact hPointOpen
  have hCoordinate :
      canonicalChartHilbertEquivCoverCoordinates coordinate =
        coverCoordinate := by
    simp [coordinate, coverCoordinate,
      finiteTangentPatchHilbertCoordinate]
  have hInverseCont :
      ContMDiffAt
        (modelWithCornersSelf Real CoverCoordinates)
        coverModelWithCorners ∞
        (extChartAt coverModelWithCorners patch.1).symm
        coverCoordinate :=
    (contMDiffWithinAt_extChartAt_symm_target
      patch.1 hTarget).contMDiffAt
        ((isOpen_extChartAt_target patch.1).mem_nhds hTarget)
  have hInverse :
      MDifferentiableAt
        (modelWithCornersSelf Real CoverCoordinates)
        coverModelWithCorners
        (extChartAt coverModelWithCorners patch.1).symm
        coverCoordinate :=
    hInverseCont.mdifferentiableAt (by simp)
  have hEquivCont :
      ContMDiffAt
        (modelWithCornersSelf Real CanonicalChartHilbertCoordinates)
        (modelWithCornersSelf Real CoverCoordinates) ∞
        canonicalChartHilbertEquivCoverCoordinates coordinate :=
    canonicalChartHilbertEquivCoverCoordinates.contDiff.contDiffAt.contMDiffAt
  have hEquiv :
      MDifferentiableAt
        (modelWithCornersSelf Real CanonicalChartHilbertCoordinates)
        (modelWithCornersSelf Real CoverCoordinates)
        canonicalChartHilbertEquivCoverCoordinates coordinate :=
    hEquivCont.mdifferentiableAt (by simp)
  have hChain :=
    mfderiv_comp_apply coordinate
      (show MDifferentiableAt
          (modelWithCornersSelf Real CoverCoordinates)
          coverModelWithCorners
          (extChartAt coverModelWithCorners patch.1).symm
          (canonicalChartHilbertEquivCoverCoordinates coordinate) by
        simpa [hCoordinate] using hInverse)
      hEquiv
      (finiteTangentGeneratorHilbertBasis basisIndex)
  have hEquivDerivative :
      mfderiv
          (modelWithCornersSelf Real CanonicalChartHilbertCoordinates)
          (modelWithCornersSelf Real CoverCoordinates)
          canonicalChartHilbertEquivCoverCoordinates coordinate
          (finiteTangentGeneratorHilbertBasis basisIndex) =
        finiteGeneratorModelBasisVector basisIndex := by
    rw [mfderiv_eq_fderiv,
      canonicalChartHilbertEquivCoverCoordinates.fderiv]
    change
      canonicalChartHilbertEquivCoverCoordinates
          (canonicalChartHilbertEquivCoverCoordinates.symm
            (finiteGeneratorModelBasisVector basisIndex)) =
        finiteGeneratorModelBasisVector basisIndex
    exact canonicalChartHilbertEquivCoverCoordinates.apply_symm_apply _
  rw [hEquivDerivative] at hChain
  rw [hCoordinate] at hChain
  have hRange : coverCoordinate ∈ Set.range coverModelWithCorners :=
    extChartAt_target_subset_range patch.1 hTarget
  have hWithin :
      mfderiv
          (modelWithCornersSelf Real CoverCoordinates)
          coverModelWithCorners
          (extChartAt coverModelWithCorners patch.1).symm
          coverCoordinate =
        mfderivWithin
          (modelWithCornersSelf Real CoverCoordinates)
          coverModelWithCorners
          (extChartAt coverModelWithCorners patch.1).symm
          (Set.range coverModelWithCorners)
          coverCoordinate := by
    exact
      (mfderivWithin_eq_mfderiv
        (coverModelWithCorners.uniqueMDiffOn coverCoordinate hRange)
        hInverse).symm
  rw [hWithin] at hChain
  rw [finiteTangentGeneratorLocalVector_eq_chartAt_inverseDerivative
    period hPeriod patch basisIndex point.1 hPointOpen]
  change
    mfderiv
        (modelWithCornersSelf Real CanonicalChartHilbertCoordinates)
        coverModelWithCorners
        ((extChartAt coverModelWithCorners patch.1).symm ∘
          canonicalChartHilbertEquivCoverCoordinates)
        coordinate
        (finiteTangentGeneratorHilbertBasis basisIndex) =
      mfderivWithin
        (modelWithCornersSelf Real CoverCoordinates)
        coverModelWithCorners
        (extChartAt coverModelWithCorners patch.1).symm
        (Set.range coverModelWithCorners)
        coverCoordinate
        (finiteGeneratorModelBasisVector basisIndex)
  exact hChain

theorem finiteTangentPatchHilbertSupport_subset_chartTarget
    (patch : Patch period hPeriod) :
    finiteTangentPatchHilbertSupport period hPeriod patch ⊆
      finiteTangentPatchHilbertChartTarget period hPeriod patch := by
  rw [← finiteTangentPatchHilbertCoordinate_range
    period hPeriod patch]
  rintro _ ⟨point, rfl⟩
  change
    canonicalChartHilbertEquivCoverCoordinates
        (canonicalChartHilbertEquivCoverCoordinates.symm
          (extChartAt coverModelWithCorners patch.1 point.1)) ∈
    (extChartAt coverModelWithCorners patch.1).target
  rw [canonicalChartHilbertEquivCoverCoordinates.apply_symm_apply]
  apply (extChartAt coverModelWithCorners patch.1).map_source
  rw [extChartAt_source,
    ← finiteTangentGeneratorOpenPatch_eq_chartAt_source
      period hPeriod patch]
  exact finiteTangentGeneratorClosedPatch_subset_openPatch
    period hPeriod patch point.2

/-- Partition-localized scalar in the common Euclidean chart, extended by
zero off the chart target. -/
def finiteTangentPatchLocalizedCoordinateFunction
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    CanonicalChartHilbertCoordinates → Real :=
  (finiteTangentPatchHilbertChartTarget period hPeriod patch).indicator
    (fun coordinate =>
      finiteTangentGeneratorWeight period hPeriod patch
          (finiteTangentPatchHilbertInverse
            period hPeriod patch coordinate) *
        field (finiteTangentPatchHilbertInverse
          period hPeriod patch coordinate))

theorem finiteTangentPatchLocalizedCoordinateFunction_eventuallyEq
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    {coordinate : CanonicalChartHilbertCoordinates}
    (hCoordinate :
      coordinate ∈ finiteTangentPatchHilbertChartTarget
        period hPeriod patch) :
    finiteTangentPatchLocalizedCoordinateFunction
        period hPeriod patch field =ᶠ[nhds coordinate]
      fun current =>
        finiteTangentGeneratorWeight period hPeriod patch
            (finiteTangentPatchHilbertInverse
              period hPeriod patch current) *
          field (finiteTangentPatchHilbertInverse
            period hPeriod patch current) := by
  filter_upwards
    [(finiteTangentPatchHilbertChartTarget_isOpen
      period hPeriod patch).mem_nhds hCoordinate] with current hCurrent
  simp [finiteTangentPatchLocalizedCoordinateFunction,
    Set.indicator_of_mem hCurrent]

theorem finiteTangentPatchLocalizedCoordinateFunction_support
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    Function.support
        (finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch field) ⊆
      finiteTangentPatchHilbertSupport period hPeriod patch := by
  intro coordinate hCoordinate
  have hTarget :
      coordinate ∈ finiteTangentPatchHilbertChartTarget
        period hPeriod patch := by
    by_contra hNotTarget
    exact hCoordinate (by
      simp [finiteTangentPatchLocalizedCoordinateFunction,
        Set.indicator_of_notMem hNotTarget])
  have hProduct :
      finiteTangentGeneratorWeight period hPeriod patch
          (finiteTangentPatchHilbertInverse
            period hPeriod patch coordinate) *
        field (finiteTangentPatchHilbertInverse
          period hPeriod patch coordinate) ≠ 0 := by
    have hExpanded :
        coordinate ∈ finiteTangentPatchHilbertChartTarget
              period hPeriod patch ∧
          finiteTangentGeneratorWeight period hPeriod patch
              (finiteTangentPatchHilbertInverse
                period hPeriod patch coordinate) ≠ 0 ∧
          field (finiteTangentPatchHilbertInverse
            period hPeriod patch coordinate) ≠ 0 := by
      simpa [finiteTangentPatchLocalizedCoordinateFunction] using hCoordinate
    exact mul_ne_zero hExpanded.2.1 hExpanded.2.2
  have hWeight :
      finiteTangentGeneratorWeight period hPeriod patch
          (finiteTangentPatchHilbertInverse
            period hPeriod patch coordinate) ≠ 0 :=
    fun hZero => hProduct (by simp [hZero])
  have hPatch :
      finiteTangentPatchHilbertInverse
          period hPeriod patch coordinate ∈
        finiteTangentGeneratorClosedPatch
          period hPeriod patch :=
    subset_closure hWeight
  rw [← finiteTangentPatchHilbertCoordinate_range
    period hPeriod patch]
  refine ⟨⟨finiteTangentPatchHilbertInverse
    period hPeriod patch coordinate, hPatch⟩, ?_⟩
  change
    canonicalChartHilbertEquivCoverCoordinates.symm
        (extChartAt coverModelWithCorners patch.1
          (finiteTangentPatchHilbertInverse
            period hPeriod patch coordinate)) =
      coordinate
  rw [show extChartAt coverModelWithCorners patch.1
      (finiteTangentPatchHilbertInverse
        period hPeriod patch coordinate) =
        canonicalChartHilbertEquivCoverCoordinates coordinate by
    exact (extChartAt coverModelWithCorners patch.1).right_inv hTarget]
  exact canonicalChartHilbertEquivCoverCoordinates.symm_apply_apply coordinate

theorem finiteTangentPatchLocalizedCoordinateFunction_tsupport
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    tsupport
        (finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch field) ⊆
      finiteTangentPatchHilbertSupport period hPeriod patch :=
  closure_minimal
    (finiteTangentPatchLocalizedCoordinateFunction_support
      period hPeriod patch field)
    (finiteTangentPatchHilbertSupport_isCompact
      period hPeriod patch).isClosed

theorem finiteTangentPatchLocalizedCoordinateFunction_coordinate
    (patch : Patch period hPeriod)
    (point : FiniteTangentPatchDomain period hPeriod patch)
    (field : SmoothQuotientField period hPeriod Real) :
    finiteTangentPatchLocalizedCoordinateFunction
        period hPeriod patch field
        (finiteTangentPatchHilbertCoordinate
          period hPeriod patch point) =
      finiteTangentGeneratorWeight period hPeriod patch point.1 *
        field point.1 := by
  have hCoordinate :
      finiteTangentPatchHilbertCoordinate period hPeriod patch point ∈
        finiteTangentPatchHilbertChartTarget
          period hPeriod patch := by
    apply finiteTangentPatchHilbertSupport_subset_chartTarget
      period hPeriod patch
    rw [← finiteTangentPatchHilbertCoordinate_range
      period hPeriod patch]
    exact ⟨point, rfl⟩
  simp [finiteTangentPatchLocalizedCoordinateFunction,
    Set.indicator_of_mem hCoordinate,
    finiteTangentPatchHilbertInverse_coordinate
      period hPeriod patch point]

theorem finiteTangentPatchLocalizedCoordinateFunction_contDiff
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ContDiff Real ∞
      (finiteTangentPatchLocalizedCoordinateFunction
        period hPeriod patch field) := by
  rw [← contMDiff_iff_contDiff]
  apply contMDiff_of_tsupport
  intro coordinate hCoordinate
  have hSupport :
      coordinate ∈ finiteTangentPatchHilbertSupport
        period hPeriod patch :=
    finiteTangentPatchLocalizedCoordinateFunction_tsupport
      period hPeriod patch field hCoordinate
  have hTarget :
      coordinate ∈ finiteTangentPatchHilbertChartTarget
        period hPeriod patch :=
    finiteTangentPatchHilbertSupport_subset_chartTarget
      period hPeriod patch hSupport
  have hEquiv :
      ContMDiffAt
        𝓘(Real, CanonicalChartHilbertCoordinates)
        (modelWithCornersSelf Real CoverCoordinates) ∞
        canonicalChartHilbertEquivCoverCoordinates coordinate :=
    canonicalChartHilbertEquivCoverCoordinates.contDiff.contDiffAt.contMDiffAt
  have hInverseChart :
      ContMDiffAt
        (modelWithCornersSelf Real CoverCoordinates)
        coverModelWithCorners ∞
        (extChartAt coverModelWithCorners patch.1).symm
        (canonicalChartHilbertEquivCoverCoordinates coordinate) :=
    (contMDiffWithinAt_extChartAt_symm_target
      patch.1 hTarget).contMDiffAt
        ((isOpen_extChartAt_target patch.1).mem_nhds hTarget)
  have hInverse :
      ContMDiffAt
        𝓘(Real, CanonicalChartHilbertCoordinates)
        coverModelWithCorners ∞
        (finiteTangentPatchHilbertInverse
          period hPeriod patch) coordinate :=
    hInverseChart.comp coordinate hEquiv
  have hWeight :=
    (finiteTangentGeneratorWeight_contMDiff
      period hPeriod patch).contMDiffAt.comp coordinate hInverse
  have hField :=
    field.contMDiff_toFun.contMDiffAt.comp coordinate hInverse
  have hLocal :
      ContDiffAt Real ∞
        (fun x =>
          finiteTangentGeneratorWeight period hPeriod patch
              (finiteTangentPatchHilbertInverse
                period hPeriod patch x) *
            field (finiteTangentPatchHilbertInverse
              period hPeriod patch x)) coordinate :=
    hWeight.mul hField |>.contDiffAt
  apply hLocal.contMDiffAt.congr_of_eventuallyEq
  filter_upwards
    [(finiteTangentPatchHilbertChartTarget_isOpen
      period hPeriod patch).mem_nhds hTarget] with x hx
  simp [finiteTangentPatchLocalizedCoordinateFunction,
    Set.indicator_of_mem hx]

/-- Constant smooth scalar used to isolate the partition weight. -/
def smoothConstantOne :
    SmoothQuotientField period hPeriod Real where
  toFun := fun _ => 1
  contMDiff_toFun := contMDiff_const

@[simp]
theorem smoothConstantOne_apply
    (point : EffectiveQuotient period hPeriod) :
    smoothConstantOne period hPeriod point = 1 :=
  rfl

/-- Partition weight in the fixed Hilbert chart, extended smoothly by zero. -/
def finiteTangentPatchLocalizedWeight
    (patch : Patch period hPeriod) :
    CanonicalChartHilbertCoordinates → Real :=
  finiteTangentPatchLocalizedCoordinateFunction
    period hPeriod patch (smoothConstantOne period hPeriod)

theorem finiteTangentPatchLocalizedWeight_contDiff
    (patch : Patch period hPeriod) :
    ContDiff Real ∞
      (finiteTangentPatchLocalizedWeight period hPeriod patch) :=
  finiteTangentPatchLocalizedCoordinateFunction_contDiff
    period hPeriod patch (smoothConstantOne period hPeriod)

set_option backward.isDefEq.respectTransparency false in
theorem finiteTangentPatchFieldPullback_fderiv_basis
    (patch : Patch period hPeriod)
    (point : FiniteTangentPatchDomain period hPeriod patch)
    (field : SmoothQuotientField period hPeriod Real)
    (basisIndex : FiniteTangentGeneratorBasisIndex) :
    fderiv Real
        (fun coordinate =>
          field (finiteTangentPatchHilbertInverse
            period hPeriod patch coordinate))
        (finiteTangentPatchHilbertCoordinate
          period hPeriod patch point)
        (finiteTangentGeneratorHilbertBasis basisIndex) =
      mvfderiv coverModelWithCorners field.toFun point.1
        (finiteTangentGeneratorLocalVector
          period hPeriod patch basisIndex point.1) := by
  let coordinate :=
    finiteTangentPatchHilbertCoordinate period hPeriod patch point
  have hCoordinate :
      coordinate ∈ finiteTangentPatchHilbertChartTarget
        period hPeriod patch := by
    apply finiteTangentPatchHilbertSupport_subset_chartTarget
      period hPeriod patch
    rw [← finiteTangentPatchHilbertCoordinate_range
      period hPeriod patch]
    exact ⟨point, rfl⟩
  have hInverse :=
    (finiteTangentPatchHilbertInverse_contMDiffAt
      period hPeriod patch hCoordinate).mdifferentiableAt (by simp)
  have hField :
      MDifferentiableAt coverModelWithCorners 𝓘(Real)
        field.toFun
        (finiteTangentPatchHilbertInverse
          period hPeriod patch coordinate) :=
    field.contMDiff_toFun.mdifferentiableAt (by simp)
  have hChain :=
    mfderiv_comp_apply coordinate hField hInverse
      (finiteTangentGeneratorHilbertBasis basisIndex)
  dsimp only [coordinate] at hChain
  rw [finiteTangentPatchHilbertInverse_coordinate
    period hPeriod patch point] at hChain
  have hInverseBasis :=
    finiteTangentPatchHilbertInverse_mfderiv_basis
      period hPeriod patch point basisIndex
  calc
    fderiv Real
          (fun current =>
            field (finiteTangentPatchHilbertInverse
              period hPeriod patch current))
          (finiteTangentPatchHilbertCoordinate
            period hPeriod patch point)
          (finiteTangentGeneratorHilbertBasis basisIndex) =
        mfderiv
          (modelWithCornersSelf Real
            CanonicalChartHilbertCoordinates)
          𝓘(Real)
          (field.toFun ∘
            finiteTangentPatchHilbertInverse
              period hPeriod patch)
          (finiteTangentPatchHilbertCoordinate
            period hPeriod patch point)
          (finiteTangentGeneratorHilbertBasis basisIndex) := by
      rw [mfderiv_eq_fderiv]
      rfl
    _ =
        mfderiv coverModelWithCorners 𝓘(Real)
          field.toFun point.1
          (mfderiv
            (modelWithCornersSelf Real
              CanonicalChartHilbertCoordinates)
            coverModelWithCorners
            (finiteTangentPatchHilbertInverse
              period hPeriod patch)
            (finiteTangentPatchHilbertCoordinate
              period hPeriod patch point)
            (finiteTangentGeneratorHilbertBasis basisIndex)) :=
      hChain
    _ =
        mfderiv coverModelWithCorners 𝓘(Real)
          field.toFun point.1
          (finiteTangentGeneratorLocalVector
            period hPeriod patch basisIndex point.1) := by
      rw [hInverseBasis]
    _ =
        mvfderiv coverModelWithCorners field.toFun point.1
          (finiteTangentGeneratorLocalVector
            period hPeriod patch basisIndex point.1) :=
      rfl

theorem finiteTangentPatchWeightedFieldPullback_fderiv_basis
    (patch : Patch period hPeriod)
    (point : FiniteTangentPatchDomain period hPeriod patch)
    (field : SmoothQuotientField period hPeriod Real)
    (basisIndex : FiniteTangentGeneratorBasisIndex) :
    finiteTangentGeneratorWeight period hPeriod patch point.1 *
        fderiv Real
          (fun coordinate =>
            field (finiteTangentPatchHilbertInverse
              period hPeriod patch coordinate))
          (finiteTangentPatchHilbertCoordinate
            period hPeriod patch point)
          (finiteTangentGeneratorHilbertBasis basisIndex) =
      frameDerivative period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field point.1
        (finiteTangentGeneratorIndexEquivFin period hPeriod
          (patch, basisIndex)) := by
  rw [finiteTangentPatchFieldPullback_fderiv_basis
    period hPeriod patch point field basisIndex,
    frameDerivative_eq_mfderiv,
    finiteSmoothTangentFrame_vectorAt_generator]
  exact
    ((mvfderiv coverModelWithCorners field.toFun point.1).map_smul
      (finiteTangentGeneratorWeight period hPeriod patch point.1)
      (finiteTangentGeneratorLocalVector
        period hPeriod patch basisIndex point.1)).symm

set_option backward.isDefEq.respectTransparency false in
theorem finiteTangentPatchLocalizedCoordinateFunction_fderiv_basis
    (patch : Patch period hPeriod)
    (point : FiniteTangentPatchDomain period hPeriod patch)
    (field : SmoothQuotientField period hPeriod Real)
    (basisIndex : FiniteTangentGeneratorBasisIndex) :
    fderiv Real
        (finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch field)
        (finiteTangentPatchHilbertCoordinate
          period hPeriod patch point)
        (finiteTangentGeneratorHilbertBasis basisIndex) =
      fderiv Real
          (finiteTangentPatchLocalizedWeight
            period hPeriod patch)
          (finiteTangentPatchHilbertCoordinate
            period hPeriod patch point)
          (finiteTangentGeneratorHilbertBasis basisIndex) *
          field point.1 +
        frameDerivative period hPeriod Real
          (finiteSmoothTangentFrame period hPeriod) field point.1
          (finiteTangentGeneratorIndexEquivFin period hPeriod
            (patch, basisIndex)) := by
  let coordinate :=
    finiteTangentPatchHilbertCoordinate period hPeriod patch point
  let weightPullback : CanonicalChartHilbertCoordinates → Real :=
    fun current =>
      finiteTangentGeneratorWeight period hPeriod patch
        (finiteTangentPatchHilbertInverse
          period hPeriod patch current)
  let fieldPullback : CanonicalChartHilbertCoordinates → Real :=
    fun current =>
      field (finiteTangentPatchHilbertInverse
        period hPeriod patch current)
  have hCoordinate :
      coordinate ∈ finiteTangentPatchHilbertChartTarget
        period hPeriod patch := by
    apply finiteTangentPatchHilbertSupport_subset_chartTarget
      period hPeriod patch
    rw [← finiteTangentPatchHilbertCoordinate_range
      period hPeriod patch]
    exact ⟨point, rfl⟩
  have hLocalized :
      finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch field =ᶠ[nhds coordinate]
        fun current => weightPullback current * fieldPullback current := by
    simpa [weightPullback, fieldPullback] using
      finiteTangentPatchLocalizedCoordinateFunction_eventuallyEq
        period hPeriod patch field hCoordinate
  have hWeight :
      finiteTangentPatchLocalizedWeight
          period hPeriod patch =ᶠ[nhds coordinate]
        weightPullback := by
    simpa [finiteTangentPatchLocalizedWeight, weightPullback,
      smoothConstantOne] using
      finiteTangentPatchLocalizedCoordinateFunction_eventuallyEq
        period hPeriod patch (smoothConstantOne period hPeriod)
        hCoordinate
  have hInverse :=
    finiteTangentPatchHilbertInverse_contMDiffAt
      period hPeriod patch hCoordinate
  have hWeightDiff :
      DifferentiableAt Real weightPullback coordinate :=
    ((finiteTangentGeneratorWeight_contMDiff
      period hPeriod patch).contMDiffAt.comp coordinate hInverse)
      |>.contDiffAt.differentiableAt (by simp)
  have hFieldDiff :
      DifferentiableAt Real fieldPullback coordinate :=
    (field.contMDiff_toFun.contMDiffAt.comp coordinate hInverse)
      |>.contDiffAt.differentiableAt (by simp)
  rw [hLocalized.fderiv_eq]
  change
    (fderiv Real (weightPullback * fieldPullback) coordinate)
        (finiteTangentGeneratorHilbertBasis basisIndex) = _
  rw [fderiv_mul hWeightDiff hFieldDiff]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [← hWeight.fderiv_eq]
  dsimp only [coordinate, weightPullback, fieldPullback]
  rw [finiteTangentPatchHilbertInverse_coordinate
      period hPeriod patch point,
    finiteTangentPatchWeightedFieldPullback_fderiv_basis
      period hPeriod patch point field basisIndex]
  ring

/-- Fixed bounded conversion from selected global graph derivatives to the
Euclidean coordinate gradient. -/
def finiteTangentPatchJetCoordinateGradient
    (patch : Patch period hPeriod) :
    (Fin (finiteSmoothTangentFrame period hPeriod).count → Real) →L[Real]
      CanonicalChartHilbertCoordinates :=
  (InnerProductSpace.toDual Real
      CanonicalChartHilbertCoordinates).symm.toContinuousLinearMap.comp
    (finiteTangentPatchJetCoordinateDifferential
      period hPeriod patch).toContinuousLinearMap

set_option backward.isDefEq.respectTransparency false in
theorem finiteTangentPatchLocalizedCoordinateFunction_fderiv
    (patch : Patch period hPeriod)
    (point : FiniteTangentPatchDomain period hPeriod patch)
    (field : SmoothQuotientField period hPeriod Real) :
    fderiv Real
        (finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch field)
        (finiteTangentPatchHilbertCoordinate
          period hPeriod patch point) =
      field point.1 •
          fderiv Real
            (finiteTangentPatchLocalizedWeight
              period hPeriod patch)
            (finiteTangentPatchHilbertCoordinate
              period hPeriod patch point) +
        finiteTangentPatchJetCoordinateDifferential
          period hPeriod patch
          (frameDerivative period hPeriod Real
            (finiteSmoothTangentFrame period hPeriod) field point.1) := by
  apply ContinuousLinearMap.coe_injective
  apply finiteTangentGeneratorHilbertBasis.ext
  intro basisIndex
  change
    fderiv Real
        (finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch field)
        (finiteTangentPatchHilbertCoordinate
          period hPeriod patch point)
        (finiteTangentGeneratorHilbertBasis basisIndex) =
      field point.1 *
          fderiv Real
            (finiteTangentPatchLocalizedWeight
              period hPeriod patch)
            (finiteTangentPatchHilbertCoordinate
              period hPeriod patch point)
            (finiteTangentGeneratorHilbertBasis basisIndex) +
        finiteTangentPatchJetCoordinateDifferential
          period hPeriod patch
          (frameDerivative period hPeriod Real
            (finiteSmoothTangentFrame period hPeriod) field point.1)
          (finiteTangentGeneratorHilbertBasis basisIndex)
  rw [finiteTangentPatchJetCoordinateDifferential_basis]
  have hDerivative :=
    finiteTangentPatchLocalizedCoordinateFunction_fderiv_basis
      period hPeriod patch point field basisIndex
  nlinarith only [hDerivative]

theorem finiteTangentPatchLocalizedCoordinateFunction_grad
    (patch : Patch period hPeriod)
    (point : FiniteTangentPatchDomain period hPeriod patch)
    (field : SmoothQuotientField period hPeriod Real) :
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad
        (E := CanonicalChartHilbertCoordinates)
        (finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch field)
        (finiteTangentPatchHilbertCoordinate
          period hPeriod patch point) =
      field point.1 •
          RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad
            (E := CanonicalChartHilbertCoordinates)
            (finiteTangentPatchLocalizedWeight
              period hPeriod patch)
            (finiteTangentPatchHilbertCoordinate
              period hPeriod patch point) +
        finiteTangentPatchJetCoordinateGradient
          period hPeriod patch
          (frameDerivative period hPeriod Real
            (finiteSmoothTangentFrame period hPeriod) field point.1) := by
  simp only [
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad]
  rw [finiteTangentPatchLocalizedCoordinateFunction_fderiv
    period hPeriod patch point field]
  simp [finiteTangentPatchJetCoordinateGradient]
  rfl

/-- Uniform pointwise value-and-gradient estimate on one compact patch. -/
theorem exists_finiteTangentPatchPointwiseGraphBound
    (patch : Patch period hPeriod) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ (point : FiniteTangentPatchDomain period hPeriod patch)
        (field : SmoothQuotientField period hPeriod Real),
        ‖finiteTangentPatchLocalizedCoordinateFunction
            period hPeriod patch field
            (finiteTangentPatchHilbertCoordinate
              period hPeriod patch point)‖ ≤
            constant *
              ‖smoothFirstJet period hPeriod Real
                (finiteSmoothTangentFrame period hPeriod)
                field point.1‖ ∧
          ‖RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad
              (E := CanonicalChartHilbertCoordinates)
              (finiteTangentPatchLocalizedCoordinateFunction
                period hPeriod patch field)
              (finiteTangentPatchHilbertCoordinate
                period hPeriod patch point)‖ ≤
            constant *
              ‖smoothFirstJet period hPeriod Real
                (finiteSmoothTangentFrame period hPeriod)
                field point.1‖ := by
  let weightGradient :=
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad
      (E := CanonicalChartHilbertCoordinates)
      (finiteTangentPatchLocalizedWeight period hPeriod patch)
  have hWeightGradientContinuous : Continuous weightGradient :=
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.continuous_grad
      ((finiteTangentPatchLocalizedWeight_contDiff
        period hPeriod patch).of_le (by simp))
  obtain ⟨rawWeightBound, hRawWeightBound⟩ :=
    (finiteTangentPatchHilbertSupport_isCompact
      period hPeriod patch).exists_bound_of_continuousOn
        hWeightGradientContinuous.continuousOn
  let weightBound := max rawWeightBound 0
  let gradientMap :=
    finiteTangentPatchJetCoordinateGradient period hPeriod patch
  let constant := 1 + weightBound + ‖gradientMap‖
  have hWeightBoundNonneg : 0 ≤ weightBound :=
    le_max_right _ _
  have hGradientMapNonneg : 0 ≤ ‖gradientMap‖ :=
    norm_nonneg _
  have hConstantNonneg : 0 ≤ constant := by
    dsimp only [constant]
    linarith
  have hConstantOne : 1 ≤ constant := by
    dsimp only [constant]
    linarith
  refine ⟨constant, hConstantNonneg, ?_⟩
  intro point field
  let jet :=
    smoothFirstJet period hPeriod Real
      (finiteSmoothTangentFrame period hPeriod) field point.1
  have hCoordinateSupport :
      finiteTangentPatchHilbertCoordinate period hPeriod patch point ∈
        finiteTangentPatchHilbertSupport period hPeriod patch := by
    rw [← finiteTangentPatchHilbertCoordinate_range
      period hPeriod patch]
    exact ⟨point, rfl⟩
  have hWeightGradient :
      ‖weightGradient
          (finiteTangentPatchHilbertCoordinate
            period hPeriod patch point)‖ ≤ weightBound :=
    (hRawWeightBound _ hCoordinateSupport).trans
      (le_max_left _ _)
  have hValueJet : ‖field point.1‖ ≤ ‖jet‖ := by
    simp [jet, smoothFirstJet]
  have hDerivativeJet :
      ‖frameDerivative period hPeriod Real
          (finiteSmoothTangentFrame period hPeriod) field point.1‖ ≤
        ‖jet‖ := by
    simp [jet, smoothFirstJet]
  have hWeightAbs :
      ‖finiteTangentGeneratorWeight period hPeriod patch point.1‖ ≤ 1 := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (finiteTangentGeneratorWeight_nonneg
          period hPeriod patch point.1)]
    exact finiteTangentGeneratorWeight_le_one
      period hPeriod patch point.1
  constructor
  · rw [finiteTangentPatchLocalizedCoordinateFunction_coordinate
      period hPeriod patch point field, norm_mul]
    calc
      ‖finiteTangentGeneratorWeight period hPeriod patch point.1‖ *
          ‖field point.1‖ ≤ 1 * ‖field point.1‖ :=
        mul_le_mul_of_nonneg_right hWeightAbs (norm_nonneg _)
      _ = ‖field point.1‖ := one_mul _
      _ ≤ ‖jet‖ := hValueJet
      _ ≤ constant * ‖jet‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hConstantOne
  · rw [finiteTangentPatchLocalizedCoordinateFunction_grad
      period hPeriod patch point field]
    calc
      ‖field point.1 •
            weightGradient
              (finiteTangentPatchHilbertCoordinate
                period hPeriod patch point) +
          gradientMap
            (frameDerivative period hPeriod Real
              (finiteSmoothTangentFrame period hPeriod) field point.1)‖ ≤
          ‖field point.1 •
            weightGradient
              (finiteTangentPatchHilbertCoordinate
                period hPeriod patch point)‖ +
          ‖gradientMap
            (frameDerivative period hPeriod Real
              (finiteSmoothTangentFrame period hPeriod) field point.1)‖ :=
        norm_add_le _ _
      _ ≤
          weightBound * ‖field point.1‖ +
            ‖gradientMap‖ *
              ‖frameDerivative period hPeriod Real
                (finiteSmoothTangentFrame period hPeriod)
                field point.1‖ := by
        apply add_le_add
        · rw [norm_smul, mul_comm]
          exact mul_le_mul_of_nonneg_right
            hWeightGradient (norm_nonneg _)
        · exact gradientMap.le_opNorm _
      _ ≤
          weightBound * ‖jet‖ +
            ‖gradientMap‖ * ‖jet‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            hValueJet hWeightBoundNonneg)
          (mul_le_mul_of_nonneg_left
            hDerivativeJet hGradientMapNonneg)
      _ = (weightBound + ‖gradientMap‖) * ‖jet‖ := by
        ring
      _ ≤ constant * ‖jet‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp only [constant]
        linarith

/-- The localized coordinate representative as a Euclidean `C¹_c`
function. -/
def finiteTangentPatchLocalizedC1c
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c
      (E := CanonicalChartHilbertCoordinates)) :=
  ⟨finiteTangentPatchLocalizedCoordinateFunction
      period hPeriod patch field,
    (finiteTangentPatchLocalizedCoordinateFunction_contDiff
      period hPeriod patch field).of_le (by simp),
    HasCompactSupport.intro
      (finiteTangentPatchHilbertSupport_isCompact
        period hPeriod patch)
      (fun coordinate hCoordinate => by
        by_contra hNe
        exact hCoordinate
          (finiteTangentPatchLocalizedCoordinateFunction_tsupport
            period hPeriod patch field (subset_closure hNe)))⟩

/-- Partition-weighted physical scalar on the quotient. -/
def finiteTangentPatchWeightedSmoothField
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    finiteTangentGeneratorWeight period hPeriod patch point * field point
  contMDiff_toFun :=
    (finiteTangentGeneratorWeight_contMDiff
      period hPeriod patch).mul field.contMDiff_toFun

/-- Global physical `L²` representative of one partition-weighted field. -/
def finiteTangentPatchWeightedBulkL2
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    CanonicalPhysicalBulkL2 period hPeriod :=
  smoothToCanonicalPhysicalBulkL2 period hPeriod
    (finiteTangentPatchWeightedSmoothField
      period hPeriod patch field)

theorem finiteTangentPatchWeightedBulkL2_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    (finiteTangentPatchWeightedBulkL2
        period hPeriod patch field :
      EffectiveQuotient period hPeriod → Real) =ᵐ[
        intrinsicCanonicalLorentzVolumeMeasure period hPeriod]
      fun point =>
        finiteTangentGeneratorWeight period hPeriod patch point *
          field point := by
  letI :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact
    smoothFieldToL2_ae period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (finiteTangentPatchWeightedSmoothField
        period hPeriod patch field)

/-- Restriction of one weighted physical field to its closed patch. -/
def finiteTangentPatchWeightedRestrictedL2
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    Lp Real (2 : ENNReal)
      ((intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
        (finiteTangentGeneratorClosedPatch period hPeriod patch)) :=
  MeasureTheory.Lp.changeMeasureL
    (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (ν := (intrinsicCanonicalLorentzVolumeMeasure
      period hPeriod).restrict
        (finiteTangentGeneratorClosedPatch period hPeriod patch))
    (E := Real) (p := (2 : ENNReal)) (c := 1)
    (by simp) (by simpa using
      (Measure.restrict_le_self :
        (intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).restrict
            (finiteTangentGeneratorClosedPatch period hPeriod patch) ≤
          intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
    (by simp)
    (finiteTangentPatchWeightedBulkL2
      period hPeriod patch field)

theorem finiteTangentPatchWeightedRestrictedL2_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    (finiteTangentPatchWeightedRestrictedL2
        period hPeriod patch field :
      EffectiveQuotient period hPeriod → Real) =ᵐ[
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
          (finiteTangentGeneratorClosedPatch period hPeriod patch)]
      fun point =>
        finiteTangentGeneratorWeight period hPeriod patch point *
          field point := by
  have hChanged :
      (finiteTangentPatchWeightedRestrictedL2
          period hPeriod patch field :
        EffectiveQuotient period hPeriod → Real) =ᵐ[
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
            (finiteTangentGeneratorClosedPatch period hPeriod patch)]
        finiteTangentPatchWeightedBulkL2
          period hPeriod patch field :=
    MeasureTheory.Lp.changeMeasureL_coeFn_ae_eq
      (by simp) (by simpa using
        (Measure.restrict_le_self :
          (intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod).restrict
              (finiteTangentGeneratorClosedPatch period hPeriod patch) ≤
            intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
      (by simp)
      (finiteTangentPatchWeightedBulkL2
        period hPeriod patch field)
  exact hChanged.trans
    (Measure.absolutelyContinuous_restrict.ae_eq
      (finiteTangentPatchWeightedBulkL2_coeFn_ae_eq
        period hPeriod patch field))

/-- Value component of one localized smooth Euclidean graph. -/
def finiteTangentPatchLocalizedValueL2
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    Lp Real (2 : ENNReal)
      (volume : Measure CanonicalChartHilbertCoordinates) :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2
    (μ := (volume : Measure CanonicalChartHilbertCoordinates))
    (E := CanonicalChartHilbertCoordinates)
    (finiteTangentPatchLocalizedC1c period hPeriod patch field)

/-- Gradient component of one localized smooth Euclidean graph. -/
def finiteTangentPatchLocalizedGradientL2
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    Lp CanonicalChartHilbertCoordinates (2 : ENNReal)
      (volume : Measure CanonicalChartHilbertCoordinates) :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.toL2Grad
    (μ := (volume : Measure CanonicalChartHilbertCoordinates))
    (E := CanonicalChartHilbertCoordinates)
    (finiteTangentPatchLocalizedC1c period hPeriod patch field)

theorem finiteTangentPatchLocalizedValueL2_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    (finiteTangentPatchLocalizedValueL2
        period hPeriod patch field :
      CanonicalChartHilbertCoordinates → Real) =ᵐ[volume]
      finiteTangentPatchLocalizedCoordinateFunction
        period hPeriod patch field := by
  exact
    (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_of_mem_C1c
      (μ := (volume : Measure CanonicalChartHilbertCoordinates))
      (E := CanonicalChartHilbertCoordinates)
      (finiteTangentPatchLocalizedC1c period hPeriod patch field).2).coeFn_toLp

theorem finiteTangentPatchLocalizedGradientL2_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    (finiteTangentPatchLocalizedGradientL2
        period hPeriod patch field :
      CanonicalChartHilbertCoordinates →
        CanonicalChartHilbertCoordinates) =ᵐ[volume]
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad
        (E := CanonicalChartHilbertCoordinates)
        (finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch field) := by
  exact
    (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.memLp_grad_of_mem_C1c
      (μ := (volume : Measure CanonicalChartHilbertCoordinates))
      (E := CanonicalChartHilbertCoordinates)
      (finiteTangentPatchLocalizedC1c period hPeriod patch field).2).coeFn_toLp

theorem finiteTangentPatchLocalizedValueL2_zero_off_support
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ∀ᵐ coordinate ∂(volume :
        Measure CanonicalChartHilbertCoordinates),
      coordinate ∉ finiteTangentPatchHilbertSupport
          period hPeriod patch →
        finiteTangentPatchLocalizedValueL2
          period hPeriod patch field coordinate = 0 := by
  filter_upwards [
    finiteTangentPatchLocalizedValueL2_coeFn_ae_eq
      period hPeriod patch field] with coordinate hValue
  intro hCoordinate
  rw [hValue]
  by_contra hNe
  exact hCoordinate
    (finiteTangentPatchLocalizedCoordinateFunction_tsupport
      period hPeriod patch field (subset_closure hNe))

theorem finiteTangentPatchLocalizedGradientL2_zero_off_support
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ∀ᵐ coordinate ∂(volume :
        Measure CanonicalChartHilbertCoordinates),
      coordinate ∉ finiteTangentPatchHilbertSupport
          period hPeriod patch →
        finiteTangentPatchLocalizedGradientL2
          period hPeriod patch field coordinate = 0 := by
  filter_upwards [
    finiteTangentPatchLocalizedGradientL2_coeFn_ae_eq
      period hPeriod patch field] with coordinate hGradient
  intro hCoordinate
  rw [hGradient]
  by_contra hNe
  exact hCoordinate
    (finiteTangentPatchLocalizedCoordinateFunction_tsupport
      period hPeriod patch field
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.tsupport_grad_subset
        (finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch field) (subset_closure hNe)))

/-- The global smooth first jet, restricted to one canonical patch. -/
def finiteTangentPatchSmoothFirstJetSourceL2
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    PatchSourceLp
      (Fiber :=
        Real ×
          (Fin (finiteSmoothTangentFrame period hPeriod).count → Real))
      period hPeriod patch := by
  letI :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact
    finiteTangentPatchRestrictQuotientLp
      (Fiber :=
        Real ×
          (Fin (finiteSmoothTangentFrame period hPeriod).count → Real))
      period hPeriod patch
      (smoothFirstJetToL2 period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field)

theorem finiteTangentPatchSmoothFirstJetSourceL2_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    (finiteTangentPatchSmoothFirstJetSourceL2
        period hPeriod patch field :
      FiniteTangentPatchDomain period hPeriod patch →
        Real ×
          (Fin (finiteSmoothTangentFrame period hPeriod).count → Real)) =ᵐ[
        finiteTangentPatchCanonicalSourceMeasure period hPeriod patch]
      fun point =>
        smoothFirstJet period hPeriod Real
          (finiteSmoothTangentFrame period hPeriod) field point.1 := by
  letI :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  let globalJet :=
    smoothFirstJetToL2 period hPeriod Real
      (finiteSmoothTangentFrame period hPeriod)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field
  have hRestricted :=
    finiteTangentPatchRestrictQuotientLp_coeFn_ae_eq
      (Fiber :=
        Real ×
          (Fin (finiteSmoothTangentFrame period hPeriod).count → Real))
      period hPeriod patch globalJet
  have hGlobal :
      (globalJet :
        EffectiveQuotient period hPeriod →
          Real ×
            (Fin (finiteSmoothTangentFrame period hPeriod).count → Real)) =ᵐ[
          intrinsicCanonicalLorentzVolumeMeasure period hPeriod]
        smoothFirstJet period hPeriod Real
          (finiteSmoothTangentFrame period hPeriod) field := by
    simpa [globalJet, smoothFirstJetToL2] using
      (smoothFirstJet_memLp period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        field).coeFn_toLp
  have hSubtypeQMP :
      Measure.QuasiMeasurePreserving
        (Subtype.val :
          FiniteTangentPatchDomain period hPeriod patch →
            EffectiveQuotient period hPeriod)
        (finiteTangentPatchCanonicalSourceMeasure period hPeriod patch)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    (finiteTangentPatchSubtypeMeasurePreserving
      period hPeriod patch).quasiMeasurePreserving.mono_right
        Measure.absolutelyContinuous_restrict
  exact hRestricted.trans (hSubtypeQMP.ae_eq_comp hGlobal)

theorem finiteTangentPatchSmoothFirstJetSourceL2_norm_le
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ‖finiteTangentPatchSmoothFirstJetSourceL2
        period hPeriod patch field‖ ≤
      ‖finiteTangentPatchRestrictQuotientLp
        (Fiber :=
          Real ×
            (Fin (finiteSmoothTangentFrame period hPeriod).count → Real))
        period hPeriod patch‖ *
        ‖smoothToCanonicalPhysicalScalarH1
          period hPeriod field‖ := by
  letI :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact
    (finiteTangentPatchRestrictQuotientLp
      (Fiber :=
        Real ×
          (Fin (finiteSmoothTangentFrame period hPeriod).count → Real))
      period hPeriod patch).le_opNorm
      (smoothFirstJetToL2 period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field)

theorem finiteTangentPatchLocalizedValueSource_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field : SmoothQuotientField period hPeriod Real) :
    (finiteTangentPatchAmbientToSourceLp
        (Fiber := Real) period hPeriod patch comparison
        (finiteTangentPatchLocalizedValueL2
          period hPeriod patch field) :
      FiniteTangentPatchDomain period hPeriod patch → Real) =ᵐ[
        finiteTangentPatchCanonicalSourceMeasure period hPeriod patch]
      fun point =>
        finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch field
          (finiteTangentPatchHilbertCoordinate
            period hPeriod patch point) := by
  refine
    (finiteTangentPatchAmbientToSourceLp_coeFn_ae_eq
      (Fiber := Real) period hPeriod patch comparison
      (finiteTangentPatchLocalizedValueL2
        period hPeriod patch field)).trans ?_
  exact
    (finiteTangentPatchHilbertCoordinateQuasiMeasurePreserving
      period hPeriod patch comparison).ae_eq_comp
      (finiteTangentPatchLocalizedValueL2_coeFn_ae_eq
        period hPeriod patch field)

/-- The localized Euclidean value pulls back to the same canonical patch
class as the globally partition-weighted physical field. -/
theorem finiteTangentPatchLocalizedValueSource_eq_weightedPullback
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field : SmoothQuotientField period hPeriod Real) :
    finiteTangentPatchAmbientToSourceLp
        (Fiber := Real) period hPeriod patch comparison
        (finiteTangentPatchLocalizedValueL2
          period hPeriod patch field) =
      finiteTangentPatchRestrictedQuotientToSourceL2
        period hPeriod patch
        (finiteTangentPatchWeightedRestrictedL2
          period hPeriod patch field) := by
  apply Lp.ext
  have hLeft :=
    finiteTangentPatchLocalizedValueSource_coeFn_ae_eq
      period hPeriod patch comparison field
  have hRight :
      (finiteTangentPatchRestrictedQuotientToSourceL2
          period hPeriod patch
          (finiteTangentPatchWeightedRestrictedL2
            period hPeriod patch field) :
        FiniteTangentPatchDomain period hPeriod patch → Real) =ᵐ[
          finiteTangentPatchCanonicalSourceMeasure period hPeriod patch]
        fun point =>
          finiteTangentPatchWeightedRestrictedL2
            period hPeriod patch field point.1 :=
    MeasureTheory.Lp.coeFn_compMeasurePreserving
      (finiteTangentPatchWeightedRestrictedL2
        period hPeriod patch field)
      (finiteTangentPatchSubtypeMeasurePreserving
        period hPeriod patch)
  have hWeighted :=
    (finiteTangentPatchSubtypeMeasurePreserving
      period hPeriod patch).quasiMeasurePreserving.ae_eq_comp
        (finiteTangentPatchWeightedRestrictedL2_coeFn_ae_eq
          period hPeriod patch field)
  filter_upwards [hLeft, hRight, hWeighted]
    with point hLeft hRight hWeighted
  rw [hLeft,
    finiteTangentPatchLocalizedCoordinateFunction_coordinate
      period hPeriod patch point field,
    hRight]
  simpa [Function.comp_apply] using hWeighted.symm

/-- Extension by zero of the restricted weighted field recovers its global
physical `L²` class exactly. -/
theorem finiteTangentPatchWeightedExtension_eq
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    (MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (E := Real) (p := (2 : ENNReal))
      (s := finiteTangentGeneratorClosedPatch period hPeriod patch)
      (finiteTangentGeneratorClosedPatch_isClosed
        period hPeriod patch).measurableSet)
        (finiteTangentPatchWeightedRestrictedL2
          period hPeriod patch field) =
      finiteTangentPatchWeightedBulkL2
        period hPeriod patch field := by
  apply Lp.ext
  let closedPatch :=
    finiteTangentGeneratorClosedPatch period hPeriod patch
  have hClosedPatchMeasurable : MeasurableSet closedPatch :=
    (finiteTangentGeneratorClosedPatch_isClosed
      period hPeriod patch).measurableSet
  have hExtended :
      ((MeasureTheory.Lp.extendByZeroₗᵢ
          (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          (E := Real) (p := (2 : ENNReal))
          (s := closedPatch) hClosedPatchMeasurable)
          (finiteTangentPatchWeightedRestrictedL2
            period hPeriod patch field) :
        EffectiveQuotient period hPeriod → Real) =ᵐ[
          intrinsicCanonicalLorentzVolumeMeasure period hPeriod]
        closedPatch.indicator fun point =>
          finiteTangentPatchWeightedRestrictedL2
            period hPeriod patch field point :=
    MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq
      hClosedPatchMeasurable
      (finiteTangentPatchWeightedRestrictedL2
        period hPeriod patch field)
  have hRestrictedOn :
      ∀ᵐ point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod,
        point ∈ closedPatch →
          finiteTangentPatchWeightedRestrictedL2
              period hPeriod patch field point =
            finiteTangentGeneratorWeight
              period hPeriod patch point * field point :=
    (ae_restrict_iff' hClosedPatchMeasurable).1
      (finiteTangentPatchWeightedRestrictedL2_coeFn_ae_eq
        period hPeriod patch field)
  have hBulk :=
    finiteTangentPatchWeightedBulkL2_coeFn_ae_eq
      period hPeriod patch field
  filter_upwards [hExtended, hRestrictedOn, hBulk]
    with point hExtended hRestricted hBulk
  rw [hExtended, hBulk]
  by_cases hPoint : point ∈ closedPatch
  · simp [Set.indicator_of_mem hPoint, hRestricted hPoint]
  · have hWeight :
        finiteTangentGeneratorWeight period hPeriod patch point = 0 := by
      by_contra hNe
      exact hPoint (subset_closure hNe)
    simp [Set.indicator_of_notMem hPoint, hWeight]

/-- One smooth localized Euclidean value, transported back to the quotient,
is exactly the corresponding partition-weighted physical field. -/
theorem finiteTangentPatchLocalizedValueExtension_eq
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field : SmoothQuotientField period hPeriod Real) :
    finiteTangentPatchSourceToQuotientL2 period hPeriod patch
        (finiteTangentPatchAmbientToSourceLp
          (Fiber := Real) period hPeriod patch comparison
          (finiteTangentPatchLocalizedValueL2
            period hPeriod patch field)) =
      finiteTangentPatchWeightedBulkL2
        period hPeriod patch field := by
  rw [finiteTangentPatchLocalizedValueSource_eq_weightedPullback
      period hPeriod patch comparison field,
    finiteTangentPatchSourceToQuotientL2_pullback
      period hPeriod patch,
    finiteTangentPatchWeightedExtension_eq
      period hPeriod patch field]

theorem finiteTangentPatchLocalizedGradientSource_coeFn_ae_eq
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch)
    (field : SmoothQuotientField period hPeriod Real) :
    (finiteTangentPatchAmbientToSourceLp
        (Fiber := CanonicalChartHilbertCoordinates)
        period hPeriod patch comparison
        (finiteTangentPatchLocalizedGradientL2
          period hPeriod patch field) :
      FiniteTangentPatchDomain period hPeriod patch →
        CanonicalChartHilbertCoordinates) =ᵐ[
          finiteTangentPatchCanonicalSourceMeasure period hPeriod patch]
      fun point =>
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad
          (E := CanonicalChartHilbertCoordinates)
          (finiteTangentPatchLocalizedCoordinateFunction
            period hPeriod patch field)
          (finiteTangentPatchHilbertCoordinate
            period hPeriod patch point) := by
  refine
    (finiteTangentPatchAmbientToSourceLp_coeFn_ae_eq
      (Fiber := CanonicalChartHilbertCoordinates)
      period hPeriod patch comparison
      (finiteTangentPatchLocalizedGradientL2
        period hPeriod patch field)).trans ?_
  exact
    (finiteTangentPatchHilbertCoordinateQuasiMeasurePreserving
      period hPeriod patch comparison).ae_eq_comp
      (finiteTangentPatchLocalizedGradientL2_coeFn_ae_eq
        period hPeriod patch field)

/-- Both localized Euclidean graph components are controlled on canonical
patch volume by the restricted global first jet. -/
theorem exists_finiteTangentPatchLocalizedSourceGraphBound
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ field : SmoothQuotientField period hPeriod Real,
        ‖finiteTangentPatchAmbientToSourceLp
            (Fiber := Real) period hPeriod patch comparison
            (finiteTangentPatchLocalizedValueL2
              period hPeriod patch field)‖ ≤
          constant *
            ‖finiteTangentPatchSmoothFirstJetSourceL2
              period hPeriod patch field‖ ∧
        ‖finiteTangentPatchAmbientToSourceLp
            (Fiber := CanonicalChartHilbertCoordinates)
            period hPeriod patch comparison
            (finiteTangentPatchLocalizedGradientL2
              period hPeriod patch field)‖ ≤
          constant *
            ‖finiteTangentPatchSmoothFirstJetSourceL2
              period hPeriod patch field‖ := by
  obtain ⟨constant, hConstant, hPointwise⟩ :=
    exists_finiteTangentPatchPointwiseGraphBound
      period hPeriod patch
  refine ⟨constant, hConstant, ?_⟩
  intro field
  constructor
  · apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [
      finiteTangentPatchLocalizedValueSource_coeFn_ae_eq
        period hPeriod patch comparison field,
      finiteTangentPatchSmoothFirstJetSourceL2_coeFn_ae_eq
        period hPeriod patch field] with point hValue hJet
    rw [hValue, hJet]
    exact (hPointwise point field).1
  · apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [
      finiteTangentPatchLocalizedGradientSource_coeFn_ae_eq
        period hPeriod patch comparison field,
      finiteTangentPatchSmoothFirstJetSourceL2_coeFn_ae_eq
        period hPeriod patch field] with point hGradient hJet
    rw [hGradient, hJet]
    exact (hPointwise point field).2

/-- Ambient Euclidean value and gradient norms are bounded by the completed
physical first-jet norm on the smooth core. -/
theorem exists_finiteTangentPatchLocalizedAmbientGraphBound
    (patch : Patch period hPeriod)
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    ∃ constant : Real,
      ∀ field : SmoothQuotientField period hPeriod Real,
        ‖finiteTangentPatchLocalizedValueL2
            period hPeriod patch field‖ ≤
          constant *
            ‖smoothToCanonicalPhysicalScalarH1
              period hPeriod field‖ ∧
        ‖finiteTangentPatchLocalizedGradientL2
            period hPeriod patch field‖ ≤
          constant *
            ‖smoothToCanonicalPhysicalScalarH1
              period hPeriod field‖ := by
  obtain ⟨sourceConstant, hSourceConstant, hSource⟩ :=
    exists_finiteTangentPatchLocalizedSourceGraphBound
      period hPeriod patch comparison
  let valueTransportNorm :=
    ‖finiteTangentPatchCoordinateToAmbientLp
      (Fiber := Real) period hPeriod patch comparison‖
  let gradientTransportNorm :=
    ‖finiteTangentPatchCoordinateToAmbientLp
      (Fiber := CanonicalChartHilbertCoordinates)
      period hPeriod patch comparison‖
  let transportNorm := max valueTransportNorm gradientTransportNorm
  let restrictionNorm :=
    ‖finiteTangentPatchRestrictQuotientLp
      (Fiber :=
        Real ×
          (Fin (finiteSmoothTangentFrame period hPeriod).count → Real))
      period hPeriod patch‖
  let constant := transportNorm * sourceConstant * restrictionNorm
  have hTransportNonneg : 0 ≤ transportNorm := by
    exact (norm_nonneg _).trans (le_max_left _ _)
  refine ⟨constant, ?_⟩
  intro field
  have hJet :=
    finiteTangentPatchSmoothFirstJetSourceL2_norm_le
      period hPeriod patch field
  have hSourceField := hSource field
  constructor
  · calc
      ‖finiteTangentPatchLocalizedValueL2
          period hPeriod patch field‖ ≤
        valueTransportNorm *
          ‖finiteTangentPatchAmbientToSourceLp
            (Fiber := Real) period hPeriod patch comparison
            (finiteTangentPatchLocalizedValueL2
              period hPeriod patch field)‖ := by
        exact
          finiteTangentPatchAmbient_norm_le_source_norm_of_support
            (Fiber := Real) period hPeriod patch comparison
            (finiteTangentPatchLocalizedValueL2
              period hPeriod patch field)
            (finiteTangentPatchLocalizedValueL2_zero_off_support
              period hPeriod patch field)
      _ ≤ valueTransportNorm *
          (sourceConstant *
            ‖finiteTangentPatchSmoothFirstJetSourceL2
              period hPeriod patch field‖) :=
        mul_le_mul_of_nonneg_left hSourceField.1 (norm_nonneg _)
      _ ≤ transportNorm *
          (sourceConstant *
            ‖finiteTangentPatchSmoothFirstJetSourceL2
              period hPeriod patch field‖) := by
        apply mul_le_mul_of_nonneg_right
        · exact le_max_left _ _
        · positivity
      _ ≤ transportNorm *
          (sourceConstant *
            (restrictionNorm *
              ‖smoothToCanonicalPhysicalScalarH1
                period hPeriod field‖)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hJet hSourceConstant
        · exact hTransportNonneg
      _ = constant *
          ‖smoothToCanonicalPhysicalScalarH1
            period hPeriod field‖ := by
        simp only [constant]
        ring
  · calc
      ‖finiteTangentPatchLocalizedGradientL2
          period hPeriod patch field‖ ≤
        gradientTransportNorm *
          ‖finiteTangentPatchAmbientToSourceLp
            (Fiber := CanonicalChartHilbertCoordinates)
            period hPeriod patch comparison
            (finiteTangentPatchLocalizedGradientL2
              period hPeriod patch field)‖ := by
        exact
          finiteTangentPatchAmbient_norm_le_source_norm_of_support
            (Fiber := CanonicalChartHilbertCoordinates)
            period hPeriod patch comparison
            (finiteTangentPatchLocalizedGradientL2
              period hPeriod patch field)
            (finiteTangentPatchLocalizedGradientL2_zero_off_support
              period hPeriod patch field)
      _ ≤ gradientTransportNorm *
          (sourceConstant *
            ‖finiteTangentPatchSmoothFirstJetSourceL2
              period hPeriod patch field‖) :=
        mul_le_mul_of_nonneg_left hSourceField.2 (norm_nonneg _)
      _ ≤ transportNorm *
          (sourceConstant *
            ‖finiteTangentPatchSmoothFirstJetSourceL2
              period hPeriod patch field‖) := by
        apply mul_le_mul_of_nonneg_right
        · exact le_max_right _ _
        · positivity
      _ ≤ transportNorm *
          (sourceConstant *
            (restrictionNorm *
              ‖smoothToCanonicalPhysicalScalarH1
                period hPeriod field‖)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hJet hSourceConstant
        · exact hTransportNonneg
      _ = constant *
          ‖smoothToCanonicalPhysicalScalarH1
            period hPeriod field‖ := by
        simp only [constant]
        ring

/-- The smooth chart localizer, before proving its global graph-norm
bound. -/
def finiteTangentPatchSmoothEuclideanH1
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    FiniteAtlasEuclideanH1 period hPeriod :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c.toH1On
    (E := CanonicalChartHilbertCoordinates)
    (finiteAtlasHilbertSupport period hPeriod)
    (finiteAtlasHilbertSupport_measurable period hPeriod)
    (finiteTangentPatchLocalizedC1c period hPeriod patch field)
    ((finiteTangentPatchLocalizedCoordinateFunction_tsupport
      period hPeriod patch field).trans
        (Set.subset_iUnion
          (fun index : Patch period hPeriod =>
            finiteTangentPatchHilbertSupport period hPeriod index)
          patch))

/-- The smooth chart localizer satisfies the graph-norm bound required for
extension to completed physical `H¹`. -/
theorem exists_finiteTangentPatchSmoothEuclideanH1_bound
    (patch : Patch period hPeriod) :
    ∃ constant : Real,
      ∀ field : SmoothQuotientField period hPeriod Real,
        ‖finiteTangentPatchSmoothEuclideanH1
            period hPeriod patch field‖ ≤
          constant *
            ‖smoothToCanonicalPhysicalScalarH1
              period hPeriod field‖ := by
  obtain ⟨constant, hBound⟩ :=
    exists_finiteTangentPatchLocalizedAmbientGraphBound
      period hPeriod patch
      (finiteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch)
  refine ⟨constant, ?_⟩
  intro field
  change
    max
        ‖finiteTangentPatchLocalizedValueL2
          period hPeriod patch field‖
        ‖finiteTangentPatchLocalizedGradientL2
          period hPeriod patch field‖ ≤
      constant *
        ‖smoothToCanonicalPhysicalScalarH1
          period hPeriod field‖
  rw [max_le_iff]
  exact hBound field

theorem finiteTangentPatchLocalizedCoordinateFunction_add
    (patch : Patch period hPeriod)
    (first second : SmoothQuotientField period hPeriod Real) :
    finiteTangentPatchLocalizedCoordinateFunction
        period hPeriod patch (first + second) =
      finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch first +
        finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch second := by
  funext coordinate
  by_cases hCoordinate :
      coordinate ∈ finiteTangentPatchHilbertChartTarget
        period hPeriod patch
  · simp only [finiteTangentPatchLocalizedCoordinateFunction,
      Set.indicator_of_mem hCoordinate, Pi.add_apply]
    change
      finiteTangentGeneratorWeight period hPeriod patch
          (finiteTangentPatchHilbertInverse
            period hPeriod patch coordinate) *
          (first (finiteTangentPatchHilbertInverse
              period hPeriod patch coordinate) +
            second (finiteTangentPatchHilbertInverse
              period hPeriod patch coordinate)) =
        _
    rw [mul_add]
  · simp [finiteTangentPatchLocalizedCoordinateFunction,
      Set.indicator_of_notMem hCoordinate]

theorem finiteTangentPatchLocalizedCoordinateFunction_smul
    (patch : Patch period hPeriod)
    (scalar : Real)
    (field : SmoothQuotientField period hPeriod Real) :
    finiteTangentPatchLocalizedCoordinateFunction
        period hPeriod patch (scalar • field) =
      scalar •
        finiteTangentPatchLocalizedCoordinateFunction
          period hPeriod patch field := by
  funext coordinate
  by_cases hCoordinate :
      coordinate ∈ finiteTangentPatchHilbertChartTarget
        period hPeriod patch
  · simp [finiteTangentPatchLocalizedCoordinateFunction,
      Set.indicator_of_mem hCoordinate, mul_left_comm]
  · simp [finiteTangentPatchLocalizedCoordinateFunction,
      Set.indicator_of_notMem hCoordinate]

theorem finiteTangentPatchLocalizedC1c_add
    (patch : Patch period hPeriod)
    (first second : SmoothQuotientField period hPeriod Real) :
    finiteTangentPatchLocalizedC1c
        period hPeriod patch (first + second) =
      finiteTangentPatchLocalizedC1c period hPeriod patch first +
        finiteTangentPatchLocalizedC1c
          period hPeriod patch second :=
  Subtype.ext
    (finiteTangentPatchLocalizedCoordinateFunction_add
      period hPeriod patch first second)

theorem finiteTangentPatchLocalizedC1c_smul
    (patch : Patch period hPeriod)
    (scalar : Real)
    (field : SmoothQuotientField period hPeriod Real) :
    finiteTangentPatchLocalizedC1c
        period hPeriod patch (scalar • field) =
      scalar •
        finiteTangentPatchLocalizedC1c
          period hPeriod patch field :=
  Subtype.ext
    (finiteTangentPatchLocalizedCoordinateFunction_smul
      period hPeriod patch scalar field)

/-- Linear smooth-core localizer on one finite chart. -/
def finiteTangentPatchSmoothEuclideanH1LinearMap
    (patch : Patch period hPeriod) :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      FiniteAtlasEuclideanH1 period hPeriod where
  toFun :=
    finiteTangentPatchSmoothEuclideanH1 period hPeriod patch
  map_add' first second := by
    apply Subtype.ext
    apply Subtype.ext
    change
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
          (μ := (volume : Measure CanonicalChartHilbertCoordinates))
          (E := CanonicalChartHilbertCoordinates)
          (finiteTangentPatchLocalizedC1c
            period hPeriod patch (first + second)) =
        RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
            (μ := (volume : Measure CanonicalChartHilbertCoordinates))
            (E := CanonicalChartHilbertCoordinates)
            (finiteTangentPatchLocalizedC1c
              period hPeriod patch first) +
          RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
            (μ := (volume : Measure CanonicalChartHilbertCoordinates))
            (E := CanonicalChartHilbertCoordinates)
            (finiteTangentPatchLocalizedC1c
              period hPeriod patch second)
    rw [finiteTangentPatchLocalizedC1c_add]
    exact
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
        (μ := (volume : Measure CanonicalChartHilbertCoordinates))
        (E := CanonicalChartHilbertCoordinates)).map_add _ _
  map_smul' scalar field := by
    apply Subtype.ext
    apply Subtype.ext
    change
      RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
          (μ := (volume : Measure CanonicalChartHilbertCoordinates))
          (E := CanonicalChartHilbertCoordinates)
          (finiteTangentPatchLocalizedC1c
            period hPeriod patch (scalar • field)) =
        scalar •
          RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
            (μ := (volume : Measure CanonicalChartHilbertCoordinates))
            (E := CanonicalChartHilbertCoordinates)
            (finiteTangentPatchLocalizedC1c
              period hPeriod patch field)
    rw [finiteTangentPatchLocalizedC1c_smul]
    exact
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.graph
        (μ := (volume : Measure CanonicalChartHilbertCoordinates))
        (E := CanonicalChartHilbertCoordinates)).map_smul scalar _

/-- Bounded return map from one Euclidean atlas `L²` space to global
physical bulk `L²`. -/
def finiteTangentPatchEuclideanL2ToPhysicalBulkL2
    (patch : Patch period hPeriod) :
    FiniteAtlasEuclideanL2 →L[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  (finiteTangentPatchSourceToQuotientL2
    period hPeriod patch).comp
    (finiteTangentPatchAmbientToSourceLp
      (Fiber := Real) period hPeriod patch
      (finiteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch))

theorem finiteAtlasEuclideanRellichEmbedding_localized
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    finiteAtlasEuclideanRellichEmbedding period hPeriod
        (finiteTangentPatchSmoothEuclideanH1
          period hPeriod patch field) =
      finiteTangentPatchLocalizedValueL2
        period hPeriod patch field :=
  rfl

theorem finiteTangentPatchEuclideanL2ToPhysicalBulkL2_localized
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    finiteTangentPatchEuclideanL2ToPhysicalBulkL2
        period hPeriod patch
        (finiteAtlasEuclideanRellichEmbedding period hPeriod
          (finiteTangentPatchSmoothEuclideanH1
            period hPeriod patch field)) =
      finiteTangentPatchWeightedBulkL2
        period hPeriod patch field := by
  rw [finiteAtlasEuclideanRellichEmbedding_localized
      period hPeriod patch field]
  exact
    finiteTangentPatchLocalizedValueExtension_eq
      period hPeriod patch
      (finiteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch) field

/-- The finite partition-weighted physical `L²` fields reconstruct the
original smooth scalar exactly. -/
theorem finiteTangentPatchWeightedBulkL2_sum_eq
    (field : SmoothQuotientField period hPeriod Real) :
    (∑ patch : Patch period hPeriod,
      finiteTangentPatchWeightedBulkL2
        period hPeriod patch field) =
      smoothToCanonicalPhysicalBulkL2
        period hPeriod field := by
  apply Lp.ext
  letI :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  have hSum :=
    Lp.coeFn_fun_finsetSum
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (Finset.univ : Finset (Patch period hPeriod))
      (fun patch =>
        finiteTangentPatchWeightedBulkL2
          period hPeriod patch field)
  have hWeighted :
      ∀ᵐ point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod,
        ∀ patch : Patch period hPeriod,
          finiteTangentPatchWeightedBulkL2
              period hPeriod patch field point =
            finiteTangentGeneratorWeight
              period hPeriod patch point * field point :=
    ae_all_iff.2 fun patch =>
      finiteTangentPatchWeightedBulkL2_coeFn_ae_eq
        period hPeriod patch field
  have hOriginal :
      (smoothToCanonicalPhysicalBulkL2 period hPeriod field :
        EffectiveQuotient period hPeriod → Real) =ᵐ[
          intrinsicCanonicalLorentzVolumeMeasure period hPeriod]
        field :=
    smoothFieldToL2_ae period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field
  filter_upwards [hSum, hWeighted, hOriginal]
    with point hSum hWeighted hOriginal
  rw [hSum, hOriginal]
  simp_rw [hWeighted]
  calc
    (∑ patch : Patch period hPeriod,
        finiteTangentGeneratorWeight period hPeriod patch point *
          field point) =
      (∑ patch : Patch period hPeriod,
        finiteTangentGeneratorWeight period hPeriod patch point) *
          field point := by
      rw [Finset.sum_mul]
    _ = field point := by
      rw [finiteTangentGeneratorWeight_sum_eq_one]
      exact one_mul _

/-- Fully geometric smooth transport package: local Euclidean Rellich,
canonical/Lebesgue comparison, bounded localization, and exact partition
reconstruction are all discharged without additional assumptions. -/
def canonicalPhysicalScalarSmoothEuclideanRellichTransportData :
    CanonicalPhysicalScalarSmoothEuclideanRellichTransportData
      period hPeriod where
  localizeCore :=
    finiteTangentPatchSmoothEuclideanH1LinearMap period hPeriod
  localizeBound :=
    exists_finiteTangentPatchSmoothEuclideanH1_bound
      period hPeriod
  extend :=
    finiteTangentPatchEuclideanL2ToPhysicalBulkL2 period hPeriod
  factorizationCore := by
    intro field
    rw [canonicalPhysicalScalarH1ToBulkL2_agrees_on_smooth]
    calc
      smoothToCanonicalPhysicalBulkL2 period hPeriod field =
          ∑ patch : Patch period hPeriod,
            finiteTangentPatchWeightedBulkL2
              period hPeriod patch field :=
        (finiteTangentPatchWeightedBulkL2_sum_eq
          period hPeriod field).symm
      _ =
          ∑ patch : Patch period hPeriod,
            finiteTangentPatchEuclideanL2ToPhysicalBulkL2
              period hPeriod patch
              (finiteAtlasEuclideanRellichEmbedding period hPeriod
                (finiteTangentPatchSmoothEuclideanH1LinearMap
                  period hPeriod patch field)) := by
        apply Finset.sum_congr rfl
        intro patch _
        exact
          (finiteTangentPatchEuclideanL2ToPhysicalBulkL2_localized
            period hPeriod patch field).symm

/-- Unconditional physical `H¹ → L²` Rellich compactness on the canonical
Janus quotient. -/
theorem canonicalPhysicalScalarRellich :
    PhysicalH1RellichCompactness period hPeriod :=
  (canonicalPhysicalScalarSmoothEuclideanRellichTransportData
    period hPeriod).rellich period hPeriod

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothRellichTransport4D
end JanusFormal
