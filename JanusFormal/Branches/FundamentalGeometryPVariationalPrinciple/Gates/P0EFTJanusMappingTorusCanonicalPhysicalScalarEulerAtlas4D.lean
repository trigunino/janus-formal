import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

/-!
# Concrete physical scalar Euler operator on the canonical total atlas

The quotient already carries a field-independent total holonomic atlas and the
intrinsic smooth Lorentz metric.  This file fixes those two concrete objects and
defines the physical scalar Euler/Jacobi residual in every chart by

`box_g phi - m² phi`.

The local residual is smooth and its vanishing is exactly the existing
canonical-atlas Euler equation, hence implies chartwise and quotient-pointwise
stress conservation.

To obtain one global scalar function, the only remaining geometric theorem is
overlap compatibility of these local scalar representatives.  A compatible
family is globalized by the total-atlas choice.  Adding continuity and the
obvious linearity laws then produces a genuine smooth-core-to-bulk-L2 linear
operator.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
open P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
open P0EFTJanusMappingTorusFrameFreeIntrinsicScalarAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- Family of scalar coordinate representatives, one for every genuine patch of
the canonical total atlas. -/
abbrev CanonicalPhysicalScalarEulerAtlasTarget :=
  (patch : SmoothHolonomicFrameChart4 period hPeriod) → Vector4 → Real

/-- Concrete physical scalar Euler residual on the canonical total atlas. -/
def canonicalPhysicalScalarEulerAtlasResidual
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod) :
    CanonicalPhysicalScalarEulerAtlasTarget period hPeriod :=
  fun patch coordinate =>
    localSmoothScalarEulerResidual period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch field massSquared 0 coordinate

/-- Expanded physical formula `box_g phi - m² phi`. -/
theorem canonicalPhysicalScalarEulerAtlasResidual_eq_wave_sub_mass
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    canonicalPhysicalScalarEulerAtlasResidual period hPeriod massSquared field
        patch coordinate =
      covariantScalarJetWave
          (localFixedSignMetric period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch field coordinate) -
        massSquared * localScalarRepresentative
          period hPeriod field patch coordinate := by
  unfold canonicalPhysicalScalarEulerAtlasResidual
    localSmoothScalarEulerResidual covariantScalarStressEulerResidual
    pointwiseScalarPotentialSlope
  ring

/-- Every local physical Euler representative is smooth. -/
theorem canonicalPhysicalScalarEulerAtlasResidual_contDiff
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (canonicalPhysicalScalarEulerAtlasResidual
        period hPeriod massSquared field patch) :=
  localSmoothScalarEulerResidual_contDiff period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
    patch field massSquared 0

/-- Concrete physical scalar Euler equation on every chart of the total atlas. -/
def CanonicalPhysicalScalarEulerEquation
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod) : Prop :=
  ∀ patch : SmoothHolonomicFrameChart4 period hPeriod,
    ∀ coordinate : Vector4,
      canonicalPhysicalScalarEulerAtlasResidual
        period hPeriod massSquared field patch coordinate = 0

/-- The concrete equation is exactly the previously installed canonical-atlas
Euler equation with zero external source. -/
theorem canonicalPhysicalScalarEulerEquation_iff_atlas
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod) :
    CanonicalPhysicalScalarEulerEquation period hPeriod massSquared field ↔
      HolonomicAtlasLocalScalarEulerEquations period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        field (canonicalTotalHolonomicAtlasCover period hPeriod)
        massSquared 0 := by
  constructor
  · intro hEuler patch _hPatch coordinate
    exact hEuler patch coordinate
  · intro hEuler patch coordinate
    exact hEuler patch (canonicalTotalHolonomicAtlasCover_patch_mem
      period hPeriod patch) coordinate

/-- The concrete physical scalar Euler equation implies stress conservation in
all selected coordinates. -/
theorem canonicalPhysicalScalarStressConserved_of_euler
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (hEuler : CanonicalPhysicalScalarEulerEquation
      period hPeriod massSquared field) :
    HolonomicAtlasLocalScalarStressConserved period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      field (canonicalTotalHolonomicAtlasCover period hPeriod)
      massSquared 0 :=
  canonicalTotalHolonomicAtlas_localScalarStressConserved_of_euler
    period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
    field massSquared 0
    ((canonicalPhysicalScalarEulerEquation_iff_atlas
      period hPeriod massSquared field).1 hEuler)

/-- The same equation gives a zero stress-divergence representative through
every quotient point. -/
theorem canonicalPhysicalScalarPointwiseStressConserved_of_euler
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (hEuler : CanonicalPhysicalScalarEulerEquation
      period hPeriod massSquared field) :
    QuotientPointwiseLocalScalarStressConserved period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      field (canonicalTotalHolonomicAtlasCover period hPeriod)
      massSquared 0 :=
  canonicalTotalHolonomicAtlas_quotientPointwiseScalarStressConserved_of_euler
    period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
    field massSquared 0
    ((canonicalPhysicalScalarEulerEquation_iff_atlas
      period hPeriod massSquared field).1 hEuler)

/-- A concrete total-atlas chart witness through one quotient point. -/
structure CanonicalPhysicalScalarEulerChartWitness
    (point : EffectiveQuotient period hPeriod) where
  patch : SmoothHolonomicFrameChart4 period hPeriod
  coordinate : Vector4
  coordinate_eq : patch.coordinateMap coordinate = point

/-- The canonical total atlas supplies a chart witness at every point. -/
noncomputable def canonicalPhysicalScalarEulerChartWitness
    (point : EffectiveQuotient period hPeriod) :
    CanonicalPhysicalScalarEulerChartWitness period hPeriod point := by
  classical
  let hCover := canonicalTotalHolonomicAtlasCover_covers period hPeriod point
  let patch := hCover.choose
  have hPatchData := hCover.choose_spec
  let coordinate := hPatchData.2.choose
  exact ⟨patch, coordinate, hPatchData.2.choose_spec⟩

/-- Exact overlap-compatibility proposition for the physical scalar residual. -/
def CanonicalPhysicalScalarEulerAtlasCompatible
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod) : Prop :=
  ∀ (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4),
    firstPatch.coordinateMap firstCoordinate =
        secondPatch.coordinateMap secondCoordinate →
      canonicalPhysicalScalarEulerAtlasResidual
          period hPeriod massSquared field firstPatch firstCoordinate =
        canonicalPhysicalScalarEulerAtlasResidual
          period hPeriod massSquared field secondPatch secondCoordinate

/-- Pointwise global residual selected from the total atlas. -/
noncomputable def canonicalPhysicalScalarEulerGlobalResidual
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  let witness := canonicalPhysicalScalarEulerChartWitness
    period hPeriod point
  canonicalPhysicalScalarEulerAtlasResidual
    period hPeriod massSquared field witness.patch witness.coordinate

/-- A compatible atlas family evaluates to the global residual in every chart. -/
theorem canonicalPhysicalScalarEulerGlobalResidual_eq_chart
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (hCompatible : CanonicalPhysicalScalarEulerAtlasCompatible
      period hPeriod massSquared field)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field (patch.coordinateMap coordinate) =
      canonicalPhysicalScalarEulerAtlasResidual
        period hPeriod massSquared field patch coordinate := by
  unfold canonicalPhysicalScalarEulerGlobalResidual
  let witness := canonicalPhysicalScalarEulerChartWitness
    period hPeriod (patch.coordinateMap coordinate)
  exact hCompatible witness.patch patch witness.coordinate coordinate
    witness.coordinate_eq

/-- Under overlap compatibility, the atlas equation is equivalent to vanishing
of the selected global residual. -/
theorem canonicalPhysicalScalarEulerEquation_iff_global
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (hCompatible : CanonicalPhysicalScalarEulerAtlasCompatible
      period hPeriod massSquared field) :
    CanonicalPhysicalScalarEulerEquation period hPeriod massSquared field ↔
      canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field = 0 := by
  constructor
  · intro hEuler
    funext point
    unfold canonicalPhysicalScalarEulerGlobalResidual
    exact hEuler _ _
  · intro hGlobal patch coordinate
    have hAt := congrFun hGlobal (patch.coordinateMap coordinate)
    rw [canonicalPhysicalScalarEulerGlobalResidual_eq_chart
      period hPeriod massSquared field hCompatible patch coordinate] at hAt
    exact hAt

/-- The precise globalization/linearity package required for a genuine bulk-L2
Euler operator.  Compatibility is geometric; continuity and linearity are the
remaining analytic consequences to prove from transition maps. -/
structure CanonicalPhysicalScalarEulerGlobalOperatorData
    (massSquared : Real) where
  compatible : ∀ field : SmoothScalarField period hPeriod,
    CanonicalPhysicalScalarEulerAtlasCompatible
      period hPeriod massSquared field
  continuous : ∀ field : SmoothScalarField period hPeriod,
    Continuous (canonicalPhysicalScalarEulerGlobalResidual
      period hPeriod massSquared field)
  ae_zero_eq_zero : ∀ field : SmoothScalarField period hPeriod,
    canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field =ᵐ[
          intrinsicCanonicalLorentzVolumeMeasure period hPeriod] 0 →
      canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field = 0
  map_add : ∀ first second : SmoothScalarField period hPeriod,
    canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared (first + second) =
      canonicalPhysicalScalarEulerGlobalResidual
          period hPeriod massSquared first +
        canonicalPhysicalScalarEulerGlobalResidual
          period hPeriod massSquared second
  map_smul : ∀ (scalar : Real)
    (field : SmoothScalarField period hPeriod),
    canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared (scalar • field) =
      scalar • canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field

namespace CanonicalPhysicalScalarEulerGlobalOperatorData

variable {period : Real} {hPeriod : period ≠ 0} {massSquared : Real}

/-- The global residual is L2 for the canonical physical bulk measure. -/
theorem residual_memLp
    (operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared)
    (field : SmoothScalarField period hPeriod) :
    MemLp (canonicalPhysicalScalarEulerGlobalResidual
      period hPeriod massSquared field)
      (2 : ENNReal)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (operatorData.continuous field).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Genuine smooth-core-to-physical-bulk-L2 scalar Euler operator. -/
def toBulkL2LinearMap
    (operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared) :
    SmoothScalarField period hPeriod →ₗ[Real]
      CanonicalPhysicalBulkL2 period hPeriod where
  toFun field :=
    (operatorData.residual_memLp field).toLp
      (canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field)
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [(operatorData.residual_memLp (first + second)).coeFn_toLp,
       (operatorData.residual_memLp first).coeFn_toLp,
       (operatorData.residual_memLp second).coeFn_toLp,
       Lp.coeFn_add
        ((operatorData.residual_memLp first).toLp
          (canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared first))
        ((operatorData.residual_memLp second).toLp
          (canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared second))]
      with point hSum hFirst hSecond hAdd
    rw [hSum, hAdd]
    change canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared (first + second) point =
      ((operatorData.residual_memLp first).toLp
          (canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared first) :
        EffectiveQuotient period hPeriod → Real) point +
      ((operatorData.residual_memLp second).toLp
          (canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared second) :
        EffectiveQuotient period hPeriod → Real) point
    rw [hFirst, hSecond]
    exact congrFun (operatorData.map_add first second) point
  map_smul' scalar field := by
    apply Lp.ext
    filter_upwards
      [(operatorData.residual_memLp (scalar • field)).coeFn_toLp,
       (operatorData.residual_memLp field).coeFn_toLp,
       Lp.coeFn_smul scalar
        ((operatorData.residual_memLp field).toLp
          (canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared field))]
      with point hScaled hField hSmul
    rw [hScaled]
    change canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared (scalar • field) point =
      ((scalar • (operatorData.residual_memLp field).toLp
        (canonicalPhysicalScalarEulerGlobalResidual
          period hPeriod massSquared field)) :
          CanonicalPhysicalBulkL2 period hPeriod) point
    rw [hSmul]
    change canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared (scalar • field) point =
      scalar • ((operatorData.residual_memLp field).toLp
        (canonicalPhysicalScalarEulerGlobalResidual
          period hPeriod massSquared field) :
          EffectiveQuotient period hPeriod → Real) point
    rw [hField]
    exact congrFun (operatorData.map_smul scalar field) point

/-- The L2 Euler operator agrees almost everywhere with the selected global
residual. -/
theorem toBulkL2LinearMap_ae
    (operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared)
    (field : SmoothScalarField period hPeriod) :
    (operatorData.toBulkL2LinearMap field :
      EffectiveQuotient period hPeriod → Real) =ᵐ[
        intrinsicCanonicalLorentzVolumeMeasure period hPeriod]
      canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field :=
  (operatorData.residual_memLp field).coeFn_toLp

/-- The physical Euler equation is exactly zero of the bulk-L2 operator. -/
theorem eulerEquation_iff_operator_eq_zero
    (operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared)
    (field : SmoothScalarField period hPeriod) :
    CanonicalPhysicalScalarEulerEquation period hPeriod massSquared field ↔
      operatorData.toBulkL2LinearMap field = 0 := by
  rw [canonicalPhysicalScalarEulerEquation_iff_global
    period hPeriod massSquared field (operatorData.compatible field)]
  constructor
  · intro hResidual
    apply Lp.ext
    filter_upwards
      [operatorData.toBulkL2LinearMap_ae field,
       Lp.coeFn_zero Real (2 : ENNReal)
         (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)]
      with point hPoint hZero
    rw [hPoint, congrFun hResidual point, hZero]
  · intro hOperator
    funext point
    have hAe : canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field =ᵐ[
          intrinsicCanonicalLorentzVolumeMeasure period hPeriod] 0 := by
      have hMiddle :
          (operatorData.toBulkL2LinearMap field :
            EffectiveQuotient period hPeriod → Real) =ᵐ[
              intrinsicCanonicalLorentzVolumeMeasure period hPeriod]
            (0 : CanonicalPhysicalBulkL2 period hPeriod) := by
        rw [hOperator]
      exact (operatorData.toBulkL2LinearMap_ae field).symm.trans
        (hMiddle.trans (Lp.coeFn_zero Real (2 : ENNReal)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)))
    have hFunctions := operatorData.ae_zero_eq_zero field hAe
    exact congrFun hFunctions point

end CanonicalPhysicalScalarEulerGlobalOperatorData

/-- Concrete physical Euler-atlas certificate. -/
theorem canonicalPhysicalScalarEulerAtlas_certificate
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod) :
    (∀ patch,
      ContDiff Real ∞
        (canonicalPhysicalScalarEulerAtlasResidual
          period hPeriod massSquared field patch)) ∧
      (CanonicalPhysicalScalarEulerEquation
          period hPeriod massSquared field →
        HolonomicAtlasLocalScalarStressConserved period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          field (canonicalTotalHolonomicAtlasCover period hPeriod)
          massSquared 0) ∧
      (CanonicalPhysicalScalarEulerEquation
          period hPeriod massSquared field →
        QuotientPointwiseLocalScalarStressConserved period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          field (canonicalTotalHolonomicAtlasCover period hPeriod)
          massSquared 0) :=
  ⟨canonicalPhysicalScalarEulerAtlasResidual_contDiff
      period hPeriod massSquared field,
    canonicalPhysicalScalarStressConserved_of_euler
      period hPeriod massSquared field,
    canonicalPhysicalScalarPointwiseStressConserved_of_euler
      period hPeriod massSquared field⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
end JanusFormal
