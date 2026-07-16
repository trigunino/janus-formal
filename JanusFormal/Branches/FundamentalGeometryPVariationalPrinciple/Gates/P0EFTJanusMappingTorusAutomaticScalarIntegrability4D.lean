import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D

/-!
# Automatic integrability for the fixed-frame scalar action

The existing holonomic action evaluates `mfderiv` on four constant model
vectors.  Those vectors are not asserted to be a global smooth tangent frame,
so smoothness of the scalar alone does not imply continuity of these four
coordinate components.  This gate isolates exactly that residual regularity.

Once the four components are continuous, every scalar density and weak
first-variation density is continuous on the compact effective quotient.
Consequently all action and variation integrability contracts are automatic
for every finite Borel measure.  Constant scalars give an unconditional,
nonzero-field family; no zero-measure witness is used.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAutomaticScalarIntegrability4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalHolonomicScalar4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D

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

/-- A smooth scalar whose four components in the action's fixed model frame
are continuous.  This is the exact residual hypothesis caused by that frame;
it is not a claim of intrinsic covariance. -/
structure FixedFrameRegularScalar where
  field : SmoothQuotientField period hPeriod Real
  component_continuous : ∀ index : Fin 4,
    Continuous (fun point =>
      holonomicCovectorComponent period hPeriod field point index)

/-- The regular class is stable under the exact affine curves used by the
existing scalar-variation gate. -/
def fixedFrameRegularAffineCurve
    (field variation : FixedFrameRegularScalar period hPeriod)
    (epsilon : Real) : FixedFrameRegularScalar period hPeriod where
  field := scalarAffineCurve period hPeriod field.field variation.field epsilon
  component_continuous := by
    intro index
    rw [show (fun point => holonomicCovectorComponent period hPeriod
        (scalarAffineCurve period hPeriod field.field variation.field epsilon)
          point index) =
        fun point => holonomicCovectorComponent period hPeriod field.field point index +
          epsilon * holonomicCovectorComponent period hPeriod variation.field point index
      from by
        funext point
        exact holonomicCovectorComponent_affine period hPeriod field.field
          variation.field epsilon point index]
    exact (field.component_continuous index).add
      (continuous_const.mul (variation.component_continuous index))

private theorem smoothMagnitudeComponent_continuous
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (index : Fin 4) :
    Continuous (fun point => magnitude point index) := by
  exact (continuous_apply index).comp magnitude.contMDiff_toFun.continuous

/-- The determinant volume density is continuous for every smooth diagonal
magnitude field. -/
theorem diagonalMetricVolumeDensity_continuous
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real)) :
    Continuous (diagonalMetricVolumeDensity period hPeriod magnitude) := by
  unfold diagonalMetricVolumeDensity
  apply Real.continuous_sqrt.comp
  exact continuous_finsetProd _ fun index _ =>
    smoothMagnitudeComponent_continuous period hPeriod magnitude index

/-- Under positive diagonal magnitudes and the exact fixed-frame regularity
condition, the existing scalar density is continuous on the true quotient. -/
theorem globalHolonomicScalarDensity_continuous
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (hPositive : ∀ point index, 0 < magnitude point index)
    (scalar : FixedFrameRegularScalar period hPeriod) :
    Continuous (globalHolonomicScalarDensity period hPeriod massSquared
      magnitude scalar.field) := by
  unfold globalHolonomicScalarDensity diagonalHolonomicKineticDensity
  apply (diagonalMetricVolumeDensity_continuous period hPeriod magnitude).mul
  apply Continuous.add
  · apply (continuous_const.mul (continuous_finsetSum _ fun index _ => ?_))
    exact ((continuous_const.div
      (smoothMagnitudeComponent_continuous period hPeriod magnitude index)
      (fun point => ne_of_gt (hPositive point index))).mul
        ((scalar.component_continuous index).pow 2))
  · exact continuous_const.mul (scalar.field.contMDiff_toFun.continuous.pow 2)

/-- The action integrability contract is automatic for every finite Borel
measure; no density-specific domination hypothesis remains. -/
theorem globalHolonomicScalarDensity_integrable
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (hPositive : ∀ point index, 0 < magnitude point index)
    (scalar : FixedFrameRegularScalar period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    Integrable (globalHolonomicScalarDensity period hPeriod massSquared
      magnitude scalar.field) measure := by
  exact (globalHolonomicScalarDensity_continuous period hPeriod massSquared
    magnitude hPositive scalar).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace
        (globalHolonomicScalarDensity period hPeriod massSquared
          magnitude scalar.field))

/-- Constructor connecting the automatic theorem directly to the existing
global scalar-sector structure and its unchanged action. -/
def finiteMeasureGlobalHolonomicScalarSector
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (hPositive : ∀ point index, 0 < magnitude point index)
    (scalar : FixedFrameRegularScalar period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    GlobalHolonomicScalarSector period hPeriod massSquared where
  magnitude := magnitude
  magnitude_pos := hPositive
  scalar := scalar.field
  measure := measure
  density_integrable := globalHolonomicScalarDensity_integrable period hPeriod
    massSquared magnitude hPositive scalar measure

/-- The weak first-variation density is continuous for two fixed-frame
regular scalars coupled to the same smooth positive metric. -/
theorem globalHolonomicScalarFirstVariationDensity_continuous
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (hPositive : ∀ point index, 0 < magnitude point index)
    (field variation : FixedFrameRegularScalar period hPeriod) :
    Continuous (globalHolonomicScalarFirstVariationDensity period hPeriod
      massSquared magnitude field.field variation.field) := by
  unfold globalHolonomicScalarFirstVariationDensity
  apply (diagonalMetricVolumeDensity_continuous period hPeriod magnitude).mul
  apply Continuous.add
  · apply continuous_finsetSum
    intro index _
    exact (((continuous_const.div
      (smoothMagnitudeComponent_continuous period hPeriod magnitude index)
      (fun point => ne_of_gt (hPositive point index))).mul
        (field.component_continuous index)).mul
          (variation.component_continuous index))
  · exact ((continuous_const.mul field.field.contMDiff_toFun.continuous).mul
      variation.field.contMDiff_toFun.continuous)

/-- All three hypotheses of the existing integrated variation theorem are
automatic for finite measures and fixed-frame regular smooth fields. -/
def finiteMeasureGlobalScalarVariationContract
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (hPositive : ∀ point index, 0 < magnitude point index)
    (field variation : FixedFrameRegularScalar period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    GlobalScalarVariationContract period hPeriod massSquared magnitude
      field.field variation.field measure where
  base_integrable := globalHolonomicScalarDensity_integrable period hPeriod
    massSquared magnitude hPositive field measure
  first_integrable :=
    (globalHolonomicScalarFirstVariationDensity_continuous period hPeriod
      massSquared magnitude hPositive field variation).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace
          (globalHolonomicScalarFirstVariationDensity period hPeriod massSquared
            magnitude field.field variation.field))
  quadratic_integrable := globalHolonomicScalarDensity_integrable period hPeriod
    massSquared magnitude hPositive variation measure

/-- The derivative of the actual integrated action now needs no separately
supplied integrability contract on this regular class. -/
theorem finiteMeasureGlobalHolonomicScalarAction_affine_hasDerivAt
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (hPositive : ∀ point index, 0 < magnitude point index)
    (field variation : FixedFrameRegularScalar period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    HasDerivAt
      (fun epsilon : Real =>
        globalHolonomicScalarAction period hPeriod massSquared magnitude
          (scalarAffineCurve period hPeriod field.field variation.field epsilon)
          measure)
      (globalHolonomicScalarFirstVariation period hPeriod massSquared magnitude
        field.field variation.field measure) 0 :=
  globalHolonomicScalarAction_affine_hasDerivAt period hPeriod massSquared
    magnitude field.field variation.field measure
      (finiteMeasureGlobalScalarVariationContract period hPeriod massSquared
        magnitude hPositive field variation measure)

/-- Constant scalars satisfy the residual fixed-frame regularity without any
extra analytic input.  The value is arbitrary and may be nonzero. -/
def constantFixedFrameRegularScalar (value : Real) :
    FixedFrameRegularScalar period hPeriod where
  field := constantSmoothField period hPeriod Real value
  component_continuous := by
    intro index
    have hZero : (fun _ : EffectiveQuotient period hPeriod => (0 : Real)) =
        fun point => holonomicCovectorComponent period hPeriod
          (constantSmoothField period hPeriod Real value) point index := by
      funext point
      simp only [holonomicCovectorComponent, scalarDifferential,
        constantSmoothField, mfderiv_const]
      change (0 : Real) = 0
      rfl
    rw [← hZero]
    exact continuous_const

private def unitMagnitude : Fin 4 → Real := fun _ => 1

/-- A positive flat magnitude coupled to any (including nonzero) constant
scalar and any finite Borel measure. -/
def finiteMeasureConstantScalarSector
    (massSquared value : Real)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    GlobalHolonomicScalarSector period hPeriod massSquared :=
  finiteMeasureGlobalHolonomicScalarSector period hPeriod massSquared
    (constantSmoothField period hPeriod (Fin 4 → Real) unitMagnitude)
    (by intro point index; simp [constantSmoothField, unitMagnitude])
    (constantFixedFrameRegularScalar period hPeriod value) measure

/-- Thus nonzero smooth scalar fields are covered for arbitrary finite
measures, not merely by the earlier zero-field/zero-measure witness. -/
theorem finiteMeasureConstantScalarSector_scalar
    (massSquared value : Real)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : EffectiveQuotient period hPeriod) :
    (finiteMeasureConstantScalarSector period hPeriod massSquared value measure).scalar
        point = value := by
  rfl

end

end P0EFTJanusMappingTorusAutomaticScalarIntegrability4D
end JanusFormal
