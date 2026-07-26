import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConcreteFullActionFrechetBridge4D

/-!
# Concrete linewise C² closure of the Einstein--Maxwell slots

The regular metric-line API makes the Einstein--Hilbert volume and scalar
curvature, and the Maxwell pairing, pointwise smooth in the line parameter.
This proves pointwise `C²` densities without an extra contract.  Consequently
the four genuine integrated blocks are `C²` for a nonzero one-atom measure,
and hence close the four Einstein--Maxwell fields occurring in
`FullMetricLineMissingC2Slots` on that concrete sector.

For a general finite measure the current structures provide only separate
pointwise smoothness and a first-derivative domination contract at zero.  They
do not provide joint parameter--point `C²` control or domination of the first
two derivatives, so no general-measure `C²` statement is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusConcreteEinsteinMaxwellLineC2Closure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinMaxwellMetricVariation4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFiniteBVAction4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFullMetricFiniteBVAction4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPConcreteFullActionFrechetBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance localRealNormedAddCommGroup : NormedAddCommGroup Real :=
  inferInstance

local instance localRealNormedSpace : NormedSpace Real Real :=
  inferInstance

local instance localRealAddCommGroup : AddCommGroup Real :=
  localRealNormedAddCommGroup.toAddCommGroup

local instance (priority := 10000) localRealModule : Module Real Real :=
  localRealNormedSpace.toModule

private theorem two_le_infty : (2 : ℕ∞ω) ≤ ∞ := by
  exact WithTop.coe_le_coe.mpr le_top

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-! ## Unconditional pointwise C² closure -/

theorem einsteinHilbertMetricLine_density_contDiff_two
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    ContDiff Real 2
      (fun parameter =>
        regularEinsteinHilbertDensityField period hPeriod couplings
          (line.data parameter) point) := by
  change ContDiff Real 2
    (fun parameter =>
      (line.data parameter).metric.volume point *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          ((line.data parameter).scalarCurvature point -
            2 * couplings.cosmologicalConstant)))
  exact
    ((line.volume_contDiff point).of_le
      two_le_infty).mul
      (contDiff_const.mul
        (((line.scalarCurvature_contDiff point).of_le
          two_le_infty).sub
          contDiff_const))

theorem maxwellMetricGaugeLine_density_contDiff_two
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (point : EffectiveQuotient period hPeriod) :
    ContDiff Real 2
      (fun parameter =>
        (gravity.data parameter).metric.volume point *
          (-(1 / 4 : Real) * line.pairing parameter point)) := by
  exact
    ((gravity.volume_contDiff point).of_le
      two_le_infty).mul
      (contDiff_const.mul
        ((line.pairing_contDiff point).of_le
          two_le_infty))

/-! ## Exact nonzero one-atom integrated sector -/

theorem einsteinHilbertMetricActionCurve_dirac_contDiff_two
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    ContDiff Real 2
      (intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings line
        (Measure.dirac point)) := by
  rw [show
      intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings line
          (Measure.dirac point) =
        fun parameter =>
          regularEinsteinHilbertDensityField period hPeriod couplings
            (line.data parameter) point by
    funext parameter
    simp [intrinsicEinsteinHilbertMetricActionCurve,
      intrinsicEinsteinHilbertAction]]
  exact einsteinHilbertMetricLine_density_contDiff_two period hPeriod
    couplings line point

theorem maxwellMetricGaugeActionCurve_dirac_contDiff_two
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (point : EffectiveQuotient period hPeriod) :
    ContDiff Real 2
      (intrinsicMaxwellMetricGaugeActionCurve period hPeriod gravity line
        (Measure.dirac point)) := by
  rw [show
      intrinsicMaxwellMetricGaugeActionCurve period hPeriod gravity line
          (Measure.dirac point) =
        fun parameter =>
          (gravity.data parameter).metric.volume point *
            (-(1 / 4 : Real) * line.pairing parameter point) by
    funext parameter
    simp [intrinsicMaxwellMetricGaugeActionCurve, intrinsicMaxwellAction]]
  exact maxwellMetricGaugeLine_density_contDiff_two period hPeriod gravity line
    point

/-- The exact four-field subrecord of `FullMetricLineMissingC2Slots`. -/
structure EinsteinMaxwellLineC2Slots
    (blocks : FullCoupledActionBlocks Real) : Prop where
  einsteinHilbertPlus :
    ContDiff Real 2 blocks.einsteinHilbertPlus
  einsteinHilbertMinus :
    ContDiff Real 2 blocks.einsteinHilbertMinus
  maxwellPlus :
    ContDiff Real 2 blocks.maxwellPlus
  maxwellMinus :
    ContDiff Real 2 blocks.maxwellMinus

/-- All four genuine Einstein--Maxwell slots of the concrete full-metric line
are `C²` when the common candidate measure is a nonzero Dirac measure. -/
theorem fullMetricFiniteBVLineBlocks_dirac_einsteinMaxwell_c2
    (point : EffectiveQuotient period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields (Measure.dirac point))
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (junction : SmoothThroatField period hPeriod Real)
    (bvField : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    (direction :
      CandidateAEinsteinMaxwellFullMetricFiniteBVVariation period hPeriod
        fields completion) :
    EinsteinMaxwellLineC2Slots
      (fullMetricFiniteBVLineBlocks period hPeriod (Measure.dirac point)
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction) where
  einsteinHilbertPlus := by
    change ContDiff Real 2
      (intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings
        direction.plusGravityLine (Measure.dirac point))
    exact einsteinHilbertMetricActionCurve_dirac_contDiff_two period hPeriod
      couplings direction.plusGravityLine point
  einsteinHilbertMinus := by
    change ContDiff Real 2
      (intrinsicEinsteinHilbertMetricActionCurve period hPeriod couplings
        direction.minusGravityLine (Measure.dirac point))
    exact einsteinHilbertMetricActionCurve_dirac_contDiff_two period hPeriod
      couplings direction.minusGravityLine point
  maxwellPlus := by
    change ContDiff Real 2
      (intrinsicMaxwellMetricGaugeActionCurve period hPeriod
        direction.plusGravityLine direction.plusMaxwellLine
        (Measure.dirac point))
    exact maxwellMetricGaugeActionCurve_dirac_contDiff_two period hPeriod
      direction.plusGravityLine direction.plusMaxwellLine point
  maxwellMinus := by
    change ContDiff Real 2
      (intrinsicMaxwellMetricGaugeActionCurve period hPeriod
        direction.minusGravityLine direction.minusMaxwellLine
        (Measure.dirac point))
    exact maxwellMetricGaugeActionCurve_dirac_contDiff_two period hPeriod
      direction.minusGravityLine direction.minusMaxwellLine point

end

end P0EFTJanusMappingTorusConcreteEinsteinMaxwellLineC2Closure4D
end JanusFormal
