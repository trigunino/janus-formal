import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalPalatiniBoxStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D

/-! # Local box Stokes theorem for the smooth Maxwell boundary current -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwellLocalBoxStokes4D

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
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusMappingTorusLocalPalatiniBoxStokes4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D

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

/-- The coordinate Maxwell integration-by-parts current for one gauge
component. -/
def regularIntrinsicMaxwellLocalBoundaryCurrent
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) : Vector4 → Vector4 :=
  fun coordinate first =>
    maxwellBoundaryCurrent
      (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
        potential patch component)
      (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
        variation component patch)
      coordinate first

/-- The actual local Maxwell boundary current is smooth. -/
theorem regularIntrinsicMaxwellLocalBoundaryCurrent_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric
        potential variation component patch) := by
  rw [contDiff_pi]
  intro first
  unfold regularIntrinsicMaxwellLocalBoundaryCurrent maxwellBoundaryCurrent
  apply ContDiff.sum
  intro second _
  exact
    (regularIntrinsicMaxwellLocalExcitationField_entry_contDiff period hPeriod
      metric potential component patch first second).mul
      (regularIntrinsicMaxwellLocalPotentialCoordinates_entry_contDiff period
        hPeriod variation component patch second)

/-- Ordinary coordinate divergence of the actual Maxwell boundary current. -/
def regularIntrinsicMaxwellLocalBoundaryDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ first : Index4,
    fderiv Real
        (regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric
          potential variation component patch)
        coordinate (Pi.single first 1) first

/-- The analytic divergence is exactly the boundary-divergence term in the
local Maxwell integration-by-parts identity. -/
theorem regularIntrinsicMaxwellLocalBoundaryDivergence_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularIntrinsicMaxwellLocalBoundaryDivergence period hPeriod metric
        potential variation component patch coordinate =
      maxwellBoundaryDivergence
        (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
          potential patch component)
        (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
          variation component patch)
        coordinate := by
  unfold regularIntrinsicMaxwellLocalBoundaryDivergence
    maxwellBoundaryDivergence coordinatePartial
  apply Finset.sum_congr rfl
  intro first _
  have hCurrent : DifferentiableAt Real
      (regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric
        potential variation component patch) coordinate :=
    (regularIntrinsicMaxwellLocalBoundaryCurrent_contDiff period hPeriod metric
      potential variation component patch).differentiable (by simp) coordinate
  have hComponent := fderiv_apply hCurrent first
  have hApplied := congrArg
    (fun derivative : Vector4 →L[Real] Real =>
      derivative (Pi.single first 1)) hComponent
  simpa only [regularIntrinsicMaxwellLocalBoundaryCurrent,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using
      hApplied.symm

/-- The smooth Maxwell boundary divergence is integrable on every compact
coordinate box. -/
theorem regularIntrinsicMaxwellLocalBoundaryDivergence_integrableOn
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    IntegrableOn
      (regularIntrinsicMaxwellLocalBoundaryDivergence period hPeriod metric
        potential variation component patch) (Icc box.lower box.upper) := by
  have hCurrent :=
    regularIntrinsicMaxwellLocalBoundaryCurrent_contDiff period hPeriod metric
      potential variation component patch
  have hDerivative : Continuous (fun coordinate =>
      fderiv Real
        (regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric
          potential variation component patch) coordinate) :=
    hCurrent.continuous_fderiv (by simp)
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact Continuous.continuousOn (by
    unfold regularIntrinsicMaxwellLocalBoundaryDivergence
    fun_prop)

/-- Concrete Bochner Stokes theorem for the smooth Maxwell current on every
compact holonomic coordinate box. -/
theorem integral_regularIntrinsicMaxwellLocalBoundaryDivergence_eq_faces
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    (∫ coordinate in Icc box.lower box.upper,
      regularIntrinsicMaxwellLocalBoundaryDivergence period hPeriod metric
        potential variation component patch coordinate) =
      ∑ index : Index4,
        ((∫ face in
              Icc (box.lower ∘ index.succAbove)
                (box.upper ∘ index.succAbove),
            regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric
              potential variation component patch
                (index.insertNth (box.upper index) face) index) -
          ∫ face in
              Icc (box.lower ∘ index.succAbove)
                (box.upper ∘ index.succAbove),
            regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric
              potential variation component patch
                (index.insertNth (box.lower index) face) index) := by
  let current :=
    regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric potential
      variation component patch
  let derivative : Vector4 → Vector4 →L[Real] Vector4 :=
    fun coordinate => fderiv Real current coordinate
  have hCurrent : ContDiff Real ∞ current :=
    regularIntrinsicMaxwellLocalBoundaryCurrent_contDiff period hPeriod metric
      potential variation component patch
  have hStokes :=
    MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
      box.lower box.upper box.lower_le_upper current derivative ∅
      Set.countable_empty hCurrent.continuous.continuousOn
      (fun coordinate _ =>
        (hCurrent.differentiable (by simp) coordinate).hasFDerivAt)
      (regularIntrinsicMaxwellLocalBoundaryDivergence_integrableOn period
        hPeriod metric potential variation component patch box)
  simpa [current, derivative,
    regularIntrinsicMaxwellLocalBoundaryDivergence] using hStokes

/-- Dirichlet test data vanish on every front and back face of the coordinate
box. -/
structure RegularIntrinsicMaxwellLocalBoxDirichlet
    (variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) : Prop where
  front : ∀ (component : Fin 2) (index : Index4)
      (face : FaceCoordinate3),
    regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod variation
        component patch (index.insertNth (box.upper index) face) = 0
  back : ∀ (component : Fin 2) (index : Index4)
      (face : FaceCoordinate3),
    regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod variation
        component patch (index.insertNth (box.lower index) face) = 0

theorem regularIntrinsicMaxwellLocalBoundaryCurrent_front_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4)
    (boundary : RegularIntrinsicMaxwellLocalBoxDirichlet period hPeriod
      variation patch box)
    (component : Fin 2) (index : Index4) (face : FaceCoordinate3) :
    regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric potential
        variation component patch
          (index.insertNth (box.upper index) face) index = 0 := by
  exact maxwellBoundaryCurrent_eq_zero_of_dirichlet _ _ _ _
    (boundary.front component index face)

theorem regularIntrinsicMaxwellLocalBoundaryCurrent_back_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4)
    (boundary : RegularIntrinsicMaxwellLocalBoxDirichlet period hPeriod
      variation patch box)
    (component : Fin 2) (index : Index4) (face : FaceCoordinate3) :
    regularIntrinsicMaxwellLocalBoundaryCurrent period hPeriod metric potential
        variation component patch
          (index.insertNth (box.lower index) face) index = 0 := by
  exact maxwellBoundaryCurrent_eq_zero_of_dirichlet _ _ _ _
    (boundary.back component index face)

/-- Dirichlet test data annihilate the integrated Maxwell boundary divergence
for each physical gauge component. -/
theorem integral_regularIntrinsicMaxwellLocalBoundaryDivergence_eq_zero_of_dirichlet
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4)
    (boundary : RegularIntrinsicMaxwellLocalBoxDirichlet period hPeriod
      variation patch box)
    (component : Fin 2) :
    (∫ coordinate in Icc box.lower box.upper,
      regularIntrinsicMaxwellLocalBoundaryDivergence period hPeriod metric
        potential variation component patch coordinate) = 0 := by
  rw [integral_regularIntrinsicMaxwellLocalBoundaryDivergence_eq_faces]
  apply Finset.sum_eq_zero
  intro index _
  simp_rw [regularIntrinsicMaxwellLocalBoundaryCurrent_front_eq_zero period
    hPeriod metric potential variation patch box boundary component index,
    regularIntrinsicMaxwellLocalBoundaryCurrent_back_eq_zero period hPeriod
      metric potential variation patch box boundary component index]
  simp

/-- Gate marker: both Maxwell components have a concrete smooth box Stokes
contract and zero Dirichlet flux. -/
theorem regular_general_metric_c2_smooth_maxwell_local_box_stokes_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4)
    (boundary : RegularIntrinsicMaxwellLocalBoxDirichlet period hPeriod
      variation patch box) :
    ∀ component : Fin 2,
      (∫ coordinate in Icc box.lower box.upper,
        regularIntrinsicMaxwellLocalBoundaryDivergence period hPeriod metric
          potential variation component patch coordinate) = 0 :=
  integral_regularIntrinsicMaxwellLocalBoundaryDivergence_eq_zero_of_dirichlet
    period hPeriod metric potential variation patch box boundary

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwellLocalBoxStokes4D
end JanusFormal
