import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeHolonomicCutoffDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalCutoffCollarMFDeriv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeAdaptedHolonomicGreenCurrentFlux4D

/-!
# Genuine canonical cutoff in local normal-first holonomic coordinates
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeHolonomicGlobalCutoffPullback4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeHolonomicCutoffDerivative4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalTangentialAdaptedHolonomicChart4D
open P0EFTJanusMappingTorusCanonicalLatitudeAdaptedHolonomicGreenCurrentFlux4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffScalarGreenDivergence4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffGreenNormalTangentialSplit4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCutBulkCanonicalCutoffGlobalSmooth4D
open P0EFTJanusMappingTorusCutBulkCanonicalCutoffCollarMFDeriv4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := Fin 4 → Real

/-- Pullback of the genuine global cutoff along an arbitrary local base
representative and the normal-first coordinate. -/
def canonicalLatitudeHolonomicGlobalCutoffPullback
    (baseMap : Vector4 → CanonicalLatitudeBase) (coordinate : Vector4) : Real :=
  cutBulkCanonicalCutoffCollarPullback period hPeriod
    (baseMap coordinate, coordinate 0)

theorem canonicalLatitudeHolonomicGlobalCutoffPullback_eq
    (baseMap : Vector4 → CanonicalLatitudeBase) (coordinate : Vector4)
    (hNormal : coordinate 0 ∈ Icc (0 : Real) 1) :
    canonicalLatitudeHolonomicGlobalCutoffPullback
        period hPeriod baseMap coordinate =
      canonicalLatitudeHolonomicCollarCutoff coordinate := by
  unfold canonicalLatitudeHolonomicGlobalCutoffPullback
    cutBulkCanonicalCutoffCollarPullback
  rw [cutBulkCanonicalCutoff_canonicalLatitudeCutBulkCollarMap
    period hPeriod (baseMap coordinate) (coordinate 0) hNormal]
  rfl

theorem canonicalLatitudeHolonomicGlobalCutoffPullback_eventuallyEq
    (baseMap : Vector4 → CanonicalLatitudeBase) (coordinate : Vector4)
    (hNormal : coordinate 0 ∈ Ioo (0 : Real) 1) :
    Filter.EventuallyEq (nhds coordinate)
      (canonicalLatitudeHolonomicGlobalCutoffPullback period hPeriod baseMap)
      canonicalLatitudeHolonomicCollarCutoff := by
  have hNeighborhood :
      (fun current : Vector4 => current 0) ⁻¹' Ioo (0 : Real) 1 ∈
        nhds coordinate :=
    (isOpen_Ioo.preimage (continuous_apply 0)).mem_nhds hNormal
  filter_upwards [hNeighborhood] with current hCurrent
  exact canonicalLatitudeHolonomicGlobalCutoffPullback_eq
    period hPeriod baseMap current ⟨hCurrent.1.le, hCurrent.2.le⟩

theorem fderiv_canonicalLatitudeHolonomicGlobalCutoffPullback_eq
    (baseMap : Vector4 → CanonicalLatitudeBase) (coordinate : Vector4)
    (hNormal : coordinate 0 ∈ Ioo (0 : Real) 1) :
    fderiv Real
        (canonicalLatitudeHolonomicGlobalCutoffPullback period hPeriod baseMap)
        coordinate =
      fderiv Real canonicalLatitudeHolonomicCollarCutoff coordinate :=
  (canonicalLatitudeHolonomicGlobalCutoffPullback_eventuallyEq
    period hPeriod baseMap coordinate hNormal).fderiv_eq

theorem canonicalLatitudeHolonomicGlobalCutoffPullback_fderiv_basis
    (baseMap : Vector4 → CanonicalLatitudeBase) (coordinate : Vector4)
    (hNormal : coordinate 0 ∈ Ioo (0 : Real) 1) (index : Fin 4) :
    fderiv Real
        (canonicalLatitudeHolonomicGlobalCutoffPullback period hPeriod baseMap)
        coordinate (Pi.single index 1) =
      if index = 0 then deriv canonicalLatitudeCollarCutoff (coordinate 0)
      else 0 := by
  rw [fderiv_canonicalLatitudeHolonomicGlobalCutoffPullback_eq
      period hPeriod baseMap coordinate hNormal,
    canonicalLatitudeHolonomicCollarCutoff_fderiv_basis]

theorem canonicalLatitudeHolonomicGlobalCutoffPullback_normalOnlyAt
    (baseMap : Vector4 → CanonicalLatitudeBase) (coordinate : Vector4)
    (hNormal : coordinate 0 ∈ Ioo (0 : Real) 1) :
    P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffGreenNormalTangentialSplit4D.LocalCutoffNormalOnlyAt
      (canonicalLatitudeHolonomicGlobalCutoffPullback period hPeriod baseMap)
      coordinate := by
  intro tangent
  rw [canonicalLatitudeHolonomicGlobalCutoffPullback_fderiv_basis
    period hPeriod baseMap coordinate hNormal]
  simp

/-- The canonical cutoff in a normal-first chart centered at `center`. -/
def canonicalLatitudeCenteredHolonomicCollarCutoff
    (center : Real) (coordinate : Vector4) : Real :=
  canonicalLatitudeCollarCutoff (center + holonomicNormalCoordinate coordinate)

/-- Genuine cutoff pullback in the same centered local coordinates. -/
def canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
    (center : Real) (baseMap : Vector4 → CanonicalLatitudeBase)
    (coordinate : Vector4) : Real :=
  cutBulkCanonicalCutoffCollarPullback period hPeriod
    (baseMap coordinate, center + coordinate 0)

theorem canonicalLatitudeCenteredHolonomicGlobalCutoffPullback_eq
    (center : Real) (baseMap : Vector4 → CanonicalLatitudeBase)
    (coordinate : Vector4)
    (hNormal : center + coordinate 0 ∈ Icc (0 : Real) 1) :
    canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
        period hPeriod center baseMap coordinate =
      canonicalLatitudeCenteredHolonomicCollarCutoff center coordinate := by
  unfold canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
    cutBulkCanonicalCutoffCollarPullback
  rw [cutBulkCanonicalCutoff_canonicalLatitudeCutBulkCollarMap
    period hPeriod (baseMap coordinate) (center + coordinate 0) hNormal]
  rfl

theorem canonicalLatitudeCenteredHolonomicGlobalCutoffPullback_eventuallyEq
    (center : Real) (baseMap : Vector4 → CanonicalLatitudeBase)
    (coordinate : Vector4)
    (hNormal : center + coordinate 0 ∈ Ioo (0 : Real) 1) :
    Filter.EventuallyEq (nhds coordinate)
      (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
        period hPeriod center baseMap)
      (canonicalLatitudeCenteredHolonomicCollarCutoff center) := by
  have hNeighborhood :
      (fun current : Vector4 => center + current 0) ⁻¹' Ioo (0 : Real) 1 ∈
        nhds coordinate :=
    (isOpen_Ioo.preimage (continuous_const.add (continuous_apply 0))).mem_nhds
      hNormal
  filter_upwards [hNeighborhood] with current hCurrent
  exact canonicalLatitudeCenteredHolonomicGlobalCutoffPullback_eq
    period hPeriod center baseMap current ⟨hCurrent.1.le, hCurrent.2.le⟩

theorem canonicalLatitudeCenteredHolonomicCollarCutoff_fderiv_basis
    (center : Real) (coordinate : Vector4) (index : Fin 4) :
    fderiv Real (canonicalLatitudeCenteredHolonomicCollarCutoff center) coordinate
        (Pi.single index 1) =
      if index = 0 then
        deriv canonicalLatitudeCollarCutoff (center + coordinate 0)
      else 0 := by
  have hDerivative : HasDerivAt canonicalLatitudeCollarCutoff
      (deriv canonicalLatitudeCollarCutoff (center + coordinate 0))
      (center + coordinate 0) :=
    (canonicalLatitudeCollarCutoff_contDiff.differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hInner : HasFDerivAt
      (fun current : Vector4 => center + holonomicNormalCoordinate current)
      holonomicNormalCoordinate coordinate :=
    holonomicNormalCoordinate.hasFDerivAt.const_add center
  have hComp := hDerivative.comp_hasFDerivAt coordinate hInner
  rw [show canonicalLatitudeCenteredHolonomicCollarCutoff center =
      canonicalLatitudeCollarCutoff ∘
        (fun current : Vector4 => center + holonomicNormalCoordinate current) by rfl,
    hComp.fderiv]
  by_cases hIndex : index = 0
  · subst index
    simp [holonomicNormalCoordinate]
  · simp [holonomicNormalCoordinate, hIndex]

theorem canonicalLatitudeCenteredHolonomicGlobalCutoffPullback_fderiv_basis
    (center : Real) (baseMap : Vector4 → CanonicalLatitudeBase)
    (coordinate : Vector4)
    (hNormal : center + coordinate 0 ∈ Ioo (0 : Real) 1)
    (index : Fin 4) :
    fderiv Real
        (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
          period hPeriod center baseMap)
        coordinate (Pi.single index 1) =
      if index = 0 then
        deriv canonicalLatitudeCollarCutoff (center + coordinate 0)
      else 0 := by
  rw [(canonicalLatitudeCenteredHolonomicGlobalCutoffPullback_eventuallyEq
      period hPeriod center baseMap coordinate hNormal).fderiv_eq,
    canonicalLatitudeCenteredHolonomicCollarCutoff_fderiv_basis]

theorem canonicalLatitudeCenteredHolonomicGlobalCutoffPullback_normalOnlyAt
    (center : Real) (baseMap : Vector4 → CanonicalLatitudeBase)
    (coordinate : Vector4)
    (hNormal : center + coordinate 0 ∈ Ioo (0 : Real) 1) :
    P0EFTJanusMappingTorusGeneralLorentzMetricLocalCutoffGreenNormalTangentialSplit4D.LocalCutoffNormalOnlyAt
      (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
        period hPeriod center baseMap)
      coordinate := by
  intro tangent
  rw [canonicalLatitudeCenteredHolonomicGlobalCutoffPullback_fderiv_basis
    period hPeriod center baseMap coordinate hNormal]
  simp

theorem canonicalLatitudeCenteredHolonomicGlobalCutoffPullback_differentiableAt
    (center : Real) (baseMap : Vector4 → CanonicalLatitudeBase)
    (coordinate : Vector4)
    (hNormal : center + coordinate 0 ∈ Ioo (0 : Real) 1) :
    DifferentiableAt Real
      (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
        period hPeriod center baseMap)
      coordinate := by
  have hSynthetic : DifferentiableAt Real
      (canonicalLatitudeCenteredHolonomicCollarCutoff center) coordinate := by
    have hInner : DifferentiableAt Real
        (fun current : Vector4 => center + holonomicNormalCoordinate current)
        coordinate :=
      holonomicNormalCoordinate.differentiableAt.const_add center
    exact (canonicalLatitudeCollarCutoff_contDiff.differentiable
      (by simp)).differentiableAt.comp coordinate hInner
  exact hSynthetic.congr_of_eventuallyEq
    (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback_eventuallyEq
      period hPeriod center baseMap coordinate hNormal)

/-- At the center of an adapted holonomic chart, the divergence of the genuine
cutoff pullback is the bump derivative times the canonical normal current. -/
theorem localActualCenteredGlobalCutoffGreenCoordinateDivergence_eq_normalCurrent_of_free
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Ioo (0 : Real) 1)
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (baseMap : Vector4 → CanonicalLatitudeBase)
    (field test : SmoothScalarField period hPeriod)
    (hFree : localActualScalarGreenCoordinateDivergence period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test 0 = 0) :
    localActualCutoffScalarGreenCoordinateDivergence period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test
        (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
          period hPeriod normal baseMap) 0 =
      deriv canonicalLatitudeCollarCutoff normal *
        canonicalLatitudeScalarGreenCurrent
          period hPeriod field test base normal := by
  rw [localActualCutoffScalarGreenCoordinateDivergence_eq_normalGradientFlux_of_free
    period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
    (chart.toSmoothHolonomicFrameChart4 period hPeriod) field test
    (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback
      period hPeriod normal baseMap) 0
    (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback_differentiableAt
      period hPeriod normal baseMap 0 (by simpa using hNormal))
    hFree
    (canonicalLatitudeCenteredHolonomicGlobalCutoffPullback_normalOnlyAt
      period hPeriod normal baseMap 0 (by simpa using hNormal)),
    canonicalLatitudeCenteredHolonomicGlobalCutoffPullback_fderiv_basis
      period hPeriod normal baseMap 0 (by simpa using hNormal),
    localActualScalarGreenCurrent_adapted_zero_normal
      period hPeriod base normal chart field test]
  simp

end
end P0EFTJanusMappingTorusCanonicalLatitudeHolonomicGlobalCutoffPullback4D
end JanusFormal
