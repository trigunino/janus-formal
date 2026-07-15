import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaussianNormalEHGHYCancellation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaussianNormalEmbeddedHypersurface

/-!
# Integrated Gaussian-normal EH/GHY cancellation on a tangent box

The affine Gaussian-normal point data are held constant on a compact
three-coordinate box.  The Einstein--Hilbert boundary flux and the exact GHY
first derivative already derived pointwise are turned into genuine tangent
densities and integrated by three nested interval integrals.  Each integration
stage is proved interval-integrable, the underlying coordinate box has finite
volume, and the integrated EH plus GHY contribution vanishes.

Both admissible normal orientations and a pair of independent Janus sectors
are covered.  This remains a local affine box calculation: it is not a global
hypersurface, partition of unity, Stokes theorem, or manifold integration
result.
-/

namespace JanusFormal
namespace P0EFTJanusGaussianNormalIntegratedBoundaryBox

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusNonNullGHYFirstVariation
open P0EFTJanusNonNullGHYMeasureVariation
open P0EFTJanusGaussianNormalEHGHYCancellation
open P0EFTJanusGaussianNormalEmbeddedHypersurface

abbrev TangentPoint :=
  P0EFTJanusGaussianNormalEmbeddedHypersurface.TangentCoordinate3

/-- A closed coordinate box in the three tangential coordinates. -/
structure CompactTangentBox where
  lower : TangentPoint
  upper : TangentPoint
  lower_le_upper : ∀ index, lower index ≤ upper index

/-- The actual compact subset of the tangent coordinate model. -/
def tangentBoxSet (box : CompactTangentBox) : Set TangentPoint :=
  Set.Icc box.lower box.upper

theorem compactTangentBox_lower_le_upper (box : CompactTangentBox) :
    box.lower ≤ box.upper :=
  box.lower_le_upper

theorem tangentBoxSet_isCompact (box : CompactTangentBox) :
    IsCompact (tangentBoxSet box) := by
  exact isCompact_Icc

/-- The full three-dimensional coordinate box has finite volume. -/
theorem tangentBoxSet_volume_lt_top (box : CompactTangentBox) :
    volume (tangentBoxSet box) < ⊤ := by
  exact measure_Icc_lt_top

/-- Curried coordinates assembled into one tangent point. -/
def tangentPoint (x0 x1 x2 : ℝ) : TangentPoint :=
  fun index => Fin.cases x0 (Fin.cases x1 (fun _ => x2)) index

/-- A genuine three-fold interval integral over the tangent box. -/
def tangentBoxIntegral
    (box : CompactTangentBox) (density : TangentPoint → ℝ) : ℝ :=
  ∫ x0 in box.lower 0..box.upper 0,
    ∫ x1 in box.lower 1..box.upper 1,
      ∫ x2 in box.lower 2..box.upper 2,
        density (tangentPoint x0 x1 x2)

/-- Coordinate volume appearing in the iterated integral. -/
def tangentBoxVolume (box : CompactTangentBox) : ℝ :=
  (box.upper 0 - box.lower 0) *
    (box.upper 1 - box.lower 1) *
      (box.upper 2 - box.lower 2)

theorem tangentBoxVolume_nonnegative (box : CompactTangentBox) :
    0 ≤ tangentBoxVolume box := by
  have h0 : 0 ≤ box.upper 0 - box.lower 0 :=
    sub_nonneg.mpr (box.lower_le_upper 0)
  have h1 : 0 ≤ box.upper 1 - box.lower 1 :=
    sub_nonneg.mpr (box.lower_le_upper 1)
  have h2 : 0 ≤ box.upper 2 - box.lower 2 :=
    sub_nonneg.mpr (box.lower_le_upper 2)
  exact mul_nonneg (mul_nonneg h0 h1) h2

/-- The iterated integral of a constant density is its value times the actual
coordinate volume of the box. -/
theorem tangentBoxIntegral_const
    (box : CompactTangentBox) (constant : ℝ) :
    tangentBoxIntegral box (fun _ => constant) =
      tangentBoxVolume box * constant := by
  simp [tangentBoxIntegral, tangentBoxVolume,
    intervalIntegral.integral_const]
  ring

/-- Integrability obligations at all three levels of the iterated integral. -/
structure BoxIntervalIntegrable
    (box : CompactTangentBox) (density : TangentPoint → ℝ) : Prop where
  inner : ∀ x0 x1,
    IntervalIntegrable
      (fun x2 => density (tangentPoint x0 x1 x2)) volume
      (box.lower 2) (box.upper 2)
  middle : ∀ x0,
    IntervalIntegrable
      (fun x1 => ∫ x2 in box.lower 2..box.upper 2,
        density (tangentPoint x0 x1 x2)) volume
      (box.lower 1) (box.upper 1)
  outer :
    IntervalIntegrable
      (fun x0 => ∫ x1 in box.lower 1..box.upper 1,
        ∫ x2 in box.lower 2..box.upper 2,
          density (tangentPoint x0 x1 x2)) volume
      (box.lower 0) (box.upper 0)

theorem boxIntervalIntegrable_const
    (box : CompactTangentBox) (constant : ℝ) :
    BoxIntervalIntegrable box (fun _ => constant) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x0 x1
    exact intervalIntegrable_const
  · intro x0
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    exact intervalIntegrable_const
  · simp only [intervalIntegral.integral_const, smul_eq_mul]
    exact intervalIntegrable_const

/-- Tangent density supplied by the already derived local EH flux. -/
def einsteinHilbertFluxDensity
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) : TangentPoint → ℝ :=
  fun _ => einsteinHilbertDirichletBoundaryFlux einsteinScale data jet

/-- Tangent density supplied by the exact-inverse GHY first derivative. -/
def exactGHYDerivativeDensity
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) : TangentPoint → ℝ :=
  fun _ =>
    nonNullGHYFirstVariation einsteinScale data
      (metricFirstJetVariation data
        (gaussianDirichletBoundaryVariation jet))

theorem localEH_add_GHY_density_eq_zero
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) (point : TangentPoint) :
    einsteinHilbertFluxDensity einsteinScale data jet point +
      exactGHYDerivativeDensity einsteinScale data jet point = 0 := by
  exact einsteinHilbert_add_exactGHYDirichletDerivative_eq_zero
    einsteinScale data jet

theorem einsteinHilbertFluxDensity_boxIntervalIntegrable
    (box : CompactTangentBox)
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    BoxIntervalIntegrable box
      (einsteinHilbertFluxDensity einsteinScale data jet) := by
  change BoxIntervalIntegrable box
    (fun _ => einsteinHilbertDirichletBoundaryFlux einsteinScale data jet)
  exact boxIntervalIntegrable_const box
    (einsteinHilbertDirichletBoundaryFlux einsteinScale data jet)

theorem exactGHYDerivativeDensity_boxIntervalIntegrable
    (box : CompactTangentBox)
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    BoxIntervalIntegrable box
      (exactGHYDerivativeDensity einsteinScale data jet) := by
  change BoxIntervalIntegrable box
    (fun _ => nonNullGHYFirstVariation einsteinScale data
      (metricFirstJetVariation data
        (gaussianDirichletBoundaryVariation jet)))
  exact boxIntervalIntegrable_const box
    (nonNullGHYFirstVariation einsteinScale data
      (metricFirstJetVariation data
        (gaussianDirichletBoundaryVariation jet)))

/-- Actual integrated Einstein--Hilbert boundary flux. -/
def integratedEinsteinHilbertFlux
    (box : CompactTangentBox)
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) : ℝ :=
  tangentBoxIntegral box
    (einsteinHilbertFluxDensity einsteinScale data jet)

/-- Actual integrated exact GHY derivative. -/
def integratedExactGHYDerivative
    (box : CompactTangentBox)
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) : ℝ :=
  tangentBoxIntegral box
    (exactGHYDerivativeDensity einsteinScale data jet)

theorem integratedEinsteinHilbertFlux_eq
    (box : CompactTangentBox)
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    integratedEinsteinHilbertFlux box einsteinScale data jet =
      tangentBoxVolume box *
        einsteinHilbertDirichletBoundaryFlux einsteinScale data jet := by
  exact tangentBoxIntegral_const box
    (einsteinHilbertDirichletBoundaryFlux einsteinScale data jet)

theorem integratedExactGHYDerivative_eq
    (box : CompactTangentBox)
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    integratedExactGHYDerivative box einsteinScale data jet =
      tangentBoxVolume box *
        nonNullGHYFirstVariation einsteinScale data
          (metricFirstJetVariation data
            (gaussianDirichletBoundaryVariation jet)) := by
  exact tangentBoxIntegral_const box
    (nonNullGHYFirstVariation einsteinScale data
      (metricFirstJetVariation data
        (gaussianDirichletBoundaryVariation jet)))

/-- Integrated cancellation of the local EH flux with the exact GHY
derivative on the compact tangent box. -/
theorem integrated_EH_add_exact_GHY_eq_zero
    (box : CompactTangentBox)
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    integratedEinsteinHilbertFlux box einsteinScale data jet +
      integratedExactGHYDerivative box einsteinScale data jet = 0 := by
  rw [integratedEinsteinHilbertFlux_eq,
    integratedExactGHYDerivative_eq, ← mul_add]
  rw [einsteinHilbert_add_exactGHYDirichletDerivative_eq_zero,
    mul_zero]

/-- The integrated theorem explicitly covers each admissible normal
orientation carried by the boundary data. -/
theorem integrated_cancellation_orientation_cases
    (box : CompactTangentBox)
    (einsteinScale : ℝ) (data : NonNullBoundaryPointData)
    (jet : GaussianNormalDirichletJet) :
    (data.orientationSign = 1 ∧
      integratedEinsteinHilbertFlux box einsteinScale data jet +
        integratedExactGHYDerivative box einsteinScale data jet = 0) ∨
    (data.orientationSign = -1 ∧
      integratedEinsteinHilbertFlux box einsteinScale data jet +
        integratedExactGHYDerivative box einsteinScale data jet = 0) := by
  rcases data.orientationSignAdmissible with hPositive | hNegative
  · exact Or.inl ⟨hPositive,
      integrated_EH_add_exact_GHY_eq_zero box einsteinScale data jet⟩
  · exact Or.inr ⟨hNegative,
      integrated_EH_add_exact_GHY_eq_zero box einsteinScale data jet⟩

/-- Sum of the independently integrated boundary ledgers of two Janus
sectors. -/
def integratedTwoSectorBoundaryLedger
    (box : CompactTangentBox)
    (einsteinScalePlus einsteinScaleMinus : ℝ)
    (dataPlus dataMinus : NonNullBoundaryPointData)
    (jetPlus jetMinus : GaussianNormalDirichletJet) : ℝ :=
  (integratedEinsteinHilbertFlux box einsteinScalePlus dataPlus jetPlus +
    integratedExactGHYDerivative box einsteinScalePlus dataPlus jetPlus) +
  (integratedEinsteinHilbertFlux box einsteinScaleMinus dataMinus jetMinus +
    integratedExactGHYDerivative box einsteinScaleMinus dataMinus jetMinus)

theorem integratedTwoSectorBoundaryLedger_eq_zero
    (box : CompactTangentBox)
    (einsteinScalePlus einsteinScaleMinus : ℝ)
    (dataPlus dataMinus : NonNullBoundaryPointData)
    (jetPlus jetMinus : GaussianNormalDirichletJet) :
    integratedTwoSectorBoundaryLedger box
      einsteinScalePlus einsteinScaleMinus dataPlus dataMinus
      jetPlus jetMinus = 0 := by
  rw [integratedTwoSectorBoundaryLedger,
    integrated_EH_add_exact_GHY_eq_zero,
    integrated_EH_add_exact_GHY_eq_zero, add_zero]

/-- In particular, oppositely oriented sector boundaries cancel separately
before their ledgers are added. -/
theorem oppositeOrientedTwoSectorBoundaryLedger_eq_zero
    (box : CompactTangentBox)
    (einsteinScalePlus einsteinScaleMinus : ℝ)
    (dataPlus dataMinus : NonNullBoundaryPointData)
    (jetPlus jetMinus : GaussianNormalDirichletJet)
    (_hPlusOrientation : dataPlus.orientationSign = 1)
    (_hMinusOrientation : dataMinus.orientationSign = -1) :
    integratedTwoSectorBoundaryLedger box
      einsteinScalePlus einsteinScaleMinus dataPlus dataMinus
      jetPlus jetMinus = 0 :=
  integratedTwoSectorBoundaryLedger_eq_zero box
    einsteinScalePlus einsteinScaleMinus dataPlus dataMinus jetPlus jetMinus

end

end P0EFTJanusGaussianNormalIntegratedBoundaryBox
end JanusFormal
