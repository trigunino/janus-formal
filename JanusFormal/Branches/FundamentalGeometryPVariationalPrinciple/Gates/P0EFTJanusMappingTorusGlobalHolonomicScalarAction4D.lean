import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalar4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient

/-!
# Global holonomic scalar action on the actual D8 quotient

The scalar value, its genuine manifold differential, the inverse diagonal
metric and the metric volume density are all computed from one smooth scalar
and one smooth positive metric field on the same compact quotient. The fixed
frame is explicit; no general tensorial diffeomorphism covariance is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalHolonomicScalar4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : Real) (hPeriod : Not (period = 0))

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

/-- Fixed-frame tangent coordinate vectors: time is coordinate zero and the
three Euclidean product coordinates are one through three. -/
def tangentCoordinate (index : Fin 4) : CoverCoordinates :=
  if _hZero : index = 0 then (0, 1)
  else (WithLp.toLp 2 (fun spatial : Fin 3 =>
    if index.val = spatial.val + 1 then (1 : Real) else 0), 0)

/-- Components of the genuine manifold differential in the fixed tangent
frame. -/
def holonomicCovectorComponent
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) : Real :=
  scalarDifferential period hPeriod field point (tangentCoordinate index)

/-- Absolute Lorentz determinant density of one positive diagonal metric. -/
def diagonalMetricVolumeDensity
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (point : EffectiveQuotient period hPeriod) : Real :=
  Real.sqrt (∏ index : Fin 4, magnitude point index)

/-- Fixed-frame contraction of the holonomic covector with the inverse of the
same diagonal Lorentz metric. -/
def diagonalHolonomicKineticDensity
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) : Real :=
  (1 / 2 : Real) * ∑ index : Fin 4,
    signature index / magnitude point index *
      holonomicCovectorComponent period hPeriod field point index ^ 2

/-- Massive scalar density using one scalar, its derivative, one metric and
the corresponding metric volume density. -/
def globalHolonomicScalarDensity
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) : Real :=
  diagonalMetricVolumeDensity period hPeriod magnitude point *
    (diagonalHolonomicKineticDensity period hPeriod magnitude field point +
      (massSquared / 2) * field point ^ 2)

/-- Actual global matter action on the compact effective quotient. -/
def globalHolonomicScalarAction
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (field : SmoothQuotientField period hPeriod Real)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point, globalHolonomicScalarDensity period hPeriod massSquared
    magnitude field point ∂measure

/-- Complete data of one global holonomic scalar sector. The integrability
contract is explicit because a fixed tangent frame need not be a globally
continuous tangent section for an arbitrary quotient atlas. -/
structure GlobalHolonomicScalarSector (massSquared : Real) where
  magnitude : SmoothQuotientField period hPeriod Coefficients4
  magnitude_pos : ∀ point index, 0 < magnitude point index
  scalar : SmoothQuotientField period hPeriod Real
  measure : Measure (EffectiveQuotient period hPeriod)
  density_integrable : Integrable
    (globalHolonomicScalarDensity period hPeriod massSquared magnitude scalar)
    measure

private def unitMagnitude : Coefficients4 := fun _ => 1

/-- Nonempty flat, zero-scalar sector. The zero measure is used only as an
unconditional witness; physical sectors carry their explicit integrability
contract and a chosen nonzero measure. -/
def zeroGlobalHolonomicScalarSector
    (massSquared : Real) :
    GlobalHolonomicScalarSector period hPeriod massSquared where
  magnitude := constantSmoothField period hPeriod Coefficients4 unitMagnitude
  magnitude_pos := by intro point index; simp [constantSmoothField, unitMagnitude]
  scalar := constantSmoothField period hPeriod Real 0
  measure := 0
  density_integrable := integrable_zero_measure

def GlobalHolonomicScalarSector.action
    (massSquared : Real)
    (sector : GlobalHolonomicScalarSector period hPeriod massSquared) : Real :=
  globalHolonomicScalarAction period hPeriod massSquared sector.magnitude
    sector.scalar sector.measure

@[simp]
theorem zeroGlobalHolonomicScalarSector_action
    (massSquared : Real) :
    (zeroGlobalHolonomicScalarSector period hPeriod massSquared).action
      period hPeriod massSquared = 0 := by
  simp [GlobalHolonomicScalarSector.action, globalHolonomicScalarAction,
    zeroGlobalHolonomicScalarSector]

/-- The two physical matter sectors on the same global quotient. -/
structure GlobalTwoSectorHolonomicMatter (massSquared : Real) where
  plus : GlobalHolonomicScalarSector period hPeriod massSquared
  minus : GlobalHolonomicScalarSector period hPeriod massSquared

def GlobalTwoSectorHolonomicMatter.action
    (massSquared : Real)
    (matter : GlobalTwoSectorHolonomicMatter period hPeriod massSquared) : Real :=
  matter.plus.action period hPeriod massSquared +
    matter.minus.action period hPeriod massSquared

/-- Exact exchange of the two global scalar sectors. -/
def exchangeMatterSectors
    (massSquared : Real)
    (matter : GlobalTwoSectorHolonomicMatter period hPeriod massSquared) :
    GlobalTwoSectorHolonomicMatter period hPeriod massSquared :=
  { plus := matter.minus, minus := matter.plus }

@[simp]
theorem exchangeMatterSectors_involutive
    (massSquared : Real)
    (matter : GlobalTwoSectorHolonomicMatter period hPeriod massSquared) :
    exchangeMatterSectors period hPeriod massSquared
        (exchangeMatterSectors period hPeriod massSquared matter) = matter := by
  cases matter
  rfl

theorem twoSectorAction_exchange
    (massSquared : Real)
    (matter : GlobalTwoSectorHolonomicMatter period hPeriod massSquared) :
    (exchangeMatterSectors period hPeriod massSquared matter).action
        period hPeriod massSquared =
      matter.action period hPeriod massSquared := by
  simp [GlobalTwoSectorHolonomicMatter.action, exchangeMatterSectors, add_comm]

/-- The covector in the action is definitionally the unique induced manifold
differential of the same scalar value. -/
theorem actionCovector_eq_scalarDifferential
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    holonomicCovectorComponent period hPeriod field point index =
      (GlobalHolonomicScalar.ofSmooth period hPeriod field).covector point
        (tangentCoordinate index) := by
  rfl

/-- The inverse coefficients used in the kinetic term are exactly those of
the same supplied positive metric magnitude field. -/
theorem kineticInverseCoefficient_eq_sameMetric
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    signature index / magnitude point index =
      lorentzMetricInverse (magnitude point) index index := by
  simp [lorentzMetricInverse]

/-- The volume factor is the square root of the absolute determinant of the
same diagonal Lorentz metric. -/
theorem volumeDensity_sq_eq_absDet_sameMetric
    (magnitude : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point index, 0 < magnitude point index)
    (point : EffectiveQuotient period hPeriod) :
    diagonalMetricVolumeDensity period hPeriod magnitude point ^ 2 =
      |Matrix.det (lorentzMetric (magnitude point))| := by
  rw [diagonalMetricVolumeDensity, sq]
  rw [Real.mul_self_sqrt]
  · have hProductPositive :
        0 < ∏ index : Fin 4, magnitude point index :=
      Finset.prod_pos fun index _ => hPositive point index
    have hSignedProduct :
        (∏ index : Fin 4, signature index * magnitude point index) =
          -(∏ index : Fin 4, magnitude point index) := by
      simp [Fin.prod_univ_succ, signature]
    rw [lorentzMetric, Matrix.det_diagonal, hSignedProduct, abs_neg,
      abs_of_pos hProductPositive]
  · exact Finset.prod_nonneg fun index _ => le_of_lt (hPositive point index)

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
end JanusFormal
