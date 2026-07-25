import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLocalDiracGaugeCovariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D

/-!
# Cartesian primitive monopole connection on the D9 throat

The north/south Dirac potentials are written without polar coordinates:

`A_N = (q/2) (x dy - y dx)/(1 + z)` and
`A_S = -(q/2) (x dy - y dx)/(1 - z)`.

Their difference on the overlap is the logarithmic angular form
`q (x dy - y dx)/(x² + y²)`.  The formulas are then pulled back through the
actual smooth projection from the mapping torus to `S²` and evaluated on the
global intrinsic throat frame.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Numerator of the angular one-form evaluated on a tangent vector whose
ambient `x` and `y` coordinate derivatives are supplied. -/
def primitiveMonopoleAngularNumerator
    (point : MonopoleSphere) (tangentX tangentY : Real) : Real :=
  monopoleSphereCoordinate point 0 * tangentY -
    monopoleSphereCoordinate point 1 * tangentX

/-- The angular one-form `dφ` on the double overlap. -/
def primitiveMonopoleAngularCoefficient
    (point : MonopoleSphere) (tangentX tangentY : Real) : Real :=
  primitiveMonopoleAngularNumerator point tangentX tangentY /
    (monopoleSphereCoordinate point 0 ^ 2 +
      monopoleSphereCoordinate point 1 ^ 2)

/-- Cartesian evaluation of the charge-`charge` monopole potential. -/
def primitiveMonopoleCartesianPotential
    (charge : Int) (chart : MonopoleChart)
    (point : MonopoleSphere) (tangentX tangentY : Real) : Real :=
  match chart with
  | .north =>
      (charge : Real) / 2 *
        primitiveMonopoleAngularNumerator point tangentX tangentY /
          (1 + monopoleSphereCoordinate point 2)
  | .south =>
      -(charge : Real) / 2 *
        primitiveMonopoleAngularNumerator point tangentX tangentY /
          (1 - monopoleSphereCoordinate point 2)

/-- The equatorial denominator is nonzero on the north/south overlap. -/
theorem monopoleSphereXY_sq_ne_zero_of_mem_overlap
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (hSouth : point ∈ monopoleChartDomain .south) :
    monopoleSphereCoordinate point 0 ^ 2 +
        monopoleSphereCoordinate point 1 ^ 2 ≠ 0 := by
  have hPlus :
      1 + monopoleSphereCoordinate point 2 ≠ 0 := by
    change monopoleSphereCoordinate point 2 ≠ -1 at hNorth
    intro hZero
    apply hNorth
    linarith
  have hMinus :
      1 - monopoleSphereCoordinate point 2 ≠ 0 := by
    change monopoleSphereCoordinate point 2 ≠ 1 at hSouth
    intro hZero
    apply hSouth
    linarith
  have hSphere := monopoleSphereCoordinate_sq_sum point
  have hFactor :
      monopoleSphereCoordinate point 0 ^ 2 +
          monopoleSphereCoordinate point 1 ^ 2 =
        (1 - monopoleSphereCoordinate point 2) *
          (1 + monopoleSphereCoordinate point 2) := by
    nlinarith
  rw [hFactor]
  exact mul_ne_zero hMinus hPlus

/-- Exact Cartesian north/south gauge law on the overlap. -/
theorem primitiveMonopoleCartesianPotential_gauge_difference
    (charge : Int) (point : MonopoleSphere)
    (tangentX tangentY : Real)
    (hNorth : point ∈ monopoleChartDomain .north)
    (hSouth : point ∈ monopoleChartDomain .south) :
    primitiveMonopoleCartesianPotential charge .north
          point tangentX tangentY -
        primitiveMonopoleCartesianPotential charge .south
          point tangentX tangentY =
      (charge : Real) *
        primitiveMonopoleAngularCoefficient point tangentX tangentY := by
  have hPlus :
      1 + monopoleSphereCoordinate point 2 ≠ 0 := by
    change monopoleSphereCoordinate point 2 ≠ -1 at hNorth
    intro hZero
    apply hNorth
    linarith
  have hMinus :
      1 - monopoleSphereCoordinate point 2 ≠ 0 := by
    change monopoleSphereCoordinate point 2 ≠ 1 at hSouth
    intro hZero
    apply hSouth
    linarith
  have hXY :=
    monopoleSphereXY_sq_ne_zero_of_mem_overlap point hNorth hSouth
  have hSphere := monopoleSphereCoordinate_sq_sum point
  unfold primitiveMonopoleCartesianPotential
    primitiveMonopoleAngularCoefficient
    primitiveMonopoleAngularNumerator
  rw [show
    monopoleSphereCoordinate point 0 ^ 2 +
        monopoleSphereCoordinate point 1 ^ 2 =
      (1 - monopoleSphereCoordinate point 2) *
        (1 + monopoleSphereCoordinate point 2) by
    nlinarith [hSphere]]
  field_simp
  ring

/-- One ambient sphere coordinate pulled back to the genuine D9 throat. -/
def d9PrimitiveMonopoleBaseCoordinate
    (coordinate : Fin 3) (base : ThroatBase period hPeriod) : Real :=
  monopoleSphereCoordinate
    (d9ThroatMonopoleSphereProjection period hPeriod base) coordinate

/-- Derivative of a pulled-back sphere coordinate along one vector of the
global intrinsic throat frame. -/
def d9PrimitiveMonopoleCoordinateFrameDerivative
    (coordinate direction : Fin 3)
    (base : ThroatBase period hPeriod) : Real :=
  mfderiv throatCoverModelWithCorners 𝓘(Real)
      (d9PrimitiveMonopoleBaseCoordinate
        period hPeriod coordinate) base
      (d9IntrinsicThroatFrame period hPeriod direction base)

/-- Pulled-back angular coefficient evaluated on one intrinsic frame vector. -/
def d9PrimitiveMonopoleAngularFrameCoefficient
    (direction : Fin 3) (base : ThroatBase period hPeriod) : Real :=
  primitiveMonopoleAngularCoefficient
    (d9ThroatMonopoleSphereProjection period hPeriod base)
    (d9PrimitiveMonopoleCoordinateFrameDerivative
      period hPeriod 0 direction base)
    (d9PrimitiveMonopoleCoordinateFrameDerivative
      period hPeriod 1 direction base)

/-- Pulled-back local monopole potential in one intrinsic frame direction. -/
def d9PrimitiveMonopoleConnectionFrameCoefficient
    (charge : Int) (chart : MonopoleChart)
    (direction : Fin 3) (base : ThroatBase period hPeriod) : Real :=
  primitiveMonopoleCartesianPotential charge chart
    (d9ThroatMonopoleSphereProjection period hPeriod base)
    (d9PrimitiveMonopoleCoordinateFrameDerivative
      period hPeriod 0 direction base)
    (d9PrimitiveMonopoleCoordinateFrameDerivative
      period hPeriod 1 direction base)

/-- The actual pulled-back coefficients obey the connection gauge law in
every intrinsic frame direction. -/
theorem d9PrimitiveMonopoleConnectionFrameCoefficient_gauge_difference
    (charge : Int) (direction : Fin 3)
    (base : ThroatBase period hPeriod)
    (hNorth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .north)
    (hSouth :
      base ∈ d9PrimitiveMonopoleChartDomain period hPeriod .south) :
    d9PrimitiveMonopoleConnectionFrameCoefficient
          period hPeriod charge .north direction base -
        d9PrimitiveMonopoleConnectionFrameCoefficient
          period hPeriod charge .south direction base =
      (charge : Real) *
        d9PrimitiveMonopoleAngularFrameCoefficient
          period hPeriod direction base := by
  exact primitiveMonopoleCartesianPotential_gauge_difference
    charge
    (d9ThroatMonopoleSphereProjection period hPeriod base)
    (d9PrimitiveMonopoleCoordinateFrameDerivative
      period hPeriod 0 direction base)
    (d9PrimitiveMonopoleCoordinateFrameDerivative
      period hPeriod 1 direction base)
    hNorth hSouth

end
end P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
end JanusFormal
