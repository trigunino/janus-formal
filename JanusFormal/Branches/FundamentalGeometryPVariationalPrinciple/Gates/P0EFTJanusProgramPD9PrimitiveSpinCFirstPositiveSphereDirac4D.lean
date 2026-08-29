import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D

/-!
# First positive spherical primitive SpinC Dirac level

This gate derives the first positive spherical spectral identity directly
from the geometric Hopf zero mode and the local Clifford connection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalDiracGaugeCovariance4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusNormalPinLiftBoundaryConditions

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

/-- Apply one fixed Clifford generator to every local representative. -/
def d9PrimitiveSpinCCliffordLocalGaugeFamily
    (choice : NormalRootChoice) (cliffordDirection : Fin 3)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice) :
    SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice where
  localValue index base :=
    d9DoubledMatterFiberCliffordGammaCLM cliffordDirection
      (family.localValue index base)
  contMDiffOn_localValue index :=
    (d9DoubledMatterFiberCliffordGammaCLM
      cliffordDirection).contDiff.contMDiff
      |>.comp_contMDiffOn (family.contMDiffOn_localValue index)
  coordChange_localValue first second base hBase := by
    simp only [d9DoubledMatterFiberCliffordGammaCLM_apply]
    rw [← d9PrimitiveSpinCCoordChange_clifford,
      family.coordChange_localValue first second base hBase]

@[simp]
theorem d9PrimitiveSpinCCliffordLocalGaugeFamily_localValue
    (choice : NormalRootChoice) (cliffordDirection : Fin 3)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    (d9PrimitiveSpinCCliffordLocalGaugeFamily
      period hPeriod choice cliffordDirection family).localValue
        index base =
      d9DoubledMatterFiberCliffordGammaCLM cliffordDirection
        (family.localValue index base) :=
  rfl

/-- A constant Clifford generator commutes with the ordinary manifold
derivative of a local representative. -/
theorem d9PrimitiveSpinCLocalFlatFrameDerivative_clifford
    (choice : NormalRootChoice) (cliffordDirection : Fin 3)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalFlatFrameDerivative
        period hPeriod choice
        (d9PrimitiveSpinCCliffordLocalGaugeFamily
          period hPeriod choice cliffordDirection family)
        index direction base =
      d9DoubledMatterFiberCliffordGammaCLM cliffordDirection
        (d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod choice family index direction base) := by
  let field := family.localValue index
  let tangent := d9IntrinsicThroatFrame period hPeriod direction base
  have hField :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) field base :=
    ((family.contMDiffOn_localValue index).contMDiffAt
      ((d9PrimitiveSpinCBaseSet_isOpen
        period hPeriod index).mem_nhds hBase)).mdifferentiableAt (by simp)
  have hOuter :
      MDifferentiableAt
        𝓘(Real, D9DoubledMatterFiber)
        𝓘(Real, D9DoubledMatterFiber)
        (d9DoubledMatterFiberCliffordGammaCLM cliffordDirection)
        (field base) :=
    (d9DoubledMatterFiberCliffordGammaCLM
      cliffordDirection).differentiableAt.mdifferentiableAt
  have hChain := mfderiv_comp_apply base hOuter hField tangent
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hChain
  unfold d9PrimitiveSpinCLocalFlatFrameDerivative
  change
    mfderiv throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber)
        (d9DoubledMatterFiberCliffordGammaCLM
          cliffordDirection ∘ field) base tangent =
      d9DoubledMatterFiberCliffordGammaCLM cliffordDirection
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber) field base tangent)
  exact hChain

/-- Clifford contraction by the quotient radial unit vector. -/
def d9PrimitiveSpinCBaseUnitRadialClifford
    (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) : D9DoubledMatterFiber :=
  ∑ direction : Fin 3,
    d9PrimitiveSpinCBaseUnitRadialCoordinate
        period hPeriod direction base •
      d9DoubledMatterFiberCliffordGammaCLM direction matter

/-- Exact Clifford commutator of the radial Levi--Civita spin correction. -/
theorem d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_clifford
    (direction cliffordDirection : Fin 3)
    (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
        period hPeriod direction base
        (d9DoubledMatterFiberCliffordGammaCLM
          cliffordDirection matter) =
      d9DoubledMatterFiberCliffordGammaCLM cliffordDirection
          (d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
            period hPeriod direction base matter) +
        d9KroneckerDelta direction cliffordDirection •
          d9PrimitiveSpinCBaseUnitRadialClifford
            period hPeriod base matter -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod cliffordDirection base •
          d9DoubledMatterFiberCliffordGammaCLM direction matter := by
  fin_cases direction <;> fin_cases cliffordDirection <;>
    simp [d9PrimitiveSpinCBaseLeviCivitaSpinCorrection,
      d9PrimitiveSpinCBaseUnitRadialClifford,
      d9KroneckerDelta, Fin.sum_univ_succ, map_smul,
      d9DoubledMatterFiberCliffordGamma_sq,
      d9DoubledMatterFiberCliffordGamma_anticommute
        1 0 (by decide),
      d9DoubledMatterFiberCliffordGamma_anticommute
        2 0 (by decide),
      d9DoubledMatterFiberCliffordGamma_anticommute
        2 1 (by decide)] <;>
    module

/-- The full Levi--Civita derivative of a Clifford-transformed family. -/
theorem d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_clifford
    (choice : NormalRootChoice) (cliffordDirection : Fin 3)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
        period hPeriod choice
        (d9PrimitiveSpinCCliffordLocalGaugeFamily
          period hPeriod choice cliffordDirection family)
        index direction base =
      d9DoubledMatterFiberCliffordGammaCLM cliffordDirection
          (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
            period hPeriod choice family index direction base) +
        d9KroneckerDelta direction cliffordDirection •
          d9PrimitiveSpinCBaseUnitRadialClifford
            period hPeriod base (family.localValue index base) -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod cliffordDirection base •
          d9DoubledMatterFiberCliffordGammaCLM direction
            (family.localValue index base) := by
  unfold d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
  rw [d9PrimitiveSpinCLocalFlatFrameDerivative_clifford
      (hBase := hBase),
    d9PrimitiveSpinCCliffordLocalGaugeFamily_localValue,
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_clifford,
    map_add]
  abel

/-- The coupled directional derivative inherits the same Clifford
commutator; the abelian SpinC connection commutes with Clifford action. -/
theorem d9PrimitiveSpinCLocalDirectionalDerivative_clifford
    (choice : NormalRootChoice) (cliffordDirection : Fin 3)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalDirectionalDerivative
        (d9PrimitiveSpinCTotalConnectionFrameCoefficient
          period hPeriod index.2 direction base)
        (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod choice
          (d9PrimitiveSpinCCliffordLocalGaugeFamily
            period hPeriod choice cliffordDirection family)
          index direction base)
        ((d9PrimitiveSpinCCliffordLocalGaugeFamily
          period hPeriod choice cliffordDirection family).localValue
            index base) =
      d9DoubledMatterFiberCliffordGammaCLM cliffordDirection
          (d9PrimitiveSpinCLocalDirectionalDerivative
            (d9PrimitiveSpinCTotalConnectionFrameCoefficient
              period hPeriod index.2 direction base)
            (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
              period hPeriod choice family index direction base)
            (family.localValue index base)) +
        d9KroneckerDelta direction cliffordDirection •
          d9PrimitiveSpinCBaseUnitRadialClifford
            period hPeriod base (family.localValue index base) -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod cliffordDirection base •
          d9DoubledMatterFiberCliffordGammaCLM direction
            (family.localValue index base) := by
  rw [d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_clifford
      (hBase := hBase),
    d9PrimitiveSpinCCliffordLocalGaugeFamily_localValue]
  unfold d9PrimitiveSpinCLocalDirectionalDerivative
  rw [d9PrimitiveSpinCImaginaryAction_clifford, map_add, map_smul]
  abel

/-- Three-dimensional Clifford contraction of the directional commutator. -/
theorem d9DoubledMatterFiberCliffordDirectionalCommutator_contraction
    (cliffordDirection : Fin 3)
    (derivative : Fin 3 → D9DoubledMatterFiber)
    (radial matter : D9DoubledMatterFiber)
    (radialCoordinate : Real) :
    (∑ direction : Fin 3,
        d9DoubledMatterFiberCliffordGammaCLM direction
          (d9DoubledMatterFiberCliffordGammaCLM cliffordDirection
                (derivative direction) +
            d9KroneckerDelta direction cliffordDirection • radial -
            radialCoordinate •
              d9DoubledMatterFiberCliffordGammaCLM direction matter)) =
      -d9DoubledMatterFiberCliffordGammaCLM cliffordDirection
          (∑ direction : Fin 3,
            d9DoubledMatterFiberCliffordGammaCLM direction
              (derivative direction)) -
        (2 : Real) • derivative cliffordDirection +
        d9DoubledMatterFiberCliffordGammaCLM
          cliffordDirection radial +
        (3 * radialCoordinate) • matter := by
  fin_cases cliffordDirection <;>
    simp [Fin.sum_univ_succ, d9KroneckerDelta, map_add, map_sub,
      map_smul, d9DoubledMatterFiberCliffordGamma_sq,
      d9DoubledMatterFiberCliffordGamma_anticommute
        1 0 (by decide),
      d9DoubledMatterFiberCliffordGamma_anticommute
        2 0 (by decide),
      d9DoubledMatterFiberCliffordGamma_anticommute
        2 1 (by decide)] <;>
    module

/-- General local Dirac formula after applying one fixed Clifford
generator to a smooth primitive SpinC representative. -/
theorem d9PrimitiveSpinCLocalGeometricDirac_clifford
    (choice : NormalRootChoice) (cliffordDirection : Fin 3)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice
        (d9PrimitiveSpinCCliffordLocalGaugeFamily
          period hPeriod choice cliffordDirection family)
        index base =
      -d9DoubledMatterFiberCliffordGammaCLM cliffordDirection
          (d9PrimitiveSpinCLocalGeometricDirac
            period hPeriod choice family index base) -
        (2 : Real) •
          d9PrimitiveSpinCLocalDirectionalDerivative
            (d9PrimitiveSpinCTotalConnectionFrameCoefficient
              period hPeriod index.2 cliffordDirection base)
            (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
              period hPeriod choice family index cliffordDirection base)
            (family.localValue index base) +
        d9DoubledMatterFiberCliffordGammaCLM cliffordDirection
          (d9PrimitiveSpinCBaseUnitRadialClifford
            period hPeriod base (family.localValue index base)) +
        (3 *
          d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod cliffordDirection base) •
          family.localValue index base := by
  unfold d9PrimitiveSpinCLocalGeometricDirac
    d9PrimitiveSpinCLocalDirac
  simp_rw [d9PrimitiveSpinCLocalDirectionalDerivative_clifford
    (hBase := hBase)]
  exact
    d9DoubledMatterFiberCliffordDirectionalCommutator_contraction
      cliffordDirection
      (fun direction =>
        d9PrimitiveSpinCLocalDirectionalDerivative
          (d9PrimitiveSpinCTotalConnectionFrameCoefficient
            period hPeriod index.2 direction base)
          (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
            period hPeriod choice family index direction base)
          (family.localValue index base))
      (d9PrimitiveSpinCBaseUnitRadialClifford
        period hPeriod base (family.localValue index base))
      (family.localValue index base)
      (d9PrimitiveSpinCBaseUnitRadialCoordinate
        period hPeriod cliffordDirection base)

/-- The quotient radial Clifford contraction agrees with the established
cover contraction at a mapping-torus representative. -/
@[simp]
theorem d9PrimitiveSpinCBaseUnitRadialClifford_mk
    (point : MappingTorusCover (ThroatData period hPeriod))
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseUnitRadialClifford
        period hPeriod
        (mappingTorusMk (ThroatData period hPeriod) point) matter =
      d9UnitRadialClifford period hPeriod point matter := by
  unfold d9PrimitiveSpinCBaseUnitRadialClifford
    d9UnitRadialClifford
  simp_rw [d9PrimitiveSpinCBaseUnitRadialCoordinate_mk]

/-- The local Dirac action on a constant Clifford transform of the Hopf
zero mode, before forming the tangential first-level combination. -/
theorem primitiveSpinCHopfZeroModeCliffordLocalGeometricDirac_mk
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (point : MappingTorusCover (ThroatData period hPeriod))
    (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCCliffordLocalGaugeFamily
          period hPeriod .positiveQuarter coordinate
          (primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode))
        (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point) =
      normalRootLeviCivitaCorrectedFrequency period sector mode •
          d9DoubledMatterFiberCliffordGammaCLM coordinate
            ((primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue
                (point, chart)
                (mappingTorusMk
                  (ThroatData period hPeriod) point)) -
        (2 * normalRootLeviCivitaCorrectedFrequency period sector mode *
          d9UnitRadialCoordinate period hPeriod coordinate point) •
          d9PrimitiveSpinCImaginaryAction
            ((primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue
                (point, chart)
                (mappingTorusMk
                  (ThroatData period hPeriod) point)) +
        d9DoubledMatterFiberCliffordGammaCLM coordinate
          (d9PrimitiveSpinCImaginaryAction
            ((primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue
                (point, chart)
                (mappingTorusMk
                  (ThroatData period hPeriod) point))) +
        (3 * d9UnitRadialCoordinate
          period hPeriod coordinate point) •
          (primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (point, chart)
              (mappingTorusMk
                (ThroatData period hPeriod) point) := by
  let base := mappingTorusMk (ThroatData period hPeriod) point
  let family :=
    primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode
  let matter := family.localValue (point, chart) base
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet
        period hPeriod (point, chart) := by
    constructor
    · exact mappingTorusMk_mem_normalBundleBaseSet
        period hPeriod point
    · exact hChart
  have hDirac :=
    d9PrimitiveSpinCLocalGeometricDirac_clifford
      period hPeriod .positiveQuarter coordinate family
      (point, chart) base hBase
  have hZero :=
    primitiveSpinCHopfZeroModeLocalGeometricDirac_mk
      period hPeriod sector mode point chart hChart
  have hDirectional :=
    primitiveSpinCHopfZeroModeLocalDirectionalDerivative_mk_eq_normal
      period hPeriod sector mode point chart coordinate hChart
  have hRadial :=
    primitiveSpinCHopfZeroModeLocalGaugeFamily_unitRadial_eigen
      period hPeriod sector mode point chart hChart
  change
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCCliffordLocalGaugeFamily
          period hPeriod .positiveQuarter coordinate family)
        (point, chart) base = _
  rw [hDirac, hZero, hDirectional,
    d9PrimitiveSpinCBaseUnitRadialClifford_mk, hRadial,
    d9PrimitiveSpinCBaseUnitRadialCoordinate_mk,
    map_smul]
  module

/-- The coordinate seed formed from the imaginary Hopf representative. -/
def primitiveSpinCHopfFirstSphereCoordinateImaginaryLocalGaugeFamily
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    SmoothPrimitiveSpinCLocalGaugeFamily
      period hPeriod .positiveQuarter :=
  d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
    period hPeriod .positiveQuarter
    (d9PrimitiveMonopoleBaseCoordinate
      period hPeriod coordinate)
    (d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod coordinate)
    (d9PrimitiveSpinCImaginaryLocalGaugeFamily
      period hPeriod .positiveQuarter
      (primitiveSpinCHopfZeroModeLocalGaugeFamily
        period hPeriod sector mode))

@[simp]
theorem primitiveSpinCHopfFirstSphereCoordinateImaginaryLocalGaugeFamily_localValue
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    (primitiveSpinCHopfFirstSphereCoordinateImaginaryLocalGaugeFamily
      period hPeriod coordinate sector mode).localValue index base =
      d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod coordinate base •
        d9PrimitiveSpinCImaginaryAction
          ((primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue index base) :=
  rfl

/-- Clifford gradient of a sphere coordinate acting on the imaginary Hopf
representative. -/
theorem primitiveSpinCHopfTangentialCoordinateClifford_imaginary_mk
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (point : MappingTorusCover (ThroatData period hPeriod))
    (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    (∑ direction : Fin 3,
        d9DoubledMatterFiberCliffordGammaCLM direction
          ((d9KroneckerDelta direction coordinate -
              d9UnitRadialCoordinate
                  period hPeriod direction point *
                d9UnitRadialCoordinate
                  period hPeriod coordinate point) •
            d9PrimitiveSpinCImaginaryAction
              ((primitiveSpinCHopfZeroModeLocalGaugeFamily
                period hPeriod sector mode).localValue
                  (point, chart)
                  (mappingTorusMk
                    (ThroatData period hPeriod) point)))) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
          (d9PrimitiveSpinCImaginaryAction
            ((primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue
                (point, chart)
                (mappingTorusMk
                  (ThroatData period hPeriod) point))) +
        d9UnitRadialCoordinate
            period hPeriod coordinate point •
          (primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (point, chart)
              (mappingTorusMk
                (ThroatData period hPeriod) point) := by
  have hTangential :=
    primitiveSpinCHopfTangentialCoordinateClifford_mk
      period hPeriod coordinate sector mode point chart hChart
  have hApplied :=
    congrArg d9PrimitiveSpinCImaginaryAction hTangential
  simp only [map_sum, map_sub, map_smul,
    d9PrimitiveSpinCImaginaryAction_clifford,
    d9PrimitiveSpinCImaginaryAction_sq] at hApplied
  simpa only [map_smul, smul_neg, sub_neg_eq_add] using hApplied

/-- Complete local Dirac action on the imaginary coordinate seed. -/
theorem primitiveSpinCHopfFirstSphereCoordinateImaginaryLocalGeometricDirac_mk
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (point : MappingTorusCover (ThroatData period hPeriod))
    (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereCoordinateImaginaryLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point) =
      (-normalRootLeviCivitaCorrectedFrequency period sector mode *
          d9UnitRadialCoordinate period hPeriod coordinate point) •
        d9PrimitiveSpinCImaginaryAction
          ((primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (point, chart)
              (mappingTorusMk
                (ThroatData period hPeriod) point)) +
        d9DoubledMatterFiberCliffordGammaCLM coordinate
          (d9PrimitiveSpinCImaginaryAction
            ((primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue
                (point, chart)
                (mappingTorusMk
                  (ThroatData period hPeriod) point))) +
        d9UnitRadialCoordinate period hPeriod coordinate point •
          (primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (point, chart)
              (mappingTorusMk
                (ThroatData period hPeriod) point) := by
  let base := mappingTorusMk (ThroatData period hPeriod) point
  let family :=
    primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode
  let imaginaryFamily :=
    d9PrimitiveSpinCImaginaryLocalGaugeFamily
      period hPeriod .positiveQuarter family
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet
        period hPeriod (point, chart) := by
    constructor
    · exact mappingTorusMk_mem_normalBundleBaseSet
        period hPeriod point
    · exact hChart
  have hLeibniz :=
    d9PrimitiveSpinCLocalGeometricDirac_realScalarMul
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate
        period hPeriod coordinate)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod coordinate)
      imaginaryFamily (point, chart) base hBase
  have hImaginary :=
    d9PrimitiveSpinCLocalGeometricDirac_imaginary
      period hPeriod .positiveQuarter family
      (point, chart) base hBase
  have hZero :=
    primitiveSpinCHopfZeroModeLocalGeometricDirac_mk
      period hPeriod sector mode point chart hChart
  have hGradient :=
    primitiveSpinCHopfTangentialCoordinateClifford_imaginary_mk
      period hPeriod coordinate sector mode point chart hChart
  have hGradient' := hGradient
  simp only [d9DoubledMatterFiberCliffordGammaCLM_apply] at hGradient'
  have hCoordinate :
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (mappingTorusMk (ThroatData period hPeriod) point) =
        d9UnitRadialCoordinate period hPeriod coordinate point :=
    rfl
  change
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
          period hPeriod .positiveQuarter
          (d9PrimitiveMonopoleBaseCoordinate
            period hPeriod coordinate)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod coordinate)
          imaginaryFamily)
        (point, chart) base = _
  rw [hLeibniz, hImaginary, hZero, map_smul]
  dsimp [base]
  unfold d9PrimitiveSpinCScalarCliffordGradientAt
  dsimp [imaginaryFamily, family]
  simp_rw [d9PrimitiveMonopoleBaseCoordinate_mvfderiv_intrinsicFrame,
    d9PrimitiveMonopoleCoordinateFrameDerivative_eq_projector,
    d9PrimitiveSpinCBaseUnitRadialCoordinate_mk]
  rw [hCoordinate, hGradient']
  module

/-- Subtract two compatible smooth local gauge families. -/
def d9PrimitiveSpinCSubLocalGaugeFamily
    (first second :
      SmoothPrimitiveSpinCLocalGaugeFamily
        period hPeriod .positiveQuarter) :
    SmoothPrimitiveSpinCLocalGaugeFamily
      period hPeriod .positiveQuarter where
  localValue index base :=
    first.localValue index base - second.localValue index base
  contMDiffOn_localValue index :=
    (first.contMDiffOn_localValue index).sub
      (second.contMDiffOn_localValue index)
  coordChange_localValue firstIndex secondIndex base hBase := by
    rw [map_sub,
      first.coordChange_localValue firstIndex secondIndex base hBase,
      second.coordChange_localValue firstIndex secondIndex base hBase]

@[simp]
theorem d9PrimitiveSpinCSubLocalGaugeFamily_localValue
    (first second :
      SmoothPrimitiveSpinCLocalGaugeFamily
        period hPeriod .positiveQuarter)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    (d9PrimitiveSpinCSubLocalGaugeFamily
      period hPeriod first second).localValue index base =
      first.localValue index base - second.localValue index base :=
  rfl

theorem d9PrimitiveSpinCLocalFlatFrameDerivative_sub
    (first second :
      SmoothPrimitiveSpinCLocalGaugeFamily
        period hPeriod .positiveQuarter)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalFlatFrameDerivative
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCSubLocalGaugeFamily
          period hPeriod first second)
        index direction base =
      d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod .positiveQuarter first index direction base -
        d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod .positiveQuarter second index direction base := by
  have hFirst :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber)
        (first.localValue index) base :=
    ((first.contMDiffOn_localValue index).contMDiffAt
      ((d9PrimitiveSpinCBaseSet_isOpen
        period hPeriod index).mem_nhds hBase)).mdifferentiableAt (by simp)
  have hSecond :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber)
        (second.localValue index) base :=
    ((second.contMDiffOn_localValue index).contMDiffAt
      ((d9PrimitiveSpinCBaseSet_isOpen
        period hPeriod index).mem_nhds hBase)).mdifferentiableAt (by simp)
  unfold d9PrimitiveSpinCLocalFlatFrameDerivative
  have hFunction :
      (d9PrimitiveSpinCSubLocalGaugeFamily
        period hPeriod first second).localValue index =
        first.localValue index - second.localValue index := by
    funext current
    rfl
  rw [hFunction, mfderiv_sub hFirst hSecond]
  rfl

theorem d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_sub
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (first second : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
        period hPeriod direction base (first - second) =
      d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
          period hPeriod direction base first -
        d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
          period hPeriod direction base second := by
  unfold d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro other _
  by_cases hSame : other = direction
  · simp [hSame]
  · simp only [hSame, ↓reduceIte, map_sub, smul_sub]

theorem d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_sub
    (first second :
      SmoothPrimitiveSpinCLocalGaugeFamily
        period hPeriod .positiveQuarter)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (direction : Fin 3) (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCSubLocalGaugeFamily
          period hPeriod first second)
        index direction base =
      d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod .positiveQuarter first index direction base -
        d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod .positiveQuarter second index direction base := by
  unfold d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
  rw [d9PrimitiveSpinCLocalFlatFrameDerivative_sub
      (hBase := hBase),
    d9PrimitiveSpinCSubLocalGaugeFamily_localValue,
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_sub]
  abel

theorem d9PrimitiveSpinCLocalGeometricDirac_sub
    (first second :
      SmoothPrimitiveSpinCLocalGaugeFamily
        period hPeriod .positiveQuarter)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCSubLocalGaugeFamily
          period hPeriod first second)
        index base =
      d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod .positiveQuarter first index base -
        d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod .positiveQuarter second index base := by
  unfold d9PrimitiveSpinCLocalGeometricDirac
    d9PrimitiveSpinCLocalDirac
  calc
    _ = ∑ direction : Fin 3,
        (d9DoubledMatterFiberCliffordGammaCLM direction
            (d9PrimitiveSpinCLocalDirectionalDerivative
              (d9PrimitiveSpinCTotalConnectionFrameCoefficient
                period hPeriod index.2 direction base)
              (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
                period hPeriod .positiveQuarter first
                index direction base)
              (first.localValue index base)) -
          d9DoubledMatterFiberCliffordGammaCLM direction
            (d9PrimitiveSpinCLocalDirectionalDerivative
              (d9PrimitiveSpinCTotalConnectionFrameCoefficient
                period hPeriod index.2 direction base)
              (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
                period hPeriod .positiveQuarter second
                index direction base)
              (second.localValue index base))) := by
        apply Finset.sum_congr rfl
        intro direction _
        simp only
        rw [d9PrimitiveSpinCLocalLeviCivitaFrameDerivative_sub
          (hBase := hBase)]
        simp only [d9PrimitiveSpinCSubLocalGaugeFamily_localValue,
          d9PrimitiveSpinCLocalDirectionalDerivative,
          map_sub, smul_sub, map_add]
        abel
    _ = _ := by
      simp only [Finset.sum_sub_distrib]

/-- Intrinsic tangential partner
`T_j = γ_j ψ - n_j Jψ` of the coordinate seed `X_j = n_j ψ`. -/
def primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    SmoothPrimitiveSpinCLocalGaugeFamily
      period hPeriod .positiveQuarter :=
  d9PrimitiveSpinCSubLocalGaugeFamily period hPeriod
    (d9PrimitiveSpinCCliffordLocalGaugeFamily
      period hPeriod .positiveQuarter coordinate
      (primitiveSpinCHopfZeroModeLocalGaugeFamily
        period hPeriod sector mode))
    (primitiveSpinCHopfFirstSphereCoordinateImaginaryLocalGaugeFamily
      period hPeriod coordinate sector mode)

@[simp]
theorem primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily_localValue
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
      period hPeriod coordinate sector mode).localValue index base =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
          ((primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue index base) -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod coordinate base •
          d9PrimitiveSpinCImaginaryAction
            ((primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue index base) :=
  rfl

/-- Exact first-level two-component system:
`D T_j = 2 X_j + k T_j`. -/
theorem primitiveSpinCHopfFirstSphereTangentialLocalGeometricDirac_mk
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (point : MappingTorusCover (ThroatData period hPeriod))
    (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point) =
      (2 * d9UnitRadialCoordinate
          period hPeriod coordinate point) •
        (primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (point, chart)
            (mappingTorusMk (ThroatData period hPeriod) point) +
        normalRootLeviCivitaCorrectedFrequency period sector mode •
          (d9DoubledMatterFiberCliffordGammaCLM coordinate
              ((primitiveSpinCHopfZeroModeLocalGaugeFamily
                period hPeriod sector mode).localValue
                  (point, chart)
                  (mappingTorusMk
                    (ThroatData period hPeriod) point)) -
            d9UnitRadialCoordinate period hPeriod coordinate point •
              d9PrimitiveSpinCImaginaryAction
                ((primitiveSpinCHopfZeroModeLocalGaugeFamily
                  period hPeriod sector mode).localValue
                    (point, chart)
                    (mappingTorusMk
                      (ThroatData period hPeriod) point))) := by
  let base := mappingTorusMk (ThroatData period hPeriod) point
  let zeroFamily :=
    primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode
  let cliffordFamily :=
    d9PrimitiveSpinCCliffordLocalGaugeFamily
      period hPeriod .positiveQuarter coordinate zeroFamily
  let coordinateImaginaryFamily :=
    primitiveSpinCHopfFirstSphereCoordinateImaginaryLocalGaugeFamily
      period hPeriod coordinate sector mode
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet
        period hPeriod (point, chart) := by
    constructor
    · exact mappingTorusMk_mem_normalBundleBaseSet
        period hPeriod point
    · exact hChart
  have hSub :=
    d9PrimitiveSpinCLocalGeometricDirac_sub
      period hPeriod cliffordFamily coordinateImaginaryFamily
      (point, chart) base hBase
  have hClifford :=
    primitiveSpinCHopfZeroModeCliffordLocalGeometricDirac_mk
      period hPeriod coordinate sector mode point chart hChart
  have hCoordinateImaginary :=
    primitiveSpinCHopfFirstSphereCoordinateImaginaryLocalGeometricDirac_mk
      period hPeriod coordinate sector mode point chart hChart
  change
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCSubLocalGaugeFamily
          period hPeriod cliffordFamily coordinateImaginaryFamily)
        (point, chart) base = _
  rw [hSub, hClifford, hCoordinateImaginary]
  module

/-- Global smooth tangential partner of one first-level coordinate seed. -/
def primitiveSpinCHopfFirstSphereTangentialSection
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter :=
  (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
    period hPeriod coordinate sector mode).toSmoothSection
      period hPeriod .positiveQuarter

@[simp]
theorem primitiveSpinCHopfFirstSphereTangentialSection_apply
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (base : ThroatBase period hPeriod) :
    primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod coordinate sector mode base =
      primitiveSpinCHopfFirstSphereCoordinateTangentialAt
        period hPeriod coordinate sector mode base :=
  rfl

/-- Global operator form of `D T_j = 2 X_j + k T_j`. -/
theorem primitiveSpinCHopfFirstSphereTangentialGeometricDiracOperator_apply
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector mode) base =
      (2 : Real) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod coordinate sector mode base +
        normalRootLeviCivitaCorrectedFrequency period sector mode •
          primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod coordinate sector mode base := by
  let tangentFamily :=
    primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
      period hPeriod coordinate sector mode
  let core :=
    d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter
  let point := normalBundleIndexAt period hPeriod base
  let chart :=
    (d9PrimitiveMonopolePrincipalBundleCore
      period hPeriod 1).indexAt base
  have hIndex :
      core.indexAt base = (point, chart) :=
    rfl
  have hProject :
      mappingTorusMk (ThroatData period hPeriod) point = base :=
    normalBundleIndexAt_projects period hPeriod base
  have hChartBase :
      base ∈ d9PrimitiveMonopoleChartDomain
        period hPeriod chart :=
    (core.mem_baseSet_at base).2
  have hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart := by
    unfold d9PrimitiveMonopoleChartDomain at hChartBase
    rw [← hProject] at hChartBase
    exact hChartBase
  unfold primitiveSpinCHopfFirstSphereTangentialSection
  rw [d9PrimitiveSpinCGeometricDiracOperator_toSmoothSection]
  rw [d9PrimitiveSpinCGeometricDiracSection_apply]
  change
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter tangentFamily
        (point, chart) base = _
  simp only [
    primitiveSpinCHopfFirstSphereCoordinateSection_apply,
    primitiveSpinCHopfZeroModeSection,
    SmoothPrimitiveSpinCLocalGaugeFamily.toSmoothSection_apply,
    primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily_localValue]
  rw [hIndex]
  rw [← hProject]
  rw [primitiveSpinCHopfFirstSphereTangentialLocalGeometricDirac_mk
    (hChart := hChart)]
  let matter :=
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode).localValue
        (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point)
  change
    (2 * d9UnitRadialCoordinate
        period hPeriod coordinate point) • matter +
        normalRootLeviCivitaCorrectedFrequency period sector mode •
          (d9DoubledMatterFiberCliffordGammaCLM coordinate matter -
            d9UnitRadialCoordinate period hPeriod coordinate point •
              d9PrimitiveSpinCImaginaryAction matter) =
      (2 : Real) •
          (d9UnitRadialCoordinate
            period hPeriod coordinate point • matter) +
        normalRootLeviCivitaCorrectedFrequency period sector mode •
          (d9DoubledMatterFiberCliffordGammaCLM coordinate matter -
            d9UnitRadialCoordinate period hPeriod coordinate point •
              d9PrimitiveSpinCImaginaryAction matter)
  module

/-- Constant real homogeneity of the complete local geometric Dirac
operator. -/
theorem d9PrimitiveSpinCLocalGeometricDirac_constantRealScalarMul
    (choice : NormalRootChoice) (scalar : Real)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice
        (d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
          period hPeriod choice
          (fun _ : ThroatBase period hPeriod => scalar)
          contMDiff_const family)
        index base =
      scalar •
        d9PrimitiveSpinCLocalGeometricDirac
          period hPeriod choice family index base := by
  rw [d9PrimitiveSpinCLocalGeometricDirac_realScalarMul
    (hBase := hBase)]
  unfold d9PrimitiveSpinCScalarCliffordGradientAt
  simp [mvfderiv_const scalar]

/-- Real homogeneity of the descended geometric Dirac operator. -/
theorem d9PrimitiveSpinCGeometricDiracOperator_real_smul
    (choice : NormalRootChoice) (scalar : Real)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod choice (scalar • state) =
      scalar •
        d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod choice state := by
  let family :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod choice state
  let scaledFamily :=
    d9PrimitiveSpinCRealScalarMulLocalGaugeFamily
      period hPeriod choice
      (fun _ : ThroatBase period hPeriod => scalar)
      contMDiff_const family
  have hScaledSection :
      scaledFamily.toSmoothSection period hPeriod choice =
        scalar • state := by
    calc
      _ =
          scalar •
            family.toSmoothSection period hPeriod choice := by
        ext base
        rfl
      _ = scalar • state := by
        rw [
          d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_toSmoothSection]
  rw [← hScaledSection,
    d9PrimitiveSpinCGeometricDiracOperator_toSmoothSection]
  ext base
  rw [d9PrimitiveSpinCGeometricDiracSection_apply]
  rw [d9PrimitiveSpinCLocalGeometricDirac_constantRealScalarMul
    (hBase :=
      (d9PrimitiveSpinCVectorBundleCore
        period hPeriod choice).mem_baseSet_at base)]
  rfl

/-- Section-level first equation `D X_j = -k X_j + T_j`. -/
theorem primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_eq
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector mode) =
      (-normalRootLeviCivitaCorrectedFrequency period sector mode) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod coordinate sector mode +
        primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector mode := by
  ext base
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector mode) base =
      (-normalRootLeviCivitaCorrectedFrequency period sector mode) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod coordinate sector mode base +
        primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector mode base
  rw [
    primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_apply',
    primitiveSpinCHopfFirstSphereCoordinateSection_apply,
    primitiveSpinCHopfFirstSphereTangentialSection_apply]
  module

/-- Section-level second equation `D T_j = 2 X_j + k T_j`. -/
theorem primitiveSpinCHopfFirstSphereTangentialGeometricDiracOperator_eq
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector mode) =
      (2 : Real) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod coordinate sector mode +
        normalRootLeviCivitaCorrectedFrequency period sector mode •
          primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod coordinate sector mode := by
  ext base
  exact
    primitiveSpinCHopfFirstSphereTangentialGeometricDiracOperator_apply
      period hPeriod coordinate sector mode base

/-- The first spherical coordinate seeds are genuine eigensections of
`D²`, with the derived shift `k² + 2`. -/
theorem primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_sq
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod coordinate sector mode)) =
      (normalRootLeviCivitaCorrectedFrequency
            period sector mode ^ 2 + 2) •
        primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector mode := by
  rw [
    primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_eq,
    d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_eq,
    primitiveSpinCHopfFirstSphereTangentialGeometricDiracOperator_eq]
  module

/-- Positive frequency of the first nonzero spherical Dirac block. -/
def primitiveSpinCHopfFirstSphereDiracFrequency
    (sector : NormalRootChoice) (mode : Int) : Real :=
  Real.sqrt
    (normalRootLeviCivitaCorrectedFrequency
        period sector mode ^ 2 + 2)

theorem primitiveSpinCHopfFirstSphereDiracFrequency_sq
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSphereDiracFrequency
          period sector mode ^ 2 =
      normalRootLeviCivitaCorrectedFrequency
          period sector mode ^ 2 + 2 := by
  unfold primitiveSpinCHopfFirstSphereDiracFrequency
  rw [Real.sq_sqrt]
  positivity

theorem primitiveSpinCHopfFirstSphereDiracFrequency_pos
    (sector : NormalRootChoice) (mode : Int) :
    0 <
      primitiveSpinCHopfFirstSphereDiracFrequency
        period sector mode := by
  unfold primitiveSpinCHopfFirstSphereDiracFrequency
  exact Real.sqrt_pos.2 (by positivity)

/-- Positive first-level eigensection obtained by diagonalizing the
geometric `(X_j,T_j)` block. -/
def primitiveSpinCHopfFirstSpherePositiveSection
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter :=
  (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
      normalRootLeviCivitaCorrectedFrequency period sector mode) •
        primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector mode +
    primitiveSpinCHopfFirstSphereTangentialSection
      period hPeriod coordinate sector mode

/-- Negative first-level eigensection of the same geometric block. -/
def primitiveSpinCHopfFirstSphereNegativeSection
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter :=
  (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
      normalRootLeviCivitaCorrectedFrequency period sector mode) •
        primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector mode +
    primitiveSpinCHopfFirstSphereTangentialSection
      period hPeriod coordinate sector mode

/-- The positive first-level section satisfies the genuine first-order
Dirac eigen-equation. -/
theorem primitiveSpinCHopfFirstSpherePositiveGeometricDiracOperator_eigen
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode) =
      primitiveSpinCHopfFirstSphereDiracFrequency period sector mode •
        primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode := by
  unfold primitiveSpinCHopfFirstSpherePositiveSection
  rw [d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_eq,
    primitiveSpinCHopfFirstSphereTangentialGeometricDiracOperator_eq]
  have hSquare :=
    primitiveSpinCHopfFirstSphereDiracFrequency_sq
      period sector mode
  let frequency :=
    primitiveSpinCHopfFirstSphereDiracFrequency period sector mode
  let normal :=
    normalRootLeviCivitaCorrectedFrequency period sector mode
  let coordinateSection :=
    primitiveSpinCHopfFirstSphereCoordinateSection
      period hPeriod coordinate sector mode
  let tangentSection :=
    primitiveSpinCHopfFirstSphereTangentialSection
      period hPeriod coordinate sector mode
  have hSquare' : frequency ^ 2 = normal ^ 2 + 2 := by
    simpa [frequency, normal] using hSquare
  change
    (frequency - normal) •
          ((-normal) • coordinateSection + tangentSection) +
        ((2 : Real) • coordinateSection + normal • tangentSection) =
      frequency •
        ((frequency - normal) • coordinateSection + tangentSection)
  calc
    _ =
        (normal ^ 2 + 2 - normal * frequency) •
            coordinateSection +
          frequency • tangentSection := by
      module
    _ =
        (frequency ^ 2 - normal * frequency) •
            coordinateSection +
          frequency • tangentSection := by
      rw [hSquare']
    _ = _ := by
      module

/-- The companion section has the negative first-level Dirac eigenvalue. -/
theorem primitiveSpinCHopfFirstSphereNegativeGeometricDiracOperator_eigen
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
        primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode := by
  unfold primitiveSpinCHopfFirstSphereNegativeSection
  rw [d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_eq,
    primitiveSpinCHopfFirstSphereTangentialGeometricDiracOperator_eq]
  let frequency :=
    primitiveSpinCHopfFirstSphereDiracFrequency period sector mode
  let normal :=
    normalRootLeviCivitaCorrectedFrequency period sector mode
  let coordinateSection :=
    primitiveSpinCHopfFirstSphereCoordinateSection
      period hPeriod coordinate sector mode
  let tangentSection :=
    primitiveSpinCHopfFirstSphereTangentialSection
      period hPeriod coordinate sector mode
  have hSquare :
      frequency ^ 2 = normal ^ 2 + 2 := by
    simpa [frequency, normal] using
      primitiveSpinCHopfFirstSphereDiracFrequency_sq
        period sector mode
  change
    (-frequency - normal) •
          ((-normal) • coordinateSection + tangentSection) +
        ((2 : Real) • coordinateSection + normal • tangentSection) =
      (-frequency) •
        ((-frequency - normal) • coordinateSection + tangentSection)
  calc
    _ =
        (normal ^ 2 + 2 + normal * frequency) •
            coordinateSection +
          (-frequency) • tangentSection := by
      module
    _ =
        (frequency ^ 2 + normal * frequency) •
            coordinateSection +
          (-frequency) • tangentSection := by
      rw [hSquare]
    _ = _ := by
      module

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
end JanusFormal
