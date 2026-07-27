import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereWitnessFiber4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D

/-!
# Geometric antipodal Hopf witness

The equatorial point of phase `0` makes the two north-gauge Hopf coordinates
both equal to `1`, selecting the sum of the two constant frame vectors.  At
the antipodal equatorial phase `π`, the first coordinate remains `1` while the
complementary coordinate becomes `-1`.  The complete global Hopf zero mode
therefore selects their difference.

The preceding fiber gate proves that this difference reverses the tangential
complex Clifford relation.  Here that algebraic statement is attached to an
actual lifted point, quotient class and local coordinate of the genuine
primitive SpinC smooth section.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalWitness4D

set_option autoImplicit false
noncomputable section

open Bundle
open Set
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereWitnessFiber4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev throatProjectionLocalHomeomorph :
    IsLocalHomeomorph
      (mappingTorusMk (ThroatData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap
    (ThroatData period hPeriod)).isLocalHomeomorph

/-- Lifted antipodal equatorial point at arbitrary normal time. -/
def primitiveSpinCHopfAntipodalWitnessCover
    (time : Real) : ThroatCover period hPeriod :=
  ⟨equatorialTwoSphereHomeomorph.symm
      (monopoleEquator Real.pi), time⟩

/-- Quotient class of the antipodal equatorial witness. -/
def primitiveSpinCHopfAntipodalWitnessBase
    (time : Real) : ThroatBase period hPeriod :=
  mappingTorusMk (ThroatData period hPeriod)
    (primitiveSpinCHopfAntipodalWitnessCover
      period hPeriod time)

/-- Joint normal/monopole chart at the antipodal witness. -/
def primitiveSpinCHopfAntipodalWitnessIndex
    (time : Real) : D9PrimitiveSpinCIndex period hPeriod :=
  (primitiveSpinCHopfAntipodalWitnessCover
      period hPeriod time, .north)

@[simp]
theorem primitiveSpinCHopfAntipodalWitnessCover_time
    (time : Real) :
    (primitiveSpinCHopfAntipodalWitnessCover
      period hPeriod time).time = time :=
  rfl

@[simp]
theorem primitiveSpinCHopfAntipodalWitnessCover_sphere
    (time : Real) :
    d9MonopoleSphereCoverProjection period hPeriod
        (primitiveSpinCHopfAntipodalWitnessCover
          period hPeriod time) =
      monopoleEquator Real.pi := by
  simp [primitiveSpinCHopfAntipodalWitnessCover,
    d9MonopoleSphereCoverProjection]

/-- The first north-gauge Hopf coordinate is `1` at phase `π`. -/
@[simp]
theorem primitiveMonopoleZeroLocalValue_antipodal :
    primitiveMonopoleZeroLocalValue .north
        (monopoleEquator Real.pi) = 1 := by
  simp [primitiveMonopoleZeroLocalValue,
    primitiveMonopoleZeroNorthValue, monopoleEquator,
    monopoleSphereCoordinate]

/-- The complementary north-gauge Hopf coordinate is `-1` at phase `π`. -/
@[simp]
theorem primitiveMonopoleZeroComplementLocalValue_antipodal :
    primitiveMonopoleZeroComplementLocalValue .north
        (monopoleEquator Real.pi) = -1 := by
  simp [primitiveMonopoleZeroComplementLocalValue,
    primitiveMonopoleZeroComplementNorthValue, monopoleEquator,
    monopoleSphereCoordinate, monopoleSphereXY]
  rw [starRingEnd_apply, Complex.star_def]
  rfl

/-- The antipodal quotient point lies in the selected joint chart. -/
theorem primitiveSpinCHopfAntipodalWitnessBase_mem
    (time : Real) :
    primitiveSpinCHopfAntipodalWitnessBase
        period hPeriod time ∈
      d9PrimitiveSpinCBaseSet period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time) := by
  constructor
  · exact (throatProjectionLocalHomeomorph period hPeriod)
      |>.apply_self_mem_localInverseAt_source
  · change
      d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time) ∈
        monopoleChartDomain .north
    rw [primitiveSpinCHopfAntipodalWitnessBase,
      d9ThroatMonopoleSphereProjection_mk,
      primitiveSpinCHopfAntipodalWitnessCover_sphere]
    simp [monopoleChartDomain, monopoleEquator,
      monopoleSphereCoordinate]

/-- Multiplication by the complex scalar `-1` is ordinary additive negation
on the doubled matter fiber. -/
@[simp]
theorem d9PrimitiveSpinCComplexAction_neg_one
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM (-1 : Complex) matter = -matter := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction, map_neg]
  simp

/-- The local value of the complete Hopf zero-mode family at the antipodal
witness is exactly the opposite-frame fiber difference. -/
theorem primitiveSpinCHopfZeroModeLocalGaugeFamily_antipodal
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode).localValue
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time) =
      primitiveSpinCHopfAntipodalWitnessFiber sector
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode
          (primitiveSpinCHopfAntipodalWitnessCover
            period hPeriod time)) := by
  change
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode).localValue
        (primitiveSpinCHopfAntipodalWitnessCover
          period hPeriod time, .north)
        (mappingTorusMk (ThroatData period hPeriod)
          (primitiveSpinCHopfAntipodalWitnessCover
            period hPeriod time)) = _
  rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_mk,
    primitiveSpinCHopfAntipodalWitnessCover_sphere,
    primitiveMonopoleZeroLocalValue_antipodal,
    primitiveMonopoleZeroComplementLocalValue_antipodal,
    d9PrimitiveSpinCComplexAction_one,
    d9PrimitiveSpinCComplexAction_neg_one]
  rfl

/-- The actual genuine global Hopf zero mode has the opposite-frame local
coordinate at the antipodal quotient witness. -/
theorem primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_antipodal
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) =
      primitiveSpinCHopfAntipodalWitnessFiber sector
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode
          (primitiveSpinCHopfAntipodalWitnessCover
            period hPeriod time)) := by
  calc
    primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod time)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector mode) =
        (primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (primitiveSpinCHopfAntipodalWitnessIndex
              period hPeriod time)
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod time) := by
      unfold primitiveSpinCHopfZeroModeSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase_mem
          period hPeriod time)]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode)
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase_mem
          period hPeriod time)
    _ = _ :=
      primitiveSpinCHopfZeroModeLocalGaugeFamily_antipodal
        period hPeriod sector mode time

/-- The antipodal local coordinate of the actual Hopf zero mode obeys the
reversed tangential complex Clifford relation. -/
theorem primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_antipodal_tangential
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod time)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector mode)) =
      -d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod
            (primitiveSpinCHopfAntipodalWitnessIndex
              period hPeriod time)
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod time)
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector mode))) := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_antipodal]
  exact primitiveSpinCHopfAntipodalWitnessFiber_tangential
    sector
    (primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalWitnessCover
        period hPeriod time))
    (primitiveSpinCNormalModeDoubledLift_gamma_one
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalWitnessCover
        period hPeriod time))

/-- Consolidated geometric antipodal witness package. -/
theorem primitiveSpinCHopfAntipodalWitness_closed
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode).localValue
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time) =
      primitiveSpinCHopfAntipodalWitnessFiber sector
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode
          (primitiveSpinCHopfAntipodalWitnessCover
            period hPeriod time)) ∧
      d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod time)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector mode)) =
      -d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod
            (primitiveSpinCHopfAntipodalWitnessIndex
              period hPeriod time)
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod time)
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector mode))) :=
  ⟨primitiveSpinCHopfZeroModeLocalGaugeFamily_antipodal
      period hPeriod sector mode time,
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_antipodal_tangential
      (period := period) (hPeriod := hPeriod) sector mode time⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalWitness4D
end JanusFormal
