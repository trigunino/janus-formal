import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquivariantSmoothDescent4D

/-!
# The primitive monopole bundle pulled back to the D9 throat

The fixed throat is the identity mapping torus of the equatorial two-sphere.
Its sphere projection is therefore deck invariant.  Pulling the explicit
charge-one clutching bundle back along this projection gives the actual
principal `U(1)` bundle used by the D9 SpinC sector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusEquivariantSmoothDescent4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D

variable {Index Base Pullback Fiber : Type*}
  [TopologicalSpace Base] [TopologicalSpace Pullback] [TopologicalSpace Fiber]

/-- Topological pullback of a fiber-bundle core. -/
def pullbackFiberBundleCore
    (core : FiberBundleCore Index Base Fiber)
    (baseMap : Pullback → Base) (hBaseMap : Continuous baseMap) :
    FiberBundleCore Index Pullback Fiber where
  baseSet index := baseMap ⁻¹' core.baseSet index
  isOpen_baseSet index :=
    (core.isOpen_baseSet index).preimage hBaseMap
  indexAt point := core.indexAt (baseMap point)
  mem_baseSet_at point := core.mem_baseSet_at (baseMap point)
  coordChange first second point :=
    core.coordChange first second (baseMap point)
  coordChange_self first point hPoint fiber :=
    core.coordChange_self first (baseMap point) hPoint fiber
  continuousOn_coordChange first second := by
    have hProduct :
        Continuous
          (fun pair : Pullback × Fiber => (baseMap pair.1, pair.2)) :=
      (hBaseMap.comp continuous_fst).prodMk continuous_snd
    exact
      (core.continuousOn_coordChange first second).comp'
        hProduct.continuousOn (by
          intro pair hPair
          exact ⟨⟨hPair.1.1, hPair.1.2⟩, hPair.2⟩)
  coordChange_comp first second third point hPoint fiber :=
    core.coordChange_comp first second third (baseMap point) hPoint fiber

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

local instance euclideanR3Finrank :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

/-- The sphere coordinate on the throat cover. -/
def d9MonopoleSphereCoverProjection
    (point : ThroatCover period hPeriod) : MonopoleSphere :=
  equatorialTwoSphereHomeomorph point.fiber

theorem d9MonopoleSphereCoverProjection_deck
    (winding : Int) (point : ThroatCover period hPeriod) :
    d9MonopoleSphereCoverProjection period hPeriod (winding +ᵥ point) =
      d9MonopoleSphereCoverProjection period hPeriod point := by
  change
    equatorialTwoSphereHomeomorph
        (((Homeomorph.refl EquatorialTwoSphere) ^ winding) point.fiber) =
      equatorialTwoSphereHomeomorph point.fiber
  rw [show ((Homeomorph.refl EquatorialTwoSphere) ^ winding) point.fiber =
      ((Homeomorph.refl EquatorialTwoSphere) ^ winding).toEquiv
        point.fiber from rfl,
    homeomorph_toEquiv_zpow,
    show (Homeomorph.refl EquatorialTwoSphere).toEquiv = 1 from rfl,
    one_zpow]
  rfl

theorem d9MonopoleSphereCoverProjection_contMDiff :
    ContMDiff throatCoverModelWithCorners (𝓡 2) ω
      (d9MonopoleSphereCoverProjection period hPeriod) := by
  have hToProduct :
      ContMDiff throatCoverModelWithCorners
        ((𝓡 2).prod 𝓘(Real)) ω
        (coverHomeomorphProd (ThroatData period hPeriod)) :=
    chartedSpacePullback_toFun_contMDiff
      throatCoverModelWithCorners ω
      (coverHomeomorphProd (ThroatData period hPeriod))
  have hFiber :
      ContMDiff throatCoverModelWithCorners (𝓡 2) ω
        (fun point : ThroatCover period hPeriod => point.fiber) :=
    contMDiff_fst.comp hToProduct
  exact
    (chartedSpacePullback_toFun_contMDiff
      (𝓡 2) ω equatorialTwoSphereHomeomorph).comp hFiber

/-- The intrinsic projection `S² × S¹ → S²` on the actual quotient throat. -/
def d9ThroatMonopoleSphereProjection :
    ThroatBase period hPeriod → MonopoleSphere :=
  mappingTorusInvariantMap
    (ThroatData period hPeriod)
    (d9MonopoleSphereCoverProjection period hPeriod)
    (d9MonopoleSphereCoverProjection_deck period hPeriod)

@[simp]
theorem d9ThroatMonopoleSphereProjection_mk
    (point : ThroatCover period hPeriod) :
    d9ThroatMonopoleSphereProjection period hPeriod
        (mappingTorusMk (ThroatData period hPeriod) point) =
      d9MonopoleSphereCoverProjection period hPeriod point :=
  rfl

theorem d9ThroatMonopoleSphereProjection_contMDiff :
    ContMDiff throatCoverModelWithCorners (𝓡 2) ω
      (d9ThroatMonopoleSphereProjection period hPeriod) := by
  exact mappingTorusInvariantMap_contMDiff
    (sourceData := ThroatData period hPeriod)
    (sourceModel := throatCoverModelWithCorners)
    (n := ω) (targetModel' := 𝓡 2)
    (invariantMap := d9MonopoleSphereCoverProjection period hPeriod)
    (hInvariant := d9MonopoleSphereCoverProjection_deck period hPeriod)
    (hSourceProjection :=
      fixedThroat_projection_isLocalDiffeomorph period hPeriod)
    (hInvariantMap :=
      d9MonopoleSphereCoverProjection_contMDiff period hPeriod)

theorem d9ThroatMonopoleSphereProjection_continuous :
    Continuous (d9ThroatMonopoleSphereProjection period hPeriod) :=
  (d9ThroatMonopoleSphereProjection_contMDiff period hPeriod).continuous

/-- Pullback chart domains on the actual D9 throat. -/
def d9PrimitiveMonopoleChartDomain (chart : MonopoleChart) :
    Set (ThroatBase period hPeriod) :=
  d9ThroatMonopoleSphereProjection period hPeriod ⁻¹'
    monopoleChartDomain chart

theorem d9PrimitiveMonopoleChartDomain_isOpen (chart : MonopoleChart) :
    IsOpen (d9PrimitiveMonopoleChartDomain period hPeriod chart) :=
  (monopoleChartDomain_isOpen chart).preimage
    (d9ThroatMonopoleSphereProjection_continuous period hPeriod)

theorem d9PrimitiveMonopoleChartDomain_cover
    (point : ThroatBase period hPeriod) :
    ∃ chart, point ∈ d9PrimitiveMonopoleChartDomain period hPeriod chart := by
  exact monopoleChartDomain_cover
    (d9ThroatMonopoleSphereProjection period hPeriod point)

/-- The charge-`charge` principal circle bundle on the actual D9 throat. -/
def d9PrimitiveMonopolePrincipalBundleCore (charge : Int) :
    FiberBundleCore MonopoleChart (ThroatBase period hPeriod) Circle :=
  pullbackFiberBundleCore
    (primitiveMonopolePrincipalBundleCore charge)
    (d9ThroatMonopoleSphereProjection period hPeriod)
    (d9ThroatMonopoleSphereProjection_continuous period hPeriod)

@[simp]
theorem d9PrimitiveMonopolePrincipalBundleCore_baseSet
    (charge : Int) (chart : MonopoleChart) :
    (d9PrimitiveMonopolePrincipalBundleCore
      period hPeriod charge).baseSet chart =
      d9PrimitiveMonopoleChartDomain period hPeriod chart :=
  rfl

@[simp]
theorem d9PrimitiveMonopolePrincipalBundleCore_coordChange
    (charge : Int) (first second : MonopoleChart)
    (point : ThroatBase period hPeriod) (phase : Circle) :
    (d9PrimitiveMonopolePrincipalBundleCore
      period hPeriod charge).coordChange first second point phase =
      primitiveMonopoleTransition charge first second
        (d9ThroatMonopoleSphereProjection period hPeriod point) * phase :=
  rfl

/-- On every lifted sphere slice the pullback clutching character is the
original charge-`charge` character. -/
theorem d9PrimitiveMonopoleTransition_lift
    (charge : Int) (first second : MonopoleChart)
    (point : ThroatCover period hPeriod) :
    primitiveMonopoleTransition charge first second
        (d9ThroatMonopoleSphereProjection period hPeriod
          (mappingTorusMk (ThroatData period hPeriod) point)) =
      primitiveMonopoleTransition charge first second
        (d9MonopoleSphereCoverProjection period hPeriod point) := by
  rfl

/-- Concrete certificate that D9 carries the pulled-back primitive `U(1)`
bundle, with no additional topological assumption. -/
structure D9PrimitiveMonopoleBundleCertificate where
  principalCore :
    FiberBundleCore MonopoleChart (ThroatBase period hPeriod) Circle
  principalCore_eq :
    principalCore = d9PrimitiveMonopolePrincipalBundleCore period hPeriod 1
  primitiveCharge : Int
  primitiveCharge_eq : primitiveCharge = 1
  flux : Real
  flux_eq : flux = 2 * Real.pi

def d9CanonicalPrimitiveMonopoleBundleCertificate :
    D9PrimitiveMonopoleBundleCertificate period hPeriod where
  principalCore := d9PrimitiveMonopolePrincipalBundleCore period hPeriod 1
  principalCore_eq := rfl
  primitiveCharge := 1
  primitiveCharge_eq := rfl
  flux :=
    2 * Real.pi *
      (∫ polarAngle in (0 : Real)..Real.pi,
        primitiveMonopoleCurvatureCoefficient 1 polarAngle)
  flux_eq := by
    simpa using primitiveMonopoleFlux_quantized 1

end
end P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
end JanusFormal
