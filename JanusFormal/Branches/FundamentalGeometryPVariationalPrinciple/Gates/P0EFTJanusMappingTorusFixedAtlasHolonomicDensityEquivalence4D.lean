import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1IntrinsicPatchCoordinates4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1LocalizedTransitionBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FiniteFramePatchClosure4D

/-!
# Fixed-atlas holonomic density equivalence

The historical holonomic density evaluates model vectors in the preferred
chart centred at the evaluation point.  Its diagonal coordinate change has a
variable chart centre and is not covered by Mathlib's fixed-centre transition
theorems.

This downstream gate removes that diagonal entirely.  It uses the finite
fixed tangent atlas already selected by the partition of unity, packages the
partition-localized fixed-atlas covector components with finite `ℓ²` norms,
and proves a pointwise uniform two-sided equivalence with the implemented
finite-frame graph density.  Fixed-atlas overlap coefficients are continuous
on every closed overlap.

No equality with the historical variable-`chartAt point` density is claimed.
The strongest available bridge to it remains one-sided and conditional on the
already isolated variable preferred-transition continuity contract.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusFixedAtlasHolonomicDensityEquivalence4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalHolonomicScalar4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FixedLocalEnergyReduction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1UniformEllipticity4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FiniteFramePatchClosure4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1LocalizedTransitionBound4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1IntrinsicPatchCoordinates4D

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

/-- One scalar transition coefficient between two members of the fixed finite
atlas.  Both chart centres are fixed before the evaluation point varies. -/
def fixedAtlasTransitionCoefficient
    (target : FiniteTangentGeneratorPatch period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod)
    (coordinate : Fin 4) : Real :=
  finiteFixedTargetTransitionCoefficient period hPeriod target.1 point index
    coordinate

/-- Fixed-centre transition coefficients are continuous on each compact
closed overlap of the finite atlas. -/
theorem fixedAtlasTransitionCoefficient_continuousOn_closedOverlap
    (target : FiniteTangentGeneratorPatch period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod)
    (coordinate : Fin 4) :
    ContinuousOn
      (fun point : EffectiveQuotient period hPeriod =>
        fixedAtlasTransitionCoefficient period hPeriod target point index
          coordinate)
      (finiteTangentGeneratorClosedPatch period hPeriod index.1 ∩
        finiteTangentGeneratorClosedPatch period hPeriod target) := by
  apply (finiteFixedTargetTransitionCoefficient_continuousOn
    period hPeriod target.1 index coordinate).mono
  intro point hPoint
  refine ⟨hPoint.1, ?_⟩
  rw [← finiteTangentGeneratorOpenPatch_eq_chart_source period hPeriod]
  exact finiteTangentGeneratorClosedPatch_subset_openPatch
    period hPeriod target hPoint.2

/-- Covector component in the local frame of one fixed atlas patch. -/
def fixedAtlasLocalHolonomicComponent
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (basisIndex : FiniteTangentGeneratorBasisIndex) : Real :=
  scalarDifferential period hPeriod field point
    (finiteTangentGeneratorLocalVector period hPeriod patch basisIndex point)

/-- The fixed-atlas component localized by the same partition weight as the
implemented global tangent generator. -/
def fixedAtlasLocalizedHolonomicComponent
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod) : Real :=
  finiteTangentGeneratorWeight period hPeriod index.1 point *
    fixedAtlasLocalHolonomicComponent period hPeriod field point index.1
      index.2

theorem fixedAtlasLocalizedHolonomicComponent_eq_finiteLocalized
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod) :
    fixedAtlasLocalizedHolonomicComponent period hPeriod field point index =
      finiteLocalizedCovectorComponent period hPeriod field point index := by
  unfold fixedAtlasLocalizedHolonomicComponent
    fixedAtlasLocalHolonomicComponent finiteLocalizedCovectorComponent
    finiteFixedLocalCovectorComponent
  rfl

/-- Each fixed-atlas component is exactly an implemented graph derivative. -/
theorem finiteFrameDerivative_eq_fixedAtlasLocalizedComponent
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod) :
    frameDerivative period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field point
          (finiteTangentGeneratorIndexEquivFin period hPeriod index) =
      fixedAtlasLocalizedHolonomicComponent period hPeriod field point
        index := by
  rw [fixedAtlasLocalizedHolonomicComponent_eq_finiteLocalized]
  exact finiteFrameDerivative_eq_localizedComponent
    period hPeriod field point index

/-- Canonical finite `ℓ²` fiber for the fixed-atlas value and localized
covector components. -/
abbrev FixedAtlasHolonomicJetFiber :=
  WithLp 2
    (Real × PiLp 2
      (fun _ : FiniteTangentGeneratorIndex period hPeriod => Real))

/-- Fixed-atlas first jet with no variable preferred chart. -/
def fixedAtlasHolonomicFirstJet
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    FixedAtlasHolonomicJetFiber period hPeriod :=
  WithLp.toLp 2
    (field point,
      WithLp.toLp 2
        (fixedAtlasLocalizedHolonomicComponent period hPeriod field point))

private abbrev FixedAtlasGraphJetFiber :=
  Real × (FiniteTangentGeneratorIndex period hPeriod → Real)

/-- The standard finite-dimensional norm equivalence from the fixed-atlas
`ℓ²` jet to the product/sup-norm graph jet. -/
def fixedAtlasHolonomicJetToGraph :
    FixedAtlasHolonomicJetFiber period hPeriod ≃L[Real]
      FixedAtlasGraphJetFiber period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real Real
      (PiLp 2
        (fun _ : FiniteTangentGeneratorIndex period hPeriod => Real))).trans
    ((ContinuousLinearEquiv.refl Real Real).prodCongr
      (PiLp.continuousLinearEquiv 2 Real
        (fun _ : FiniteTangentGeneratorIndex period hPeriod => Real)))

@[simp]
theorem fixedAtlasHolonomicJetToGraph_firstJet
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    fixedAtlasHolonomicJetToGraph period hPeriod
        (fixedAtlasHolonomicFirstJet period hPeriod field point) =
      finiteFixedLocalFirstJet period hPeriod field point := by
  change
    (field point,
      fixedAtlasLocalizedHolonomicComponent period hPeriod field point) =
    (field point, finiteLocalizedCovectorComponent period hPeriod field point)
  apply Prod.ext
  · rfl
  · funext index
    exact fixedAtlasLocalizedHolonomicComponent_eq_finiteLocalized
      period hPeriod field point index

/-- Positive fixed-atlas holonomic density. -/
def fixedAtlasHolonomicDensity
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ‖fixedAtlasHolonomicFirstJet period hPeriod field point‖ ^ 2

theorem fixedAtlasHolonomicDensity_nonneg
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    0 ≤ fixedAtlasHolonomicDensity period hPeriod field point :=
  sq_nonneg _

/-- Nonnegative energy root; definitionally the fixed-atlas `ℓ²` jet norm. -/
def fixedAtlasHolonomicDensityRoot
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ‖fixedAtlasHolonomicFirstJet period hPeriod field point‖

theorem fixedAtlasHolonomicDensityRoot_eq_sqrt
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    fixedAtlasHolonomicDensityRoot period hPeriod field point =
      Real.sqrt (fixedAtlasHolonomicDensity period hPeriod field point) := by
  rw [fixedAtlasHolonomicDensityRoot, fixedAtlasHolonomicDensity,
    Real.sqrt_sq (norm_nonneg _)]

/-- Uniform graph-to-fixed-atlas density constant. -/
def fixedAtlasToGraphDensityConstant : Real :=
  ‖(fixedAtlasHolonomicJetToGraph period hPeriod).toContinuousLinearMap‖ ^ 2

/-- Uniform fixed-atlas-to-graph density constant. -/
def graphToFixedAtlasDensityConstant : Real :=
  ‖(fixedAtlasHolonomicJetToGraph period hPeriod).symm.toContinuousLinearMap‖ ^ 2

theorem fixedAtlasToGraphDensityConstant_nonneg :
    0 ≤ fixedAtlasToGraphDensityConstant period hPeriod :=
  sq_nonneg _

theorem graphToFixedAtlasDensityConstant_nonneg :
    0 ≤ graphToFixedAtlasDensityConstant period hPeriod :=
  sq_nonneg _

/-- First half of the unconditional uniform density equivalence. -/
theorem finiteFixedLocalJacobiDensity_le_fixedAtlasHolonomicDensity
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    finiteFixedLocalJacobiDensity period hPeriod field point ≤
      fixedAtlasToGraphDensityConstant period hPeriod *
        fixedAtlasHolonomicDensity period hPeriod field point := by
  let jet := fixedAtlasHolonomicFirstJet period hPeriod field point
  let equivalence := fixedAtlasHolonomicJetToGraph period hPeriod
  have hNorm : ‖equivalence jet‖ ≤
      ‖equivalence.toContinuousLinearMap‖ * ‖jet‖ :=
    equivalence.toContinuousLinearMap.le_opNorm jet
  have hSquare := mul_self_le_mul_self (norm_nonneg (equivalence jet)) hNorm
  change ‖finiteFixedLocalFirstJet period hPeriod field point‖ ^ 2 ≤
    ‖equivalence.toContinuousLinearMap‖ ^ 2 * ‖jet‖ ^ 2
  rw [← fixedAtlasHolonomicJetToGraph_firstJet period hPeriod field point]
  calc
    ‖equivalence jet‖ ^ 2 =
        ‖equivalence jet‖ * ‖equivalence jet‖ := by rw [pow_two]
    _ ≤ (‖equivalence.toContinuousLinearMap‖ * ‖jet‖) *
        (‖equivalence.toContinuousLinearMap‖ * ‖jet‖) := hSquare
    _ = ‖equivalence.toContinuousLinearMap‖ ^ 2 * ‖jet‖ ^ 2 := by
      ring

/-- Reverse half of the unconditional uniform density equivalence. -/
theorem fixedAtlasHolonomicDensity_le_finiteFixedLocalJacobiDensity
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    fixedAtlasHolonomicDensity period hPeriod field point ≤
      graphToFixedAtlasDensityConstant period hPeriod *
        finiteFixedLocalJacobiDensity period hPeriod field point := by
  let jet := fixedAtlasHolonomicFirstJet period hPeriod field point
  let graphJet := finiteFixedLocalFirstJet period hPeriod field point
  let equivalence := fixedAtlasHolonomicJetToGraph period hPeriod
  have hIdentify : equivalence.symm graphJet = jet := by
    apply equivalence.injective
    rw [equivalence.apply_symm_apply]
    exact (fixedAtlasHolonomicJetToGraph_firstJet
      period hPeriod field point).symm
  have hNorm : ‖equivalence.symm graphJet‖ ≤
      ‖equivalence.symm.toContinuousLinearMap‖ * ‖graphJet‖ :=
    equivalence.symm.toContinuousLinearMap.le_opNorm graphJet
  have hSquare :=
    mul_self_le_mul_self (norm_nonneg (equivalence.symm graphJet)) hNorm
  change ‖jet‖ ^ 2 ≤
    ‖equivalence.symm.toContinuousLinearMap‖ ^ 2 * ‖graphJet‖ ^ 2
  rw [← hIdentify]
  calc
    ‖equivalence.symm graphJet‖ ^ 2 =
        ‖equivalence.symm graphJet‖ * ‖equivalence.symm graphJet‖ := by
      rw [pow_two]
    _ ≤ (‖equivalence.symm.toContinuousLinearMap‖ * ‖graphJet‖) *
        (‖equivalence.symm.toContinuousLinearMap‖ * ‖graphJet‖) := hSquare
    _ = ‖equivalence.symm.toContinuousLinearMap‖ ^ 2 * ‖graphJet‖ ^ 2 := by
      ring

/-- Root form of the reverse comparison, used by the residual historical
density bridge below. -/
theorem fixedAtlasHolonomicDensityRoot_le_finiteFixedLocalJacobiRoot
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    fixedAtlasHolonomicDensityRoot period hPeriod field point ≤
      ‖(fixedAtlasHolonomicJetToGraph period hPeriod).symm.toContinuousLinearMap‖ *
        Real.sqrt
          (finiteFixedLocalJacobiDensity period hPeriod field point) := by
  let jet := fixedAtlasHolonomicFirstJet period hPeriod field point
  let graphJet := finiteFixedLocalFirstJet period hPeriod field point
  let equivalence := fixedAtlasHolonomicJetToGraph period hPeriod
  have hIdentify : equivalence.symm graphJet = jet := by
    apply equivalence.injective
    rw [equivalence.apply_symm_apply]
    exact (fixedAtlasHolonomicJetToGraph_firstJet
      period hPeriod field point).symm
  change ‖jet‖ ≤
    ‖equivalence.symm.toContinuousLinearMap‖ * Real.sqrt (‖graphJet‖ ^ 2)
  rw [Real.sqrt_sq (norm_nonneg graphJet), ← hIdentify]
  exact equivalence.symm.toContinuousLinearMap.le_opNorm graphJet

/-- Exact residual statement for comparison with the historical density.
Only domination of the fixed-atlas root is currently available. -/
structure FixedAtlasHistoricalHolonomicDomination
    (data : PositiveStaticGlobalScalarData period hPeriod) where
  constant : Real
  constant_nonneg : 0 ≤ constant
  pointwise_bound : ∀
      (field : StaticGlobalScalarTest period hPeriod data)
      (point : EffectiveQuotient period hPeriod),
    fixedAtlasHolonomicDensityRoot period hPeriod field.toField point ≤
      constant * staticScalarJacobiDensityRoot period hPeriod data field point

/-- The isolated variable preferred-transition continuity contract gives the
strongest presently justified bridge to the historical raw density. -/
def FiniteVariablePreferredTransitionContinuity.toFixedAtlasHistoricalDomination
    (regularity : FiniteVariablePreferredTransitionContinuity period hPeriod)
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    FixedAtlasHistoricalHolonomicDomination period hPeriod data := by
  let domination := regularity.toEnergyDomination period hPeriod data
  let transitionConstant :=
    ‖(fixedAtlasHolonomicJetToGraph period hPeriod).symm.toContinuousLinearMap‖
  refine
    { constant := transitionConstant * domination.constant
      constant_nonneg := mul_nonneg (norm_nonneg _) domination.constant_nonneg
      pointwise_bound := ?_ }
  intro field point
  calc
    fixedAtlasHolonomicDensityRoot period hPeriod field.toField point ≤
        transitionConstant * Real.sqrt
          (finiteFixedLocalJacobiDensity period hPeriod field.toField point) :=
      fixedAtlasHolonomicDensityRoot_le_finiteFixedLocalJacobiRoot
        period hPeriod field.toField point
    _ ≤ transitionConstant *
        (domination.constant *
          staticScalarJacobiDensityRoot period hPeriod data field point) :=
      mul_le_mul_of_nonneg_left (domination.pointwise_bound field point)
        (norm_nonneg _)
    _ = (transitionConstant * domination.constant) *
        staticScalarJacobiDensityRoot period hPeriod data field point := by
      ring

/-- Unconditional fixed-atlas/graph equivalence plus the exact conditional
status of the historical bridge. -/
theorem fixed_atlas_holonomic_density_equivalence4D_closure
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    finiteFixedLocalJacobiDensity period hPeriod field point ≤
        fixedAtlasToGraphDensityConstant period hPeriod *
          fixedAtlasHolonomicDensity period hPeriod field point ∧
      fixedAtlasHolonomicDensity period hPeriod field point ≤
        graphToFixedAtlasDensityConstant period hPeriod *
          finiteFixedLocalJacobiDensity period hPeriod field point :=
  ⟨finiteFixedLocalJacobiDensity_le_fixedAtlasHolonomicDensity
      period hPeriod field point,
    fixedAtlasHolonomicDensity_le_finiteFixedLocalJacobiDensity
      period hPeriod field point⟩

end

end P0EFTJanusMappingTorusFixedAtlasHolonomicDensityEquivalence4D
end JanusFormal
