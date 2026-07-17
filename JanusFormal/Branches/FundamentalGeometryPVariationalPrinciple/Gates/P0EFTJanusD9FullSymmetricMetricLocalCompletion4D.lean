import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9MatterSquaredSpinorCoordinateCompletion4D

/-!
# D9 full symmetric metric completion at local-field level

This gate supplies the six independent coefficients of a local symmetric
three-metric variation and projects them explicitly onto D9's metric slot.
It closes the off-diagonal coefficient residual pointwise while preserving
the already constructed normal, gauge, ghost and squared-spinor fields.

The added coefficients are independent local data.  No claim is made here
that they arise from a tangent vector to the global Program-P action.
-/

namespace JanusFormal
namespace P0EFTJanusD9FullSymmetricMetricLocalCompletion4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusD9MatterSquaredSpinorCoordinateCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev ThroatCover := MappingTorusCover (throatData period hPeriod)

/-- Six independent coefficients of a local symmetric three-metric
variation.  This is local coefficient data, not a global action tangent. -/
@[ext] structure D9FullSymmetricMetricVariation where
  xx : Real
  yy : Real
  zz : Real
  xy : Real
  xz : Real
  yz : Real

/-- Explicit projection of the six metric-variation coefficients onto D9's
symmetric-tensor slot. -/
def d9FullMetricProjection
    (variation : D9FullSymmetricMetricVariation) : SymmetricTensor3 where
  xx := variation.xx
  yy := variation.yy
  zz := variation.zz
  xy := variation.xy
  xz := variation.xz
  yz := variation.yz

/-- Canonical coefficient lift of a D9 symmetric tensor. -/
def d9FullMetricLift
    (tensor : SymmetricTensor3) : D9FullSymmetricMetricVariation where
  xx := tensor.xx
  yy := tensor.yy
  zz := tensor.zz
  xy := tensor.xy
  xz := tensor.xz
  yz := tensor.yz

@[simp] theorem d9FullMetricProjection_lift
    (tensor : SymmetricTensor3) :
    d9FullMetricProjection (d9FullMetricLift tensor) = tensor := by
  rfl

/-- The local six-coefficient projection fills every D9 metric component,
including the three off-diagonal entries absent from the diagonal Program-P
variation. -/
theorem d9FullMetricProjection_surjective :
    Function.Surjective d9FullMetricProjection := by
  intro tensor
  exact ⟨d9FullMetricLift tensor, d9FullMetricProjection_lift tensor⟩

/-- Program-P supplies the non-metric coefficients while an independent
six-component local variation supplies the complete D9 metric slot. -/
structure D9CompleteLocalVariation where
  programVariation : IndependentFieldVariation period hPeriod
  metricVariation : D9FullSymmetricMetricVariation

/-- Assemble the complete local D9 field, retaining the geometric normal
section, gauge coefficient, geometric ghost and squared-spinor coordinate
from the existing bridge and replacing only its diagonal metric slot by the
full six-component local projection. -/
def d9LocalFieldWithFullSymmetricMetric
    (fields : IndependentFields period hPeriod)
    (variation : D9CompleteLocalVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (ghost : CInfinityThroatGhost period hPeriod) :
    CompleteLocalField D9SquaredSpinorCoordinateFiber :=
  let base := d9LocalFieldWithSquaredSpinorCoordinates period hPeriod fields
    variation.programVariation sector column point displacement anchor hPoint ghost
  { bosonic :=
      { normalMode := base.bosonic.normalMode
        gaugeOneForm := base.bosonic.gaugeOneForm
        metricPerturbation := d9FullMetricProjection variation.metricVariation }
    ghosts := base.ghosts
    spinor := base.spinor }

@[simp] theorem d9LocalFieldWithFullSymmetricMetric_metricPerturbation
    (fields : IndependentFields period hPeriod)
    (variation : D9CompleteLocalVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (ghost : CInfinityThroatGhost period hPeriod) :
    (d9LocalFieldWithFullSymmetricMetric period hPeriod fields variation
      sector column point displacement anchor hPoint ghost).bosonic.metricPerturbation =
        d9FullMetricProjection variation.metricVariation := rfl

/-- At fixed non-metric local data, the assembled complete field realizes
every D9 symmetric metric perturbation. -/
theorem d9LocalFieldWithFullSymmetricMetric_metric_surjective
    (fields : IndependentFields period hPeriod)
    (programVariation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (ghost : CInfinityThroatGhost period hPeriod) :
    Function.Surjective
      (fun metricVariation : D9FullSymmetricMetricVariation =>
        (d9LocalFieldWithFullSymmetricMetric period hPeriod fields
          { programVariation := programVariation
            metricVariation := metricVariation }
          sector column point displacement anchor hPoint ghost).bosonic.metricPerturbation) := by
  intro tensor
  exact ⟨d9FullMetricLift tensor, d9FullMetricProjection_lift tensor⟩

end
end P0EFTJanusD9FullSymmetricMetricLocalCompletion4D
end JanusFormal
