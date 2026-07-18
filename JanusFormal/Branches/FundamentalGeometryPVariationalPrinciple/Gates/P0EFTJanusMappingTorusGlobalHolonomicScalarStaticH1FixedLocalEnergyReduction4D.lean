import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1UniformEllipticity4D

/-!
# Fixed-local reduction of the finite-frame H1 graph norm

The generators of `finiteSmoothTangentFrame` are partition weights times
vectors from finitely many fixed tangent trivializations.  Consequently its
graph derivatives are exactly localized fixed-frame covector components; no
raw preferred coordinate of a tangent-bundle section is needed.

This closes the graph side unconditionally.  The remaining comparison with
the existing holonomic Jacobi density is isolated separately: that density is
defined using the raw `tangentCoordinate` vectors at `chartAt point`, so its
domination of the fixed-local density still requires a uniform transition
bound (or an intrinsic reformulation of the action density).
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FixedLocalEnergyReduction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalHolonomicScalar4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1UniformEllipticity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- A covector component in the frame of one fixed tangent trivialization. -/
def finiteFixedLocalCovectorComponent
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod) : Real :=
  scalarDifferential period hPeriod field point
    (finiteTangentGeneratorLocalVector period hPeriod
      index.1 index.2 point)

/-- The same component localized by the partition weight used in the actual
global generator.  The local frame is therefore relevant only on its fixed
trivialization patch. -/
def finiteLocalizedCovectorComponent
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod) : Real :=
  finiteTangentGeneratorWeight period hPeriod index.1 point *
    finiteFixedLocalCovectorComponent period hPeriod field point index

/-- Value plus all partition-localized fixed-trivialization components. -/
def finiteFixedLocalFirstJet
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    Real × (FiniteTangentGeneratorIndex period hPeriod → Real) :=
  (field point, finiteLocalizedCovectorComponent period hPeriod field point)

/-- Each implemented graph derivative is exactly one localized component. -/
theorem finiteFrameDerivative_eq_localizedComponent
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod) :
    frameDerivative period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field point
          (finiteTangentGeneratorIndexEquivFin period hPeriod index) =
      finiteLocalizedCovectorComponent period hPeriod field point index := by
  rw [frameDerivative_eq_mfderiv]
  change scalarDifferential period hPeriod field point
      ((finiteSmoothTangentFrame period hPeriod).vectorAt point
        (finiteTangentGeneratorIndexEquivFin period hPeriod index)) = _
  rw [finiteSmoothTangentFrame_vectorAt_generator, map_smul]
  rfl

/-- The actual finite-frame graph norm is controlled unconditionally by its
fixed-local representation. -/
theorem smoothFirstJet_norm_le_finiteFixedLocalFirstJet
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    ‖smoothFirstJet period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field point‖ ≤
      ‖finiteFixedLocalFirstJet period hPeriod field point‖ := by
  have hDerivative :
      ‖frameDerivative period hPeriod Real
          (finiteSmoothTangentFrame period hPeriod) field point‖ ≤
        ‖finiteLocalizedCovectorComponent period hPeriod field point‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro frameIndex
    let index :=
      (finiteTangentGeneratorIndexEquivFin period hPeriod).symm frameIndex
    have hFrameIndex :
        finiteTangentGeneratorIndexEquivFin period hPeriod index = frameIndex :=
      (finiteTangentGeneratorIndexEquivFin period hPeriod).apply_symm_apply
        frameIndex
    rw [← hFrameIndex,
      finiteFrameDerivative_eq_localizedComponent period hPeriod]
    exact norm_le_pi_norm
      (finiteLocalizedCovectorComponent period hPeriod field point) index
  rw [Prod.norm_mk, Prod.norm_mk]
  exact max_le_max le_rfl hDerivative

/-- Reindexing by the generator enumeration loses no information: the two
pointwise graph norms are equal. -/
theorem smoothFirstJet_norm_eq_finiteFixedLocalFirstJet
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    ‖smoothFirstJet period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field point‖ =
      ‖finiteFixedLocalFirstJet period hPeriod field point‖ := by
  apply le_antisymm
  · exact smoothFirstJet_norm_le_finiteFixedLocalFirstJet
      period hPeriod field point
  · have hDerivative :
        ‖finiteLocalizedCovectorComponent period hPeriod field point‖ ≤
          ‖frameDerivative period hPeriod Real
            (finiteSmoothTangentFrame period hPeriod) field point‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      intro index
      rw [← finiteFrameDerivative_eq_localizedComponent
        period hPeriod field point index]
      exact norm_le_pi_norm
        (frameDerivative period hPeriod Real
          (finiteSmoothTangentFrame period hPeriod) field point)
        (finiteTangentGeneratorIndexEquivFin period hPeriod index)
    rw [Prod.norm_mk, Prod.norm_mk]
    exact max_le_max le_rfl hDerivative

/-- Alternative positive density obtained entirely from the fixed local
trivializations used by the finite generator construction. -/
def finiteFixedLocalJacobiDensity
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ‖finiteFixedLocalFirstJet period hPeriod field point‖ ^ 2

theorem finiteFixedLocalJacobiDensity_nonneg
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    0 ≤ finiteFixedLocalJacobiDensity period hPeriod field point :=
  sq_nonneg _

/-- The graph side is elliptic with constant one for the fixed-local density,
without any preferred-chart regularity assumption. -/
theorem smoothFirstJet_norm_le_finiteFixedLocalJacobiRoot
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    ‖smoothFirstJet period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field point‖ ≤
      Real.sqrt (finiteFixedLocalJacobiDensity period hPeriod field point) := by
  rw [finiteFixedLocalJacobiDensity, Real.sqrt_sq (norm_nonneg _)]
  exact smoothFirstJet_norm_le_finiteFixedLocalFirstJet
    period hPeriod field point

/-- Exact remaining energy-side contract.  It compares the localized
fixed-trivialization density with the current raw holonomic Jacobi density. -/
structure StaticScalarFixedLocalEnergyDomination
    (data : PositiveStaticGlobalScalarData period hPeriod) where
  constant : Real
  constant_nonneg : 0 ≤ constant
  pointwise_bound : ∀
      (field : StaticGlobalScalarTest period hPeriod data)
      (point : EffectiveQuotient period hPeriod),
    Real.sqrt
        (finiteFixedLocalJacobiDensity period hPeriod field.toField point) ≤
      constant *
        staticScalarJacobiDensityRoot period hPeriod data field point

/-- Once the energy-side comparison is supplied, the existing H1 bridge
follows with no further frame or chart hypothesis. -/
def StaticScalarFixedLocalEnergyDomination.toUniformGraphEllipticity
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (domination : StaticScalarFixedLocalEnergyDomination
      period hPeriod data) :
    StaticScalarUniformGraphEllipticity period hPeriod data
      (finiteSmoothTangentFrame period hPeriod) where
  constant := domination.constant
  constant_nonneg := domination.constant_nonneg
  pointwise_bound field point :=
    (smoothFirstJet_norm_le_finiteFixedLocalJacobiRoot period hPeriod
      field.toField point).trans (domination.pointwise_bound field point)

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FixedLocalEnergyReduction4D
end JanusFormal
