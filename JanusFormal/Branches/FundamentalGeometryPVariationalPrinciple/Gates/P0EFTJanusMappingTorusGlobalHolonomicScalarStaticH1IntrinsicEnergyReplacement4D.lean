import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1IntrinsicPatchCoordinates4D

/-!
# Intrinsic fixed-patch replacement for the static scalar H1 energy

The raw holonomic density uses `chartAt point`; its target orthonormal basis is
chosen pointwise and Mathlib supplies no continuity for that choice.  A finite
fixed-chart cover therefore cannot prove continuity of the raw diagonal.

This gate takes the honest alternative route.  It weights the already proved
fixed-trivialization jet density by a positive intrinsic scalar depending only
on the smooth metric volume and mass.  The resulting density is uniformly
equivalent to the fixed-local density on the compact D8 quotient and gives an
unconditional graph ellipticity statement.  This is an alternative energy
density, not a proof that the historical raw `chartAt point` density has the
same regularity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1IntrinsicEnergyReplacement4D

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
open P0EFTJanusMappingTorusAutomaticScalarIntegrability4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1UniformEllipticity4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FixedLocalEnergyReduction4D

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

/-- Positive intrinsic weight.  The leading one makes its lower bound
independent of all chart choices. -/
def intrinsicFixedPatchWeight
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  1 + diagonalMetricVolumeDensity period hPeriod
      data.formData.magnitude point * min data.formData.massSquared 1

theorem intrinsicFixedPatchWeight_continuous
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    Continuous (intrinsicFixedPatchWeight period hPeriod data) := by
  exact continuous_const.add
    ((diagonalMetricVolumeDensity_continuous period hPeriod
      data.formData.magnitude).mul continuous_const)

theorem intrinsicFixedPatchWeight_one_le
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    1 ≤ intrinsicFixedPatchWeight period hPeriod data point := by
  unfold intrinsicFixedPatchWeight
  exact le_add_of_nonneg_right
    (mul_nonneg
      (diagonalMetricVolumeDensity_pos period hPeriod data point).le
      (le_min data.massSquared_pos.le zero_le_one))

theorem intrinsicFixedPatchWeight_pos
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    0 < intrinsicFixedPatchWeight period hPeriod data point :=
  zero_lt_one.trans_le
    (intrinsicFixedPatchWeight_one_le period hPeriod data point)

/-- Intrinsic weighted replacement for the raw variable-chart density. -/
def intrinsicFixedPatchJacobiDensity
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) : Real :=
  intrinsicFixedPatchWeight period hPeriod data point *
    finiteFixedLocalJacobiDensity period hPeriod field.toField point

theorem intrinsicFixedPatchJacobiDensity_nonneg
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) :
    0 ≤ intrinsicFixedPatchJacobiDensity period hPeriod data field point :=
  mul_nonneg
    (intrinsicFixedPatchWeight_pos period hPeriod data point).le
    (finiteFixedLocalJacobiDensity_nonneg period hPeriod field.toField point)

/-- Its nonnegative pointwise energy root. -/
def intrinsicFixedPatchJacobiDensityRoot
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) : Real :=
  Real.sqrt
    (intrinsicFixedPatchJacobiDensity period hPeriod data field point)

/-- The unweighted fixed-patch density is pointwise dominated with constant
one by the intrinsic weighted replacement. -/
theorem finiteFixedLocalJacobiDensity_le_intrinsic
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) :
    finiteFixedLocalJacobiDensity period hPeriod field.toField point ≤
      intrinsicFixedPatchJacobiDensity period hPeriod data field point := by
  unfold intrinsicFixedPatchJacobiDensity
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (intrinsicFixedPatchWeight_one_le period hPeriod data point)
    (finiteFixedLocalJacobiDensity_nonneg period hPeriod field.toField point)

theorem finiteFixedLocalJacobiRoot_le_intrinsicRoot
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) :
    Real.sqrt
        (finiteFixedLocalJacobiDensity period hPeriod field.toField point) ≤
      intrinsicFixedPatchJacobiDensityRoot period hPeriod data field point := by
  exact Real.sqrt_le_sqrt
    (finiteFixedLocalJacobiDensity_le_intrinsic
      period hPeriod data field point)

/-- The fixed-patch density is exactly the square of the implemented graph
jet norm. -/
theorem smoothFirstJet_norm_eq_finiteFixedLocalJacobiRoot
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    ‖smoothFirstJet period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field point‖ =
      Real.sqrt (finiteFixedLocalJacobiDensity period hPeriod field point) := by
  rw [finiteFixedLocalJacobiDensity,
    Real.sqrt_sq (norm_nonneg _),
    smoothFirstJet_norm_eq_finiteFixedLocalFirstJet]

/-- Uniform two-sided density equivalence. -/
structure IntrinsicFixedPatchDensityEquivalence
    (data : PositiveStaticGlobalScalarData period hPeriod) where
  upper : Real
  upper_pos : 0 < upper
  lower_density : ∀
      (field : StaticGlobalScalarTest period hPeriod data)
      (point : EffectiveQuotient period hPeriod),
    finiteFixedLocalJacobiDensity period hPeriod field.toField point ≤
      intrinsicFixedPatchJacobiDensity period hPeriod data field point
  upper_density : ∀
      (field : StaticGlobalScalarTest period hPeriod data)
      (point : EffectiveQuotient period hPeriod),
    intrinsicFixedPatchJacobiDensity period hPeriod data field point ≤
      upper * finiteFixedLocalJacobiDensity period hPeriod field.toField point

/-- Compactness gives the reverse uniform comparison as well. -/
noncomputable def intrinsicFixedPatchDensityEquivalence
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    IntrinsicFixedPatchDensityEquivalence period hPeriod data := by
  have hBounded := isCompact_univ.bddAbove_image
    (intrinsicFixedPatchWeight_continuous period hPeriod data).norm.continuousOn
  let normUpper := Classical.choose hBounded
  have hNormUpper := Classical.choose_spec hBounded
  let upper := |normUpper| + 1
  have hUpperPos : 0 < upper := by
    dsimp only [upper]
    positivity
  refine
    { upper := upper
      upper_pos := hUpperPos
      lower_density := finiteFixedLocalJacobiDensity_le_intrinsic
        period hPeriod data
      upper_density := ?_ }
  intro field point
  have hNorm :
      ‖intrinsicFixedPatchWeight period hPeriod data point‖ ≤ normUpper :=
    hNormUpper ⟨point, Set.mem_univ point, rfl⟩
  have hWeightUpper :
      intrinsicFixedPatchWeight period hPeriod data point ≤ upper := by
    calc
      intrinsicFixedPatchWeight period hPeriod data point ≤
          ‖intrinsicFixedPatchWeight period hPeriod data point‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      _ ≤ normUpper := hNorm
      _ ≤ upper := by
        dsimp only [upper]
        linarith [le_abs_self normUpper]
  unfold intrinsicFixedPatchJacobiDensity
  exact mul_le_mul_of_nonneg_right hWeightUpper
    (finiteFixedLocalJacobiDensity_nonneg period hPeriod field.toField point)

/-- Energy domination contract for the intrinsic replacement density. -/
structure StaticScalarIntrinsicFixedLocalEnergyDomination
    (data : PositiveStaticGlobalScalarData period hPeriod) where
  constant : Real
  constant_nonneg : 0 ≤ constant
  pointwise_bound : ∀
      (field : StaticGlobalScalarTest period hPeriod data)
      (point : EffectiveQuotient period hPeriod),
    Real.sqrt
        (finiteFixedLocalJacobiDensity period hPeriod field.toField point) ≤
      constant *
        intrinsicFixedPatchJacobiDensityRoot period hPeriod data field point

/-- The intrinsic replacement closes fixed-local energy domination
unconditionally, with constant one. -/
def intrinsicFixedLocalEnergyDomination
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    StaticScalarIntrinsicFixedLocalEnergyDomination period hPeriod data where
  constant := 1
  constant_nonneg := zero_le_one
  pointwise_bound field point := by
    simpa using finiteFixedLocalJacobiRoot_le_intrinsicRoot
      period hPeriod data field point

/-- Uniform graph ellipticity contract for the intrinsic replacement. -/
structure StaticScalarIntrinsicUniformGraphEllipticity
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) where
  constant : Real
  constant_nonneg : 0 ≤ constant
  pointwise_bound : ∀
      (field : StaticGlobalScalarTest period hPeriod data)
      (point : EffectiveQuotient period hPeriod),
    ‖smoothFirstJet period hPeriod Real frame field.toField point‖ ≤
      constant *
        intrinsicFixedPatchJacobiDensityRoot period hPeriod data field point

/-- Unconditional pointwise ellipticity for the implemented finite smooth
frame and the intrinsic energy, again with constant one. -/
def intrinsicFixedPatchUniformGraphEllipticity
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    StaticScalarIntrinsicUniformGraphEllipticity period hPeriod data
      (finiteSmoothTangentFrame period hPeriod) where
  constant := 1
  constant_nonneg := zero_le_one
  pointwise_bound field point := by
    rw [one_mul,
      smoothFirstJet_norm_eq_finiteFixedLocalJacobiRoot]
    exact finiteFixedLocalJacobiRoot_le_intrinsicRoot
      period hPeriod data field point

theorem intrinsic_fixed_patch_energy_replacement4D_closure
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    Nonempty (IntrinsicFixedPatchDensityEquivalence period hPeriod data) ∧
      Nonempty
        (StaticScalarIntrinsicFixedLocalEnergyDomination
          period hPeriod data) ∧
      Nonempty
        (StaticScalarIntrinsicUniformGraphEllipticity period hPeriod data
          (finiteSmoothTangentFrame period hPeriod)) :=
  ⟨⟨intrinsicFixedPatchDensityEquivalence period hPeriod data⟩,
    ⟨intrinsicFixedLocalEnergyDomination period hPeriod data⟩,
    ⟨intrinsicFixedPatchUniformGraphEllipticity period hPeriod data⟩⟩

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1IntrinsicEnergyReplacement4D
end JanusFormal
