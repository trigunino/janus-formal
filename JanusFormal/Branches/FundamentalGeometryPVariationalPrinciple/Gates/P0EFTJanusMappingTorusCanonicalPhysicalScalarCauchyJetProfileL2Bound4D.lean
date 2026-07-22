import Mathlib.MeasureTheory.Integral.Prod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetBulkL2Reduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetNormalCalculus4D

/-!
# Bulk `L²` bound for the explicit physical Cauchy jet

For

`E(g,h)(x,ν) = a(ν) g(x) + b(ν) h(x)`,

the elementary inequality

`|E|² ≤ 2 a² |g|² + 2 b² |h|²`

separates the boundary and normal variables.  Fubini then gives a bound solely
in terms of the two fixed profile moments

`A = ∫ a²`, `B = ∫ b²`

and the boundary `L²` pair norm.  Thus the bulk component of the graph estimate
is automatic once the two one-dimensional profile squares are integrable.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetProfileL2Bound4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetNormalCalculus4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGraphBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetBulkL2Reduction4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)

/-- Integrability of the two fixed normal profile squares. -/
structure CanonicalLatitudeCauchyJetProfileIntegrabilityData where
  value_sq_integrable : Integrable
    (fun normal => canonicalLatitudeCauchyValueProfile normal ^ 2)
    canonicalLatitudeCauchyJetNormalMeasure
  normal_sq_integrable : Integrable
    (fun normal => canonicalLatitudeCauchyNormalProfile normal ^ 2)
    canonicalLatitudeCauchyJetNormalMeasure

namespace CanonicalLatitudeCauchyJetProfileIntegrabilityData

/-- Squared `L²` moment of the value profile. -/
def valueMoment
    (profile : CanonicalLatitudeCauchyJetProfileIntegrabilityData) : Real :=
  ∫ normal, canonicalLatitudeCauchyValueProfile normal ^ 2
    ∂canonicalLatitudeCauchyJetNormalMeasure

/-- Squared `L²` moment of the normal profile. -/
def normalMoment
    (profile : CanonicalLatitudeCauchyJetProfileIntegrabilityData) : Real :=
  ∫ normal, canonicalLatitudeCauchyNormalProfile normal ^ 2
    ∂canonicalLatitudeCauchyJetNormalMeasure

/-- The value-profile moment is nonnegative. -/
theorem valueMoment_nonnegative
    (profile : CanonicalLatitudeCauchyJetProfileIntegrabilityData) :
    0 ≤ profile.valueMoment := by
  unfold valueMoment
  exact integral_nonneg fun _ => sq_nonneg _

/-- The normal-profile moment is nonnegative. -/
theorem normalMoment_nonnegative
    (profile : CanonicalLatitudeCauchyJetProfileIntegrabilityData) :
    0 ≤ profile.normalMoment := by
  unfold normalMoment
  exact integral_nonneg fun _ => sq_nonneg _

/-- Common bulk extension constant. -/
def extensionConstant
    (profile : CanonicalLatitudeCauchyJetProfileIntegrabilityData) : Real :=
  Real.sqrt (2 * (profile.valueMoment + profile.normalMoment))

/-- Nonnegativity of the bulk extension constant. -/
theorem extensionConstant_nonnegative
    (profile : CanonicalLatitudeCauchyJetProfileIntegrabilityData) :
    0 ≤ profile.extensionConstant :=
  Real.sqrt_nonneg _

/-- Square of the common bulk extension constant. -/
theorem extensionConstant_sq
    (profile : CanonicalLatitudeCauchyJetProfileIntegrabilityData) :
    profile.extensionConstant ^ 2 =
      2 * (profile.valueMoment + profile.normalMoment) := by
  unfold extensionConstant
  rw [Real.sq_sqrt]
  exact mul_nonneg (by norm_num)
    (add_nonneg profile.valueMoment_nonnegative
      profile.normalMoment_nonnegative)

/-- Pointwise separation of the two Cauchy components. -/
theorem localExtension_sq_le
    (profile : CanonicalLatitudeCauchyJetProfileIntegrabilityData)
    (value normal : Real) (normalCoordinate : Real) :
    (canonicalLatitudeCauchyValueProfile normalCoordinate * value +
        canonicalLatitudeCauchyNormalProfile normalCoordinate * normal) ^ 2 ≤
      2 * canonicalLatitudeCauchyValueProfile normalCoordinate ^ 2 * value ^ 2 +
        2 * canonicalLatitudeCauchyNormalProfile normalCoordinate ^ 2 *
          normal ^ 2 := by
  nlinarith [sq_nonneg
    (canonicalLatitudeCauchyValueProfile normalCoordinate * value -
      canonicalLatitudeCauchyNormalProfile normalCoordinate * normal)]

/-- One-dimensional integral estimate at a fixed boundary base point. -/
theorem normalIntegral_bound
    (profile : CanonicalLatitudeCauchyJetProfileIntegrabilityData)
    (value normal : Real) :
    (∫ normalCoordinate,
      (canonicalLatitudeCauchyValueProfile normalCoordinate * value +
        canonicalLatitudeCauchyNormalProfile normalCoordinate * normal) ^ 2
      ∂canonicalLatitudeCauchyJetNormalMeasure) ≤
      2 * profile.valueMoment * value ^ 2 +
        2 * profile.normalMoment * normal ^ 2 := by
  have hRightIntegrable : Integrable
      (fun normalCoordinate =>
        2 * canonicalLatitudeCauchyValueProfile normalCoordinate ^ 2 * value ^ 2 +
          2 * canonicalLatitudeCauchyNormalProfile normalCoordinate ^ 2 *
            normal ^ 2)
      canonicalLatitudeCauchyJetNormalMeasure :=
    ((profile.value_sq_integrable.const_mul
      (2 * value ^ 2)).add
      (profile.normal_sq_integrable.const_mul (2 * normal ^ 2))).congr
        (Filter.Eventually.of_forall fun normalCoordinate => by ring)
  have hLeftIntegrable : Integrable
      (fun normalCoordinate =>
        (canonicalLatitudeCauchyValueProfile normalCoordinate * value +
          canonicalLatitudeCauchyNormalProfile normalCoordinate * normal) ^ 2)
      canonicalLatitudeCauchyJetNormalMeasure := by
    exact hRightIntegrable.mono'
      (((canonicalLatitudeCauchyValueProfile_contDiff.continuous.mul
          continuous_const).add
        (canonicalLatitudeCauchyNormalProfile_contDiff.continuous.mul
          continuous_const)).pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun normalCoordinate => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
          Real.norm_eq_abs, abs_of_nonneg]
        · exact profile.localExtension_sq_le value normal normalCoordinate
        · positivity)
  calc
    (∫ normalCoordinate,
      (canonicalLatitudeCauchyValueProfile normalCoordinate * value +
        canonicalLatitudeCauchyNormalProfile normalCoordinate * normal) ^ 2
      ∂canonicalLatitudeCauchyJetNormalMeasure) ≤
      ∫ normalCoordinate,
        (2 * canonicalLatitudeCauchyValueProfile normalCoordinate ^ 2 * value ^ 2 +
          2 * canonicalLatitudeCauchyNormalProfile normalCoordinate ^ 2 *
            normal ^ 2)
        ∂canonicalLatitudeCauchyJetNormalMeasure := by
      exact integral_mono hLeftIntegrable hRightIntegrable
        (fun normalCoordinate => profile.localExtension_sq_le
          value normal normalCoordinate)
    _ = 2 * profile.valueMoment * value ^ 2 +
        2 * profile.normalMoment * normal ^ 2 := by
      rw [integral_add]
      · rw [integral_const_mul, integral_const_mul]
        unfold valueMoment normalMoment
        ring
      · exact profile.value_sq_integrable.const_mul (2 * value ^ 2)
      · exact profile.normal_sq_integrable.const_mul (2 * normal ^ 2)

end CanonicalLatitudeCauchyJetProfileIntegrabilityData

namespace CanonicalPhysicalScalarCauchyJetGeometricData

/-- Boundary value representative has the expected squared `L²` integral. -/
theorem valueRepresentative_integral_sq_eq_norm_sq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (value : ValueCore) :
    (∫ base,
      geometric.boundaryCore.valueRepresentative value base ^ 2
      ∂canonicalLatitudeBaseMeasure period) =
      ‖geometric.boundaryCore.valueEmbedding value‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [geometric.boundaryCore.valueEmbedding_ae value]
    with base hBase
  rw [hBase]
  simp [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Boundary normal representative has the expected squared `L²` integral. -/
theorem normalRepresentative_integral_sq_eq_norm_sq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (normal : NormalCore) :
    (∫ base,
      geometric.boundaryCore.normalRepresentative normal base ^ 2
      ∂canonicalLatitudeBaseMeasure period) =
      ‖geometric.boundaryCore.normalEmbedding normal‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [geometric.boundaryCore.normalEmbedding_ae normal]
    with base hBase
  rw [hBase]
  simp [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Product-integral estimate for the explicit Cauchy jet. -/
theorem localProductExtension_integral_bound
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (profile : CanonicalLatitudeCauchyJetProfileIntegrabilityData)
    (data : ValueCore × NormalCore) :
    (∫ parameter,
      geometric.localProductExtension data parameter ^ 2
      ∂canonicalLatitudeCauchyJetProductMeasure period) ≤
      profile.extensionConstant ^ 2 *
        ‖geometric.boundaryCoreEmbedding data‖ ^ 2 := by
  let valueNorm := ‖geometric.boundaryCore.valueEmbedding data.1‖
  let normalNorm := ‖geometric.boundaryCore.normalEmbedding data.2‖
  let boundaryNorm := ‖geometric.boundaryCoreEmbedding data‖
  have hValueBoundary : valueNorm ≤ boundaryNorm := by
    change ‖geometric.boundaryCore.valueEmbedding data.1‖ ≤
      max ‖geometric.boundaryCore.valueEmbedding data.1‖
        ‖geometric.boundaryCore.normalEmbedding data.2‖
    exact le_max_left _ _
  have hNormalBoundary : normalNorm ≤ boundaryNorm := by
    change ‖geometric.boundaryCore.normalEmbedding data.2‖ ≤
      max ‖geometric.boundaryCore.valueEmbedding data.1‖
        ‖geometric.boundaryCore.normalEmbedding data.2‖
    exact le_max_right _ _
  have hValueSq : valueNorm ^ 2 ≤ boundaryNorm ^ 2 := by
    nlinarith [norm_nonneg (geometric.boundaryCore.valueEmbedding data.1),
      norm_nonneg (geometric.boundaryCoreEmbedding data)]
  have hNormalSq : normalNorm ^ 2 ≤ boundaryNorm ^ 2 := by
    nlinarith [norm_nonneg (geometric.boundaryCore.normalEmbedding data.2),
      norm_nonneg (geometric.boundaryCoreEmbedding data)]
  unfold canonicalLatitudeCauchyJetProductMeasure
  rw [integral_prod]
  · calc
      (∫ base,
        ∫ normalCoordinate,
          geometric.localProductExtension data (base, normalCoordinate) ^ 2
          ∂canonicalLatitudeCauchyJetNormalMeasure
        ∂canonicalLatitudeBaseMeasure period) ≤
        ∫ base,
          (2 * profile.valueMoment *
              geometric.boundaryCore.valueRepresentative data.1 base ^ 2 +
            2 * profile.normalMoment *
              geometric.boundaryCore.normalRepresentative data.2 base ^ 2)
          ∂canonicalLatitudeBaseMeasure period := by
        apply integral_mono_ae
        · exact (integrable_prod_iff
            (by fun_prop : AEStronglyMeasurable
              (fun parameter : CanonicalLatitudeBase × Real =>
                geometric.localProductExtension data parameter ^ 2)
              ((canonicalLatitudeBaseMeasure period).prod
                canonicalLatitudeCauchyJetNormalMeasure))).1
              (by infer_instance) |>.2
        · exact
            ((geometric.boundaryCore.valueRepresentative_memLp data.1).integrable_sq.const_mul
                (2 * profile.valueMoment)).add
              ((geometric.boundaryCore.normalRepresentative_memLp data.2).integrable_sq.const_mul
                (2 * profile.normalMoment))
        · filter_upwards [] with base
          exact profile.normalIntegral_bound
            (geometric.boundaryCore.valueRepresentative data.1 base)
            (geometric.boundaryCore.normalRepresentative data.2 base)
      _ = 2 * profile.valueMoment * valueNorm ^ 2 +
          2 * profile.normalMoment * normalNorm ^ 2 := by
        rw [integral_add, integral_const_mul, integral_const_mul,
          geometric.valueRepresentative_integral_sq_eq_norm_sq,
          geometric.normalRepresentative_integral_sq_eq_norm_sq]
      _ ≤ 2 * profile.valueMoment * boundaryNorm ^ 2 +
          2 * profile.normalMoment * boundaryNorm ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hValueSq
            (mul_nonneg (by norm_num) profile.valueMoment_nonnegative))
          (mul_le_mul_of_nonneg_left hNormalSq
            (mul_nonneg (by norm_num) profile.normalMoment_nonnegative))
      _ = profile.extensionConstant ^ 2 * boundaryNorm ^ 2 := by
        rw [profile.extensionConstant_sq]
        ring
  · exact (by
      apply integrable_prod_iff.mpr
      refine ⟨?_, ?_⟩
      · filter_upwards [] with base
        exact (profile.value_sq_integrable.const_mul
          (2 * geometric.boundaryCore.valueRepresentative data.1 base ^ 2)).add
          (profile.normal_sq_integrable.const_mul
            (2 * geometric.boundaryCore.normalRepresentative data.2 base ^ 2))
          |>.mono'
            (by fun_prop)
            (Filter.Eventually.of_forall fun normalCoordinate => by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
                Real.norm_eq_abs, abs_of_nonneg]
              · exact profile.localExtension_sq_le _ _ normalCoordinate
              · positivity)
      · exact
          ((geometric.boundaryCore.valueRepresentative_memLp data.1).integrable_sq.const_mul
              (2 * profile.valueMoment)).add
            ((geometric.boundaryCore.normalRepresentative_memLp data.2).integrable_sq.const_mul
              (2 * profile.normalMoment))
          |>.mono'
            (by fun_prop)
            (Filter.Eventually.of_forall fun base => by
              rw [Real.norm_eq_abs, abs_of_nonneg]
              · exact profile.normalIntegral_bound _ _
              · positivity))

/-- Canonical product-`L²` estimate package generated by the profile moments. -/
def cauchyJetProductL2EstimateData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (profile : CanonicalLatitudeCauchyJetProfileIntegrabilityData) :
    geometric.CauchyJetProductL2EstimateData period hPeriod where
  constant := profile.extensionConstant
  nonnegative := profile.extensionConstant_nonnegative
  product_bound_sq := geometric.localProductExtension_integral_bound profile

/-- Bulk `L²` component of the explicit graph bound. -/
theorem inclusion_bound_sq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (profile : CanonicalLatitudeCauchyJetProfileIntegrabilityData)
    (data : ValueCore × NormalCore) :
    ‖geometric.greenCore.core.inclusion (geometric.extension data)‖ ^ 2 ≤
      profile.extensionConstant ^ 2 *
        ‖geometric.boundaryCoreEmbedding data‖ ^ 2 :=
  (geometric.cauchyJetProductL2EstimateData profile).inclusion_bound_sq data

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetProfileL2Bound4D
end JanusFormal
