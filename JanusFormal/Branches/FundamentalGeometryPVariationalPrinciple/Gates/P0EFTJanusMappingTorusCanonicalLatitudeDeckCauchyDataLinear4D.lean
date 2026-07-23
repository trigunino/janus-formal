import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGlobalCandidate4D

/-!
# Linear structure of deck-compatible Cauchy data

Deck-periodic values and deck-antiperiodic normal data form a real vector space.
The local collar extension, its quotient descent, the field on the physical
tubular image and the global extension-by-zero candidate are all linear in these
data.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeDeckCauchyDataLinear4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCollarQuotient4D
open P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGlobalCandidate4D

variable (period : Real)

@[ext]
theorem CanonicalLatitudeDeckCauchyData.ext
    {first second : CanonicalLatitudeDeckCauchyData period}
    (hValue : first.value = second.value)
    (hNormal : first.normal = second.normal) : first = second := by
  cases first
  cases second
  simp_all

instance : Zero (CanonicalLatitudeDeckCauchyData period) where
  zero :=
    { value := fun _ => 0
      normal := fun _ => 0
      value_periodic := by intro base; rfl
      normal_antiperiodic := by intro base; simp }

instance : Add (CanonicalLatitudeDeckCauchyData period) where
  add first second :=
    { value := fun base => first.value base + second.value base
      normal := fun base => first.normal base + second.normal base
      value_periodic := by
        intro base
        change first.value (canonicalLatitudeBaseDeck period base) +
            second.value (canonicalLatitudeBaseDeck period base) =
          first.value base + second.value base
        rw [first.value_periodic, second.value_periodic]
      normal_antiperiodic := by
        intro base
        change first.normal (canonicalLatitudeBaseDeck period base) +
            second.normal (canonicalLatitudeBaseDeck period base) =
          -(first.normal base + second.normal base)
        rw [first.normal_antiperiodic, second.normal_antiperiodic]
        ring }

instance : Neg (CanonicalLatitudeDeckCauchyData period) where
  neg data :=
    { value := fun base => -data.value base
      normal := fun base => -data.normal base
      value_periodic := by
        intro base
        change -data.value (canonicalLatitudeBaseDeck period base) =
          -data.value base
        rw [data.value_periodic]
      normal_antiperiodic := by
        intro base
        change -data.normal (canonicalLatitudeBaseDeck period base) =
          -(-data.normal base)
        rw [data.normal_antiperiodic] }

instance : AddCommGroup (CanonicalLatitudeDeckCauchyData period) where
  add_assoc := by
    intro first second third
    apply CanonicalLatitudeDeckCauchyData.ext <;> funext base <;>
      exact add_assoc _ _ _
  zero_add := by
    intro data
    apply CanonicalLatitudeDeckCauchyData.ext <;> funext base <;>
      exact zero_add _
  add_zero := by
    intro data
    apply CanonicalLatitudeDeckCauchyData.ext <;> funext base <;>
      exact add_zero _
  nsmul := nsmulRec
  add_comm := by
    intro first second
    apply CanonicalLatitudeDeckCauchyData.ext <;> funext base <;>
      exact add_comm _ _
  neg_add_cancel := by
    intro data
    apply CanonicalLatitudeDeckCauchyData.ext <;> funext base <;>
      exact neg_add_cancel _
  sub_eq_add_neg := by
    intro first second
    rfl
  zsmul := zsmulRec

instance : SMul Real (CanonicalLatitudeDeckCauchyData period) where
  smul scalar data :=
    { value := fun base => scalar * data.value base
      normal := fun base => scalar * data.normal base
      value_periodic := by
        intro base
        change scalar * data.value (canonicalLatitudeBaseDeck period base) =
          scalar * data.value base
        rw [data.value_periodic]
      normal_antiperiodic := by
        intro base
        change scalar * data.normal (canonicalLatitudeBaseDeck period base) =
          -(scalar * data.normal base)
        rw [data.normal_antiperiodic]
        ring }

instance : Module Real (CanonicalLatitudeDeckCauchyData period) where
  one_smul := by
    intro data
    apply CanonicalLatitudeDeckCauchyData.ext <;> funext base <;>
      exact one_mul _
  mul_smul := by
    intro first second data
    apply CanonicalLatitudeDeckCauchyData.ext <;> funext base <;>
      exact mul_assoc _ _ _
  smul_add := by
    intro scalar first second
    apply CanonicalLatitudeDeckCauchyData.ext <;> funext base <;>
      exact mul_add _ _ _
  smul_zero := by
    intro scalar
    apply CanonicalLatitudeDeckCauchyData.ext <;> funext base <;>
      exact mul_zero _
  add_smul := by
    intro first second data
    apply CanonicalLatitudeDeckCauchyData.ext <;> funext base <;>
      exact add_mul _ _ _
  zero_smul := by
    intro data
    apply CanonicalLatitudeDeckCauchyData.ext <;> funext base <;>
      exact zero_mul _

namespace CanonicalLatitudeDeckCauchyData

/-- The local collar extension is linear in deck Cauchy data. -/
def localExtensionLinearMap :
    CanonicalLatitudeDeckCauchyData period →ₗ[Real]
      (CanonicalLatitudeCauchyCollar period → Real) where
  toFun := CanonicalLatitudeDeckCauchyData.localExtension
  map_add' first second := by
    funext parameter
    change canonicalLatitudeCauchyValueProfile parameter.2 *
          (first.value parameter.1 + second.value parameter.1) +
        canonicalLatitudeCauchyNormalProfile parameter.2 *
          (first.normal parameter.1 + second.normal parameter.1) =
      (canonicalLatitudeCauchyValueProfile parameter.2 * first.value parameter.1 +
          canonicalLatitudeCauchyNormalProfile parameter.2 * first.normal parameter.1) +
        (canonicalLatitudeCauchyValueProfile parameter.2 * second.value parameter.1 +
          canonicalLatitudeCauchyNormalProfile parameter.2 * second.normal parameter.1)
    ring
  map_smul' scalar data := by
    funext parameter
    change canonicalLatitudeCauchyValueProfile parameter.2 *
          (scalar * data.value parameter.1) +
        canonicalLatitudeCauchyNormalProfile parameter.2 *
          (scalar * data.normal parameter.1) =
      scalar * (canonicalLatitudeCauchyValueProfile parameter.2 *
          data.value parameter.1 +
        canonicalLatitudeCauchyNormalProfile parameter.2 * data.normal parameter.1)
    ring

/-- Additivity of the tubular local extension. -/
theorem tubularLocalExtension_add
    (first second : CanonicalLatitudeDeckCauchyData period)
    (parameter : CanonicalLatitudeTubularCollar period) :
    (first + second).tubularLocalExtension period parameter =
      first.tubularLocalExtension period parameter +
        second.tubularLocalExtension period parameter := by
  unfold P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCollarQuotient4D.CanonicalLatitudeDeckCauchyData.tubularLocalExtension
  change _ * (_ + _) + _ * (_ + _) = (_ * _ + _ * _) + (_ * _ + _ * _)
  ring

/-- Homogeneity of the tubular local extension. -/
theorem tubularLocalExtension_smul
    (scalar : Real) (data : CanonicalLatitudeDeckCauchyData period)
    (parameter : CanonicalLatitudeTubularCollar period) :
    (scalar • data).tubularLocalExtension period parameter =
      scalar • data.tubularLocalExtension period parameter := by
  unfold P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCollarQuotient4D.CanonicalLatitudeDeckCauchyData.tubularLocalExtension
  exact congrFun (map_smul (localExtensionLinearMap period) scalar data)
    (parameter.1, parameter.2.1)

/-- Additivity after descent to the tubular quotient. -/
theorem tubularDescend_add
    (first second : CanonicalLatitudeDeckCauchyData period) :
    (first + second).tubularDescend period =
      first.tubularDescend period + second.tubularDescend period := by
  funext quotientPoint
  refine Quotient.inductionOn quotientPoint ?_
  intro parameter
  exact tubularLocalExtension_add period first second parameter

/-- Homogeneity after descent to the tubular quotient. -/
theorem tubularDescend_smul
    (scalar : Real) (data : CanonicalLatitudeDeckCauchyData period) :
    (scalar • data).tubularDescend period =
      scalar • data.tubularDescend period := by
  funext quotientPoint
  refine Quotient.inductionOn quotientPoint ?_
  intro parameter
  exact tubularLocalExtension_smul period scalar data parameter

/-- Additivity on the embedded physical tubular image. -/
theorem tubularBulkField_add
    (hPeriod : period ≠ 0)
    (first second : CanonicalLatitudeDeckCauchyData period) :
    canonicalLatitudeTubularBulkField period hPeriod (first + second) =
      canonicalLatitudeTubularBulkField period hPeriod first +
        canonicalLatitudeTubularBulkField period hPeriod second := by
  funext point
  unfold canonicalLatitudeTubularBulkField
  rw [tubularDescend_add]
  simp only [Pi.add_apply]

/-- Homogeneity on the embedded physical tubular image. -/
theorem tubularBulkField_smul
    (hPeriod : period ≠ 0)
    (scalar : Real) (data : CanonicalLatitudeDeckCauchyData period) :
    canonicalLatitudeTubularBulkField period hPeriod (scalar • data) =
      scalar • canonicalLatitudeTubularBulkField period hPeriod data := by
  funext point
  unfold canonicalLatitudeTubularBulkField
  rw [tubularDescend_smul]
  simp only [Pi.smul_apply]

/-- Additivity of the global physical candidate. -/
theorem globalCandidate_add
    (hPeriod : period ≠ 0)
    (first second : CanonicalLatitudeDeckCauchyData period) :
    canonicalLatitudeCauchyJetGlobalCandidate period hPeriod (first + second) =
      canonicalLatitudeCauchyJetGlobalCandidate period hPeriod first +
        canonicalLatitudeCauchyJetGlobalCandidate period hPeriod second := by
  funext point
  unfold canonicalLatitudeCauchyJetGlobalCandidate
  by_cases hPoint : point ∈ canonicalLatitudeTubularBulkSet period hPeriod
  · simp only [dif_pos hPoint, Pi.add_apply]
    rw [tubularBulkField_add]
    simp only [Pi.add_apply]
  · simp [hPoint]

/-- Homogeneity of the global physical candidate. -/
theorem globalCandidate_smul
    (hPeriod : period ≠ 0)
    (scalar : Real) (data : CanonicalLatitudeDeckCauchyData period) :
    canonicalLatitudeCauchyJetGlobalCandidate period hPeriod (scalar • data) =
      scalar • canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data := by
  funext point
  unfold canonicalLatitudeCauchyJetGlobalCandidate
  by_cases hPoint : point ∈ canonicalLatitudeTubularBulkSet period hPeriod
  · simp only [dif_pos hPoint, Pi.smul_apply]
    rw [tubularBulkField_smul]
    simp only [Pi.smul_apply]
  · simp [hPoint]

/-- Global candidate as a linear map into ordinary scalar functions on the bulk. -/
def globalCandidateLinearMap
    (hPeriod : period ≠ 0) :
    CanonicalLatitudeDeckCauchyData period →ₗ[Real]
      (MappingTorus (reflectedSphereData period hPeriod) → Real) where
  toFun := canonicalLatitudeCauchyJetGlobalCandidate period hPeriod
  map_add' := globalCandidate_add period hPeriod
  map_smul' := globalCandidate_smul period hPeriod

/-- Linearity certificate. -/
theorem globalCandidateLinearMap_certificate
    (hPeriod : period ≠ 0) :
    (∀ first second,
      globalCandidateLinearMap period hPeriod (first + second) =
        globalCandidateLinearMap period hPeriod first +
          globalCandidateLinearMap period hPeriod second) ∧
      (∀ (scalar : Real) data,
        globalCandidateLinearMap period hPeriod (scalar • data) =
          scalar • globalCandidateLinearMap period hPeriod data) :=
  ⟨map_add (globalCandidateLinearMap period hPeriod),
    map_smul (globalCandidateLinearMap period hPeriod)⟩

end CanonicalLatitudeDeckCauchyData

end
end P0EFTJanusMappingTorusCanonicalLatitudeDeckCauchyDataLinear4D
end JanusFormal
