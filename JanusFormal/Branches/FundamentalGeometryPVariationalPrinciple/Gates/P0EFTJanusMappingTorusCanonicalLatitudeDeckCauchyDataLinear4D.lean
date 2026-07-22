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
    { value := 0
      normal := 0
      value_periodic := by intro base; rfl
      normal_antiperiodic := by intro base; simp }

instance : Add (CanonicalLatitudeDeckCauchyData period) where
  add first second :=
    { value := first.value + second.value
      normal := first.normal + second.normal
      value_periodic := by
        intro base
        rw [LinearMap.add_apply, LinearMap.add_apply,
          first.value_periodic, second.value_periodic]
      normal_antiperiodic := by
        intro base
        rw [LinearMap.add_apply, LinearMap.add_apply,
          first.normal_antiperiodic, second.normal_antiperiodic]
        ring }

instance : Neg (CanonicalLatitudeDeckCauchyData period) where
  neg data :=
    { value := -data.value
      normal := -data.normal
      value_periodic := by
        intro base
        rw [LinearMap.neg_apply, LinearMap.neg_apply,
          data.value_periodic]
      normal_antiperiodic := by
        intro base
        rw [LinearMap.neg_apply, LinearMap.neg_apply,
          data.normal_antiperiodic]
        ring }

instance : AddCommGroup (CanonicalLatitudeDeckCauchyData period) where
  add_assoc first second third := by
    ext <;> simp [add_assoc]
  zero_add data := by
    ext <;> simp
  add_zero data := by
    ext <;> simp
  nsmul := nsmulRec
  add_comm first second := by
    ext <;> simp [add_comm]
  neg_add_cancel data := by
    ext <;> simp
  sub_eq_add_neg := by
    intro first second
    rfl
  zsmul := zsmulRec

instance : SMul Real (CanonicalLatitudeDeckCauchyData period) where
  smul scalar data :=
    { value := scalar • data.value
      normal := scalar • data.normal
      value_periodic := by
        intro base
        rw [LinearMap.smul_apply, LinearMap.smul_apply,
          data.value_periodic]
      normal_antiperiodic := by
        intro base
        rw [LinearMap.smul_apply, LinearMap.smul_apply,
          data.normal_antiperiodic]
        ring }

instance : Module Real (CanonicalLatitudeDeckCauchyData period) where
  one_smul data := by ext <;> simp
  mul_smul first second data := by ext <;> simp [mul_smul]
  smul_add scalar first second := by ext <;> simp [smul_add]
  smul_zero scalar := by ext <;> simp
  add_smul first second data := by ext <;> simp [add_smul]
  zero_smul data := by ext <;> simp

namespace CanonicalLatitudeDeckCauchyData

/-- The local collar extension is linear in deck Cauchy data. -/
def localExtensionLinearMap :
    CanonicalLatitudeDeckCauchyData period →ₗ[Real]
      (CanonicalLatitudeCauchyCollar → Real) where
  toFun := CanonicalLatitudeDeckCauchyData.localExtension
  map_add' first second := by
    funext parameter
    simp [CanonicalLatitudeDeckCauchyData.localExtension,
      canonicalLatitudeLocalCauchyExtension]
    ring
  map_smul' scalar data := by
    funext parameter
    simp [CanonicalLatitudeDeckCauchyData.localExtension,
      canonicalLatitudeLocalCauchyExtension]
    ring

/-- Additivity of the tubular local extension. -/
theorem tubularLocalExtension_add
    (first second : CanonicalLatitudeDeckCauchyData period)
    (parameter : CanonicalLatitudeTubularCollar) :
    (first + second).tubularLocalExtension parameter =
      first.tubularLocalExtension parameter +
        second.tubularLocalExtension parameter := by
  rfl

/-- Homogeneity of the tubular local extension. -/
theorem tubularLocalExtension_smul
    (scalar : Real) (data : CanonicalLatitudeDeckCauchyData period)
    (parameter : CanonicalLatitudeTubularCollar) :
    (scalar • data).tubularLocalExtension parameter =
      scalar • data.tubularLocalExtension parameter := by
  change _ = scalar * _
  rfl

/-- Additivity after descent to the tubular quotient. -/
theorem tubularDescend_add
    (first second : CanonicalLatitudeDeckCauchyData period) :
    (first + second).tubularDescend =
      first.tubularDescend + second.tubularDescend := by
  funext quotientPoint
  refine Quotient.inductionOn quotientPoint ?_
  intro parameter
  rfl

/-- Homogeneity after descent to the tubular quotient. -/
theorem tubularDescend_smul
    (scalar : Real) (data : CanonicalLatitudeDeckCauchyData period) :
    (scalar • data).tubularDescend =
      scalar • data.tubularDescend := by
  funext quotientPoint
  refine Quotient.inductionOn quotientPoint ?_
  intro parameter
  rfl

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
  rfl

/-- Homogeneity on the embedded physical tubular image. -/
theorem tubularBulkField_smul
    (hPeriod : period ≠ 0)
    (scalar : Real) (data : CanonicalLatitudeDeckCauchyData period) :
    canonicalLatitudeTubularBulkField period hPeriod (scalar • data) =
      scalar • canonicalLatitudeTubularBulkField period hPeriod data := by
  funext point
  unfold canonicalLatitudeTubularBulkField
  rw [tubularDescend_smul]
  rfl

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
      (∀ scalar data,
        globalCandidateLinearMap period hPeriod (scalar • data) =
          scalar • globalCandidateLinearMap period hPeriod data) :=
  ⟨map_add (globalCandidateLinearMap period hPeriod),
    map_smul (globalCandidateLinearMap period hPeriod)⟩

end CanonicalLatitudeDeckCauchyData

end
end P0EFTJanusMappingTorusCanonicalLatitudeDeckCauchyDataLinear4D
end JanusFormal
