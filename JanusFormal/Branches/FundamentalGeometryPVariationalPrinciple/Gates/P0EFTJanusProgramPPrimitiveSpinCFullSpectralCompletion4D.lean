import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusPrimitiveMonopoleZ4Spectrum
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalMaximalOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD7CircleHeatRegulatorBridge
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D

/-!
# Full primitive SpinC spectral completion

The legacy separated product model deliberately starts at the first positive
sphere level.  For primitive charge one, the geometric monopole Dirac
operator also has one sphere zero mode.  This gate restores that mode and
uses a maximal diagonal realization on the complete multiplicity-aware
`ℓ²` space.  The operator is self-adjoint for every circle twist and is
bijective/Fredholm in the physical quarter-twisted sector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProductThroatUnboundedDiracSquared4D
open P0EFTJanusProgramPD7CircleHeatRegulatorBridge
open P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Every primitive monopole sphere level, including level zero, with its
exact multiplicity. -/
abbrev PrimitiveSpinCFullSphereMode :=
  Σ level : Nat, Fin (primitiveSphereModeDegeneracy level)

/-- Full primitive sphere-times-circle mode set. -/
abbrev PrimitiveSpinCFullMode :=
  PrimitiveSpinCFullSphereMode × Int

/-- Radius-one primitive sphere eigenvalue squared at level `n`. -/
def primitiveSpinCFullSphereEigenvalueSquared (level : Nat) : Real :=
  (level : Real) * ((level + 1 : Nat) : Real)

theorem primitiveSpinCFullSphereEigenvalueSquared_eq_numerator
    (level : Nat) :
    primitiveSpinCFullSphereEigenvalueSquared level =
      (primitiveSphereModeNumerator level : Real) := by
  simp [primitiveSpinCFullSphereEigenvalueSquared,
    primitiveSphereModeNumerator]

@[simp]
theorem primitiveSpinCFullSphereEigenvalueSquared_zero :
    primitiveSpinCFullSphereEigenvalueSquared 0 = 0 := by
  simp [primitiveSpinCFullSphereEigenvalueSquared]

theorem primitiveSpinCFullSphereEigenvalueSquared_nonnegative
    (level : Nat) :
    0 ≤ primitiveSpinCFullSphereEigenvalueSquared level := by
  unfold primitiveSpinCFullSphereEigenvalueSquared
  positivity

/-- Complete squared product spectrum, now including the monopole zero
sphere level. -/
def primitiveSpinCFullDiracSquaredEigenvalue
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode) : Real :=
  primitiveSpinCFullSphereEigenvalueSquared mode.1.1 +
    circleOperatorSquaredEigenvalue fold twist mode.2

theorem primitiveSpinCFullDiracSquaredEigenvalue_nonnegative
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode) :
    0 ≤ primitiveSpinCFullDiracSquaredEigenvalue fold twist mode := by
  unfold primitiveSpinCFullDiracSquaredEigenvalue
  exact add_nonneg
    (primitiveSpinCFullSphereEigenvalueSquared_nonnegative mode.1.1)
    (by
      rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
      exact eigenvalueSq_nonnegative fold twist mode.2)

/-- PT-signed first-order eigenvalue of the full primitive spectrum. -/
def primitiveSpinCFullDiracEigenvalue
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode) : Real :=
  fold.spectralSign *
    Real.sqrt
      (primitiveSpinCFullDiracSquaredEigenvalue fold twist mode)

theorem primitiveSpinCFullDiracEigenvalue_sq
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode) :
    primitiveSpinCFullDiracEigenvalue fold twist mode ^ 2 =
      primitiveSpinCFullDiracSquaredEigenvalue fold twist mode := by
  unfold primitiveSpinCFullDiracEigenvalue
  rw [mul_pow, Real.sq_sqrt
    (primitiveSpinCFullDiracSquaredEigenvalue_nonnegative
      fold twist mode)]
  cases fold <;> norm_num

/-- The complete primitive spectral Hilbert space. -/
abbrev PrimitiveSpinCFullL2 :=
  ComplexDiagonalHilbert PrimitiveSpinCFullMode

/-- Full maximal first-order Sobolev/graph domain. -/
abbrev PrimitiveSpinCFullH1
    (fold : Fold) (twist : CircleTwist) :=
  complexDiagonalDomain PrimitiveSpinCFullMode
    (primitiveSpinCFullDiracEigenvalue fold twist)

/-- Full maximal first-order Dirac realization. -/
abbrev primitiveSpinCFullUnboundedDirac
    (fold : Fold) (twist : CircleTwist) :=
  complexDiagonalOperator PrimitiveSpinCFullMode
    (primitiveSpinCFullDiracEigenvalue fold twist)

/-- Full maximal squared Sobolev/graph domain. -/
abbrev PrimitiveSpinCFullH2
    (fold : Fold) (twist : CircleTwist) :=
  complexDiagonalDomain PrimitiveSpinCFullMode
    (primitiveSpinCFullDiracSquaredEigenvalue fold twist)

/-- Full maximal squared Dirac realization. -/
abbrev primitiveSpinCFullUnboundedDiracSquared
    (fold : Fold) (twist : CircleTwist) :=
  complexDiagonalOperator PrimitiveSpinCFullMode
    (primitiveSpinCFullDiracSquaredEigenvalue fold twist)

theorem primitiveSpinCFullH1_dense
    (fold : Fold) (twist : CircleTwist) :
    Dense (PrimitiveSpinCFullH1 fold twist :
      Set PrimitiveSpinCFullL2) :=
  complexDiagonalDomain_dense PrimitiveSpinCFullMode
    (primitiveSpinCFullDiracEigenvalue fold twist)

theorem primitiveSpinCFullUnboundedDirac_isSelfAdjoint
    (fold : Fold) (twist : CircleTwist) :
    IsSelfAdjoint
      (primitiveSpinCFullUnboundedDirac fold twist) :=
  complexDiagonalOperator_isSelfAdjoint PrimitiveSpinCFullMode
    (primitiveSpinCFullDiracEigenvalue fold twist)

theorem primitiveSpinCFullUnboundedDirac_isClosed
    (fold : Fold) (twist : CircleTwist) :
    (primitiveSpinCFullUnboundedDirac fold twist).IsClosed :=
  complexDiagonalOperator_isClosed PrimitiveSpinCFullMode
    (primitiveSpinCFullDiracEigenvalue fold twist)

theorem primitiveSpinCFullH2_dense
    (fold : Fold) (twist : CircleTwist) :
    Dense (PrimitiveSpinCFullH2 fold twist :
      Set PrimitiveSpinCFullL2) :=
  complexDiagonalDomain_dense PrimitiveSpinCFullMode
    (primitiveSpinCFullDiracSquaredEigenvalue fold twist)

theorem primitiveSpinCFullUnboundedDiracSquared_isSelfAdjoint
    (fold : Fold) (twist : CircleTwist) :
    IsSelfAdjoint
      (primitiveSpinCFullUnboundedDiracSquared fold twist) :=
  complexDiagonalOperator_isSelfAdjoint PrimitiveSpinCFullMode
    (primitiveSpinCFullDiracSquaredEigenvalue fold twist)

theorem primitiveSpinCFullUnboundedDiracSquared_isClosed
    (fold : Fold) (twist : CircleTwist) :
    (primitiveSpinCFullUnboundedDiracSquared fold twist).IsClosed :=
  complexDiagonalOperator_isClosed PrimitiveSpinCFullMode
    (primitiveSpinCFullDiracSquaredEigenvalue fold twist)

/-- The missing sphere zero sector is present with multiplicity exactly one. -/
theorem primitiveSpinCFull_zeroSphereSector_multiplicity :
    primitiveSphereModeDegeneracy 0 = 1 :=
  primitive_sphere_zero_mode_degeneracy

/-- On the sphere zero sector, the product square is exactly the circle
operator square. -/
@[simp]
theorem primitiveSpinCFull_zeroSphereSector_squaredEigenvalue
    (fold : Fold) (twist : CircleTwist)
    (multiplicity : Fin (primitiveSphereModeDegeneracy 0))
    (circleMode : Int) :
    primitiveSpinCFullDiracSquaredEigenvalue fold twist
        ((⟨0, multiplicity⟩ :
          PrimitiveSpinCFullSphereMode), circleMode) =
      circleOperatorSquaredEigenvalue fold twist circleMode := by
  simp [primitiveSpinCFullDiracSquaredEigenvalue]

/-- Positive full levels `n = level + 1` agree exactly with the legacy
positive-level sphere spectrum. -/
theorem primitiveSpinCFull_positiveSphereEigenvalue_agrees
    (level : Nat) :
    primitiveSpinCFullSphereEigenvalueSquared (level + 1) =
      sphereEigenvalueSquared
        (PrimitiveSpinCSpectralData period hPeriod) level := by
  have hRadius :
      (PrimitiveSpinCSpectralData period hPeriod).sphereRadius = 1 :=
    canonicalPrimitiveProgramPCommonGeometricDomain4D_sphereRadius
      period hPeriod
  have hCharge :
      monopoleAbsCharge
        (PrimitiveSpinCSpectralData period hPeriod) = 1 := by
    unfold monopoleAbsCharge
    rw [canonicalPrimitiveProgramPCommonGeometricDomain4D_spectralCharge
      period hPeriod]
    norm_num
  rw [sphereEigenvalueSquared, hRadius, hCharge]
  norm_num [primitiveSpinCFullSphereEigenvalueSquared]

/-- Positive full-level multiplicities agree exactly with the legacy
positive-level multiplicities. -/
theorem primitiveSpinCFull_positiveSphereMultiplicity_agrees
    (level : Nat) :
    primitiveSphereModeDegeneracy (level + 1) =
      sphereMultiplicity
        (PrimitiveSpinCSpectralData period hPeriod) level := by
  have hCharge :
      monopoleAbsCharge
        (PrimitiveSpinCSpectralData period hPeriod) = 1 := by
    unfold monopoleAbsCharge
    rw [canonicalPrimitiveProgramPCommonGeometricDomain4D_spectralCharge
      period hPeriod]
    norm_num
  rw [sphereMultiplicity, hCharge]
  simp [primitiveSphereModeDegeneracy]

/-- A quarter-twisted circle eigenvalue stays at least `1/4` from zero. -/
theorem quarterTwist_baseEigenvalue_abs_ge
    (mode : Int) :
    (1 / 4 : Real) ≤ |baseEigenvalue quarterTwist mode| := by
  by_cases hMode : 0 ≤ mode
  · have hCast : 0 ≤ (mode : Real) := by
      exact_mod_cast hMode
    have hBase : 0 ≤ baseEigenvalue quarterTwist mode := by
      simp [baseEigenvalue, quarterTwist]
      linarith
    rw [abs_of_nonneg hBase]
    simp [baseEigenvalue, quarterTwist]
    linarith
  · have hModeLe : mode ≤ -1 := by omega
    have hCast : (mode : Real) ≤ -1 := by
      exact_mod_cast hModeLe
    have hBase : baseEigenvalue quarterTwist mode ≤ 0 := by
      simp [baseEigenvalue, quarterTwist]
      linarith
    rw [abs_of_nonpos hBase]
    simp [baseEigenvalue, quarterTwist]
    linarith

theorem quarterTwist_circleSquaredEigenvalue_ge
    (fold : Fold) (mode : Int) :
    (1 / 16 : Real) ≤
      circleOperatorSquaredEigenvalue fold quarterTwist mode := by
  rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
  have hFold :
      eigenvalueSq fold quarterTwist mode =
        baseEigenvalue quarterTwist mode ^ 2 := by
    cases fold <;>
      simp [eigenvalueSq, diracEigenvalue]
  rw [hFold]
  have hAbs := quarterTwist_baseEigenvalue_abs_ge mode
  have hProduct :
      0 ≤
        (|baseEigenvalue quarterTwist mode| - (1 / 4 : Real)) *
          (|baseEigenvalue quarterTwist mode| + (1 / 4 : Real)) :=
    mul_nonneg (sub_nonneg.mpr hAbs)
      (add_nonneg (abs_nonneg _) (by norm_num))
  nlinarith [sq_abs (baseEigenvalue quarterTwist mode)]

theorem primitiveSpinCFull_quarter_squared_gap
    (fold : Fold) (mode : PrimitiveSpinCFullMode) :
    (1 / 16 : Real) ≤
      primitiveSpinCFullDiracSquaredEigenvalue
        fold quarterTwist mode := by
  have hSphere :=
    primitiveSpinCFullSphereEigenvalueSquared_nonnegative mode.1.1
  have hCircle :=
    quarterTwist_circleSquaredEigenvalue_ge fold mode.2
  unfold primitiveSpinCFullDiracSquaredEigenvalue
  linarith

/-- The full primitive operator retains a physical quarter-twisted gap even
though the sphere zero mode is now included. -/
theorem primitiveSpinCFull_quarter_gap
    (fold : Fold) (mode : PrimitiveSpinCFullMode) :
    (1 / 4 : Real) ≤
      |primitiveSpinCFullDiracEigenvalue
        fold quarterTwist mode| := by
  unfold primitiveSpinCFullDiracEigenvalue
  rw [abs_mul]
  have hSign : |fold.spectralSign| = 1 := by
    cases fold <;> norm_num
  rw [hSign, one_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hSqrt := Real.sqrt_le_sqrt
    (primitiveSpinCFull_quarter_squared_gap fold mode)
  norm_num at hSqrt
  exact hSqrt

theorem primitiveSpinCFullUnboundedDirac_quarter_bijective
    (fold : Fold) :
    Function.Bijective
      (primitiveSpinCFullUnboundedDirac fold quarterTwist) :=
  ⟨complexDiagonalOperator_injective_of_gap
      PrimitiveSpinCFullMode
      (primitiveSpinCFullDiracEigenvalue fold quarterTwist)
      (1 / 4) (by norm_num)
      (primitiveSpinCFull_quarter_gap fold),
    complexDiagonalOperator_surjective_of_gap
      PrimitiveSpinCFullMode
      (primitiveSpinCFullDiracEigenvalue fold quarterTwist)
      (1 / 4) (by norm_num)
      (primitiveSpinCFull_quarter_gap fold)⟩

theorem primitiveSpinCFullUnboundedDirac_quarter_fredholm
    (fold : Fold) :
    IsClosed
        (LinearMap.range
            (primitiveSpinCFullUnboundedDirac
              fold quarterTwist).toFun :
          Set PrimitiveSpinCFullL2) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (primitiveSpinCFullUnboundedDirac
            fold quarterTwist).toFun) ∧
      FiniteDimensional Complex
        (ComplexDiagonalCokernel PrimitiveSpinCFullMode
          (primitiveSpinCFullDiracEigenvalue fold quarterTwist)) :=
  complexDiagonalOperator_fredholm_of_gap
    PrimitiveSpinCFullMode
    (primitiveSpinCFullDiracEigenvalue fold quarterTwist)
    (1 / 4) (by norm_num)
    (primitiveSpinCFull_quarter_gap fold)

theorem primitiveSpinCFullUnboundedDirac_quarter_index_zero
    (fold : Fold) :
    complexDiagonalOperatorIndex PrimitiveSpinCFullMode
      (primitiveSpinCFullDiracEigenvalue fold quarterTwist) = 0 :=
  complexDiagonalOperatorIndex_zero_of_gap
    PrimitiveSpinCFullMode
    (primitiveSpinCFullDiracEigenvalue fold quarterTwist)
    (1 / 4) (by norm_num)
    (primitiveSpinCFull_quarter_gap fold)

/-- Concrete full completion certificate for the primitive physical sector. -/
structure ProgramPPrimitiveSpinCFullSpectralCertificate4D where
  zeroSphereMultiplicity :
    primitiveSphereModeDegeneracy 0 = 1
  h1Dense :
    ∀ fold twist,
      Dense (PrimitiveSpinCFullH1 fold twist :
        Set PrimitiveSpinCFullL2)
  firstOrderSelfAdjoint :
    ∀ fold twist,
      IsSelfAdjoint
        (primitiveSpinCFullUnboundedDirac fold twist)
  squaredSelfAdjoint :
    ∀ fold twist,
      IsSelfAdjoint
        (primitiveSpinCFullUnboundedDiracSquared fold twist)
  physicalQuarterFredholm :
    ∀ fold,
      IsClosed
          (LinearMap.range
              (primitiveSpinCFullUnboundedDirac
                fold quarterTwist).toFun :
            Set PrimitiveSpinCFullL2) ∧
        FiniteDimensional Complex
          (LinearMap.ker
            (primitiveSpinCFullUnboundedDirac
              fold quarterTwist).toFun)
  physicalQuarterIndexZero :
    ∀ fold,
      complexDiagonalOperatorIndex PrimitiveSpinCFullMode
        (primitiveSpinCFullDiracEigenvalue
          fold quarterTwist) = 0

def programPPrimitiveSpinCFullSpectralCertificate4D :
    ProgramPPrimitiveSpinCFullSpectralCertificate4D where
  zeroSphereMultiplicity :=
    primitiveSpinCFull_zeroSphereSector_multiplicity
  h1Dense := primitiveSpinCFullH1_dense
  firstOrderSelfAdjoint :=
    primitiveSpinCFullUnboundedDirac_isSelfAdjoint
  squaredSelfAdjoint :=
    primitiveSpinCFullUnboundedDiracSquared_isSelfAdjoint
  physicalQuarterFredholm := fun fold =>
    ⟨(primitiveSpinCFullUnboundedDirac_quarter_fredholm fold).1,
      (primitiveSpinCFullUnboundedDirac_quarter_fredholm fold).2.1⟩
  physicalQuarterIndexZero :=
    primitiveSpinCFullUnboundedDirac_quarter_index_zero

theorem programPPrimitiveSpinCFullSpectralCertificate4D_nonempty :
    Nonempty ProgramPPrimitiveSpinCFullSpectralCertificate4D :=
  ⟨programPPrimitiveSpinCFullSpectralCertificate4D⟩

end
end P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D
end JanusFormal
