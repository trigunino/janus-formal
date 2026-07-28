import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFullSpectralSynthesis4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D

/-!
# Geometric L² orthonormalization of each primitive SpinC spectral block

The null-power multiplicity packets are canonical and linearly independent,
but are not declared orthonormal.  This module applies Gram--Schmidt in the
independently integrated geometric `L²` product, separately inside every
fixed sphere-level/sector/circle-mode eigenspace.  Hence normalization does
not alter the exact geometric `D²` eigenvalue.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalization4D

set_option autoImplicit false

noncomputable section

open InnerProductSpace
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFullSpectralSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

/-- The canonical null-power multiplicity packet in one fixed spectral
block. -/
def primitiveSpinCGeometricL2RawBlockFamily
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int)
    (multiplicity : Fin (primitiveSphereModeDegeneracy sphereLevel)) :
    SmoothSection period hPeriod :=
  primitiveSpinCAllModeNullHarmonicRealSection
    period hPeriod
    (sector, (⟨sphereLevel, multiplicity⟩, circleMode))

private theorem primitiveSpinCGeometricL2RawBlockMode_injective
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int) :
    Function.Injective
      (fun multiplicity : Fin (primitiveSphereModeDegeneracy sphereLevel) =>
        ((sector, (⟨sphereLevel, multiplicity⟩, circleMode)) :
          PrimitiveSpinCGeometricFullMode)) := by
  intro first second hEqual
  cases hEqual
  rfl

/-- Each fixed spectral multiplicity packet remains linearly independent in
the geometric inner-product space. -/
theorem primitiveSpinCGeometricL2RawBlockFamily_linearIndependent
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int) :
    LinearIndependent Complex
      (primitiveSpinCGeometricL2RawBlockFamily
        period hPeriod sphereLevel sector circleMode) := by
  exact
    (primitiveSpinCAllModeNullHarmonicRealSection_linearIndependent
      period hPeriod).comp
      (fun multiplicity =>
        ((sector, (⟨sphereLevel, multiplicity⟩, circleMode)) :
          PrimitiveSpinCGeometricFullMode))
      (primitiveSpinCGeometricL2RawBlockMode_injective
        sphereLevel sector circleMode)

/-- Gram--Schmidt normalization in the independently integrated geometric
`L²` product. -/
def primitiveSpinCGeometricL2OrthonormalBlockFamily
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int) :
    Fin (primitiveSphereModeDegeneracy sphereLevel) →
      SmoothSection period hPeriod :=
  gramSchmidtNormed Complex
    (primitiveSpinCGeometricL2RawBlockFamily
      period hPeriod sphereLevel sector circleMode)

theorem primitiveSpinCGeometricL2OrthonormalBlockFamily_orthonormal
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int) :
    Orthonormal Complex
      (primitiveSpinCGeometricL2OrthonormalBlockFamily
        period hPeriod sphereLevel sector circleMode) :=
  gramSchmidtNormed_orthonormal
    (primitiveSpinCGeometricL2RawBlockFamily_linearIndependent
      period hPeriod sphereLevel sector circleMode)

/-- Orthonormalization preserves the whole finite multiplicity span. -/
theorem primitiveSpinCGeometricL2OrthonormalBlockFamily_span
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int) :
    Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2OrthonormalBlockFamily
            period hPeriod sphereLevel sector circleMode)) =
      Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod sphereLevel sector circleMode)) := by
  rw [primitiveSpinCGeometricL2OrthonormalBlockFamily,
    span_gramSchmidtNormed_range, span_gramSchmidt]

/-- The squared eigenvalue shared by one complete multiplicity block. -/
def primitiveSpinCGeometricL2BlockSquaredEigenvalue
    (sphereLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) : Complex :=
  ((primitiveSpinCFullSphereEigenvalueSquared sphereLevel +
      normalRootLeviCivitaCorrectedFrequency
        period sector circleMode ^ 2 : Real) : Complex)

private theorem primitiveSpinCGeometricL2RawBlockFamily_mem_eigenspace
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int)
    (multiplicity : Fin (primitiveSphereModeDegeneracy sphereLevel)) :
    primitiveSpinCGeometricL2RawBlockFamily
        period hPeriod sphereLevel sector circleMode multiplicity ∈
      Module.End.eigenspace
        (primitiveSpinCGeometricDiracSquaredComplexLinearMap
          period hPeriod)
        (primitiveSpinCGeometricL2BlockSquaredEigenvalue
          period sphereLevel sector circleMode) := by
  rw [Module.End.mem_eigenspace_iff]
  have hValue :
      primitiveSpinCGeometricL2BlockSquaredEigenvalue
          period sphereLevel sector circleMode =
        ((primitiveSpinCGeometricSquaredEigenvalue
          period hPeriod
          (sector, (⟨sphereLevel, multiplicity⟩, circleMode)) : Real) :
            Complex) := by
    unfold primitiveSpinCGeometricL2BlockSquaredEigenvalue
      primitiveSpinCGeometricSquaredEigenvalue
    rw [normalRootLeviCivitaCorrectedFrequency_sq_eq_circle
      period hPeriod sector circleMode]
  rw [hValue]
  exact
    primitiveSpinCAllModeNullHarmonicRealSection_dirac_sq_complex
      period hPeriod
      (sector, (⟨sphereLevel, multiplicity⟩, circleMode))

/-- Every geometrically orthonormalized block vector satisfies the same
exact intrinsic `D²` equation as the raw null-power packet. -/
theorem primitiveSpinCGeometricL2OrthonormalBlockFamily_dirac_sq
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int)
    (multiplicity : Fin (primitiveSphereModeDegeneracy sphereLevel)) :
    primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
        (primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod sphereLevel sector circleMode multiplicity) =
      primitiveSpinCGeometricL2BlockSquaredEigenvalue
          period sphereLevel sector circleMode •
        primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod sphereLevel sector circleMode multiplicity := by
  rw [← Module.End.mem_eigenspace_iff]
  have hSpan :
      Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod sphereLevel sector circleMode)) ≤
        Module.End.eigenspace
          (primitiveSpinCGeometricDiracSquaredComplexLinearMap
            period hPeriod)
          (primitiveSpinCGeometricL2BlockSquaredEigenvalue
            period sphereLevel sector circleMode) := by
    rw [Submodule.span_le]
    rintro state ⟨rawMultiplicity, rfl⟩
    exact
      primitiveSpinCGeometricL2RawBlockFamily_mem_eigenspace
        period hPeriod sphereLevel sector circleMode rawMultiplicity
  apply hSpan
  rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span
    period hPeriod sphereLevel sector circleMode]
  exact Submodule.subset_span (Set.mem_range_self multiplicity)

/-- Finite synthesis from standard Euclidean coefficients into one
geometrically normalized eigenspace. -/
def primitiveSpinCGeometricL2OrthonormalBlockSynthesis
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int) :
    EuclideanSpace Complex
        (Fin (primitiveSphereModeDegeneracy sphereLevel)) →ₗ[Complex]
      SmoothSection period hPeriod where
  toFun coefficients :=
    ∑ multiplicity,
      coefficients multiplicity •
        primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod sphereLevel sector circleMode multiplicity
  map_add' first second := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' scalar coefficients := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply,
      smul_eq_mul, smul_smul, Finset.smul_sum]

/-- Exact finite-block Parseval identity in the independent geometric
pairing. -/
theorem primitiveSpinCGeometricL2OrthonormalBlockSynthesis_inner
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int)
    (first second :
      EuclideanSpace Complex
        (Fin (primitiveSphereModeDegeneracy sphereLevel))) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod sphereLevel sector circleMode first)
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod sphereLevel sector circleMode second) =
      ∑ multiplicity,
        (starRingEnd Complex) (first multiplicity) *
          second multiplicity := by
  change
    inner Complex
        (∑ multiplicity,
          first multiplicity •
            primitiveSpinCGeometricL2OrthonormalBlockFamily
              period hPeriod sphereLevel sector circleMode multiplicity)
        (∑ multiplicity,
          second multiplicity •
            primitiveSpinCGeometricL2OrthonormalBlockFamily
              period hPeriod sphereLevel sector circleMode multiplicity) =
      _
  simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
    (primitiveSpinCGeometricL2OrthonormalBlockFamily_orthonormal
      period hPeriod sphereLevel sector circleMode).inner_sum
        first second Finset.univ

/-- Each finite multiplicity block is isometric to its standard Euclidean
coefficient space. -/
def primitiveSpinCGeometricL2OrthonormalBlockLinearIsometry
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int) :
    EuclideanSpace Complex
        (Fin (primitiveSphereModeDegeneracy sphereLevel)) →ₗᵢ[Complex]
      SmoothSection period hPeriod :=
  (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
    period hPeriod sphereLevel sector circleMode).isometryOfInner (by
      intro first second
      change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
              period hPeriod sphereLevel sector circleMode first)
            (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
              period hPeriod sphereLevel sector circleMode second) =
          inner Complex first second
      rw [primitiveSpinCGeometricL2OrthonormalBlockSynthesis_inner
        period hPeriod sphereLevel sector circleMode]
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro multiplicity _
      rw [RCLike.inner_apply, mul_comm])

/-- The finite-block isometry still exactly intertwines the geometric
`D²` operator with its scalar eigenvalue. -/
theorem primitiveSpinCGeometricL2OrthonormalBlockSynthesis_dirac_sq
    (sphereLevel : Nat) (sector : NormalRootChoice) (circleMode : Int)
    (coefficients :
      EuclideanSpace Complex
        (Fin (primitiveSphereModeDegeneracy sphereLevel))) :
    primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod sphereLevel sector circleMode coefficients) =
      primitiveSpinCGeometricL2BlockSquaredEigenvalue
          period sphereLevel sector circleMode •
        primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod sphereLevel sector circleMode coefficients := by
  change
    primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
        (∑ multiplicity,
          coefficients multiplicity •
            primitiveSpinCGeometricL2OrthonormalBlockFamily
              period hPeriod sphereLevel sector circleMode multiplicity) =
      primitiveSpinCGeometricL2BlockSquaredEigenvalue
          period sphereLevel sector circleMode •
        ∑ multiplicity,
          coefficients multiplicity •
            primitiveSpinCGeometricL2OrthonormalBlockFamily
              period hPeriod sphereLevel sector circleMode multiplicity
  rw [map_sum]
  simp_rw [map_smul,
    primitiveSpinCGeometricL2OrthonormalBlockFamily_dirac_sq
      period hPeriod sphereLevel sector circleMode]
  rw [Finset.smul_sum]
  simp_rw [smul_smul, mul_comm]

/-- Assumption-free certificate that every finite multiplicity block admits
an orthonormal geometric eigenpacket. -/
structure ProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalizationCertificate4D
    where
  orthonormal :
    ∀ sphereLevel sector circleMode,
      Orthonormal Complex
        (primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod sphereLevel sector circleMode)
  sameSpan :
    ∀ sphereLevel sector circleMode,
      Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2OrthonormalBlockFamily
              period hPeriod sphereLevel sector circleMode)) =
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod sphereLevel sector circleMode))
  exactDiracSquared :
    ∀ sphereLevel sector circleMode multiplicity,
      primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
          (primitiveSpinCGeometricL2OrthonormalBlockFamily
            period hPeriod sphereLevel sector circleMode multiplicity) =
        primitiveSpinCGeometricL2BlockSquaredEigenvalue
            period sphereLevel sector circleMode •
          primitiveSpinCGeometricL2OrthonormalBlockFamily
            period hPeriod sphereLevel sector circleMode multiplicity
  blockParseval :
    ∀ sphereLevel sector circleMode first second,
      d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
            period hPeriod sphereLevel sector circleMode first)
          (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
            period hPeriod sphereLevel sector circleMode second) =
        ∑ multiplicity,
          (starRingEnd Complex) (first multiplicity) *
            second multiplicity
  blockIntertwining :
    ∀ sphereLevel sector circleMode coefficients,
      primitiveSpinCGeometricDiracSquaredComplexLinearMap period hPeriod
          (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
            period hPeriod sphereLevel sector circleMode coefficients) =
        primitiveSpinCGeometricL2BlockSquaredEigenvalue
            period sphereLevel sector circleMode •
          primitiveSpinCGeometricL2OrthonormalBlockSynthesis
            period hPeriod sphereLevel sector circleMode coefficients

def programPD9PrimitiveSpinCGeometricL2BlockOrthonormalizationCertificate4D :
    ProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalizationCertificate4D
      period hPeriod where
  orthonormal :=
    primitiveSpinCGeometricL2OrthonormalBlockFamily_orthonormal
      period hPeriod
  sameSpan :=
    primitiveSpinCGeometricL2OrthonormalBlockFamily_span period hPeriod
  exactDiracSquared :=
    primitiveSpinCGeometricL2OrthonormalBlockFamily_dirac_sq
      period hPeriod
  blockParseval :=
    primitiveSpinCGeometricL2OrthonormalBlockSynthesis_inner
      period hPeriod
  blockIntertwining :=
    primitiveSpinCGeometricL2OrthonormalBlockSynthesis_dirac_sq
      period hPeriod

theorem primitiveSpinCGeometricL2BlockOrthonormalization_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalizationCertificate4D
        period hPeriod) :=
  ⟨programPD9PrimitiveSpinCGeometricL2BlockOrthonormalizationCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalization4D
end JanusFormal
