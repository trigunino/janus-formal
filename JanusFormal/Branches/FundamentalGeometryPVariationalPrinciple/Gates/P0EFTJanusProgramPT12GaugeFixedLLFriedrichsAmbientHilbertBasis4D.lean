import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFriedrichsWeylHeat4D

/-!
# Real Hilbert basis for the T12 Friedrichs ambient product

This file combines a complex Hilbert basis, viewed through its compatible
real inner product, with a real Hilbert basis on an `L²` product.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsAmbientHilbertBasis4D

set_option autoImplicit false
noncomputable section

open Set Submodule
open scoped ENNReal lp
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLFriedrichsWeylHeat4D

section ComplexRealification

variable {Index E : Type*} [DecidableEq Index]
variable [NormedAddCommGroup E] [InnerProductSpace Complex E]
variable [InnerProductSpace Real E] [CompleteSpace E]

/-- The two real vectors attached to one complex Hilbert-basis vector. -/
def complexHilbertBasisRealVector
    (basis : HilbertBasis Index Complex E) : Index ⊕ Index → E
  | .inl index => basis index
  | .inr index => Complex.I • basis index

theorem complexHilbertBasisRealVector_orthonormal
    (basis : HilbertBasis Index Complex E)
    (inner_compatible : ∀ (first second : E),
      inner Real first second = (inner Complex first second).re) :
    Orthonormal Real (complexHilbertBasisRealVector basis) := by
  classical
  rw [orthonormal_iff_ite]
  intro first second
  have hBasis := orthonormal_iff_ite.mp basis.orthonormal
  rcases first with first | first <;> rcases second with second | second
  all_goals simp only [complexHilbertBasisRealVector]
  · rw [inner_compatible, hBasis]
    by_cases h : first = second <;> simp [h]
  · rw [inner_compatible, inner_smul_right, hBasis]
    by_cases h : first = second <;> simp [h]
  · rw [inner_compatible, inner_smul_left, hBasis]
    by_cases h : first = second <;> simp [h]
  · rw [inner_compatible, inner_smul_left, inner_smul_right, hBasis]
    by_cases h : first = second <;> simp [h]

theorem complexHilbertBasisRealVector_orthogonal_eq_bot
    (basis : HilbertBasis Index Complex E)
    (inner_compatible : ∀ (first second : E),
      inner Real first second = (inner Complex first second).re) :
    (span Real (Set.range (complexHilbertBasisRealVector basis)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro state hState
  apply basis.repr.injective
  ext index
  rw [basis.repr_apply_apply]
  have hReal :
      inner Real (complexHilbertBasisRealVector basis (.inl index)) state = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span
        (Set.mem_range_self (Sum.inl index : Index ⊕ Index))) hState
  have hImaginary :
      inner Real (complexHilbertBasisRealVector basis (.inr index)) state = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span
        (Set.mem_range_self (Sum.inr index : Index ⊕ Index))) hState
  apply Complex.ext
  · simpa [complexHilbertBasisRealVector, inner_compatible] using hReal
  · simpa [complexHilbertBasisRealVector, inner_compatible,
      inner_smul_left] using hImaginary

/-- A complex Hilbert basis and its `I`-multiple form a real Hilbert basis. -/
def complexHilbertBasisToReal
    (basis : HilbertBasis Index Complex E)
    (inner_compatible : ∀ (first second : E),
      inner Real first second = (inner Complex first second).re) :
    HilbertBasis (Index ⊕ Index) Real E :=
  HilbertBasis.mkOfOrthogonalEqBot
    (complexHilbertBasisRealVector_orthonormal basis inner_compatible)
    (complexHilbertBasisRealVector_orthogonal_eq_bot basis inner_compatible)

@[simp]
theorem complexHilbertBasisToReal_apply
    (basis : HilbertBasis Index Complex E)
    (inner_compatible : ∀ (first second : E),
      inner Real first second = (inner Complex first second).re)
    (index : Index ⊕ Index) :
    complexHilbertBasisToReal basis inner_compatible index =
      complexHilbertBasisRealVector basis index := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) index

end ComplexRealification

section Product

variable {Index LeftIndex RightIndex E F : Type*}
variable [RCLike Index]
variable [DecidableEq LeftIndex] [DecidableEq RightIndex]
variable [NormedAddCommGroup E] [InnerProductSpace Index E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace Index F] [CompleteSpace F]

/-- The disjoint-union family induced by two Hilbert bases on an `L²` product. -/
def hilbertBasisL2ProductVector
    (left : HilbertBasis LeftIndex Index E)
    (right : HilbertBasis RightIndex Index F) :
    LeftIndex ⊕ RightIndex → WithLp 2 (E × F)
  | .inl index => WithLp.toLp 2 (left index, 0)
  | .inr index => WithLp.toLp 2 (0, right index)

theorem hilbertBasisL2ProductVector_orthonormal
    (left : HilbertBasis LeftIndex Index E)
    (right : HilbertBasis RightIndex Index F) :
    Orthonormal Index (hilbertBasisL2ProductVector left right) := by
  classical
  rw [orthonormal_iff_ite]
  intro first second
  rcases first with first | first <;>
    rcases second with second | second <;>
    simp [hilbertBasisL2ProductVector, WithLp.prod_inner_apply,
      orthonormal_iff_ite.mp left.orthonormal,
      orthonormal_iff_ite.mp right.orthonormal]

theorem hilbertBasisL2ProductVector_orthogonal_eq_bot
    (left : HilbertBasis LeftIndex Index E)
    (right : HilbertBasis RightIndex Index F) :
    (span Index (Set.range (hilbertBasisL2ProductVector left right)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro state hState
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply left.repr.injective
    ext index
    rw [left.repr_apply_apply]
    have hCoordinate :
        inner Index
          (hilbertBasisL2ProductVector left right (.inl index)) state = 0 :=
      Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self (Sum.inl index))) hState
    simpa [hilbertBasisL2ProductVector, WithLp.prod_inner_apply] using
      hCoordinate
  · apply right.repr.injective
    ext index
    rw [right.repr_apply_apply]
    have hCoordinate :
        inner Index
          (hilbertBasisL2ProductVector left right (.inr index)) state = 0 :=
      Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self (Sum.inr index))) hState
    simpa [hilbertBasisL2ProductVector, WithLp.prod_inner_apply] using
      hCoordinate

/-- Hilbert bases combine canonically on the `L²` product. -/
def hilbertBasisL2Product
    (left : HilbertBasis LeftIndex Index E)
    (right : HilbertBasis RightIndex Index F) :
    HilbertBasis (LeftIndex ⊕ RightIndex) Index (WithLp 2 (E × F)) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (hilbertBasisL2ProductVector_orthonormal left right)
    (hilbertBasisL2ProductVector_orthogonal_eq_bot left right)

@[simp]
theorem hilbertBasisL2Product_apply
    (left : HilbertBasis LeftIndex Index E)
    (right : HilbertBasis RightIndex Index F)
    (index : LeftIndex ⊕ RightIndex) :
    hilbertBasisL2Product left right index =
      hilbertBasisL2ProductVector left right index := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) index

end Product

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace

/-- The fixed real basis of the full Friedrichs ambient carrier, obtained
from the canonical complex diagonal basis and supplied LL eigenbasis. -/
def programPT12GaugeFixedLLFriedrichsAmbientHilbertBasis
    (period : Real) (hPeriod : period ≠ 0)
    {configuration : GlobalFieldConfiguration period hPeriod}
    {iota : Type*} [DecidableEq iota]
    (analysis : GlobalAnalysisData period hPeriod configuration)
    {LLMode : Type*} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode) :
    HilbertBasis
      ((ProgramPGlobalGaugeFixedSpectralHessianMode iota ⊕
          ProgramPGlobalGaugeFixedSpectralHessianMode iota) ⊕ LLMode)
      Real
      (ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert
        period hPeriod iota analysis) := by
  letI : DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode iota) :=
    Classical.decEq _
  exact hilbertBasisL2Product
    (complexHilbertBasisToReal
      (complexDiagonalBasis (ProgramPGlobalGaugeFixedSpectralHessianMode iota))
      (fun _ _ => real_inner_eq_re_inner Complex _ _))
    llSpectral.basis

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsAmbientHilbertBasis4D
end JanusFormal
