import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHeatOperator4D

/-!
# Nuclear rank-one expansion of the product-throat heat operator

The bounded diagonal operator on the full monopole-degenerate product
spectral Hilbert space is the operator-norm sum of its rank-one spectral
projections.  The component norms are summable and the resulting nuclear
trace is the previously identified product-throat trace.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHeatOperatorNuclearExpansion4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatNuclearHeatTrace4D
open P0EFTJanusProductThroatHeatOperator4D
open scoped ENNReal lp

/-- Canonical Hilbert basis of the full degenerate product spectrum. -/
def productThroatHeatBasis (data : ProductThroatSpectralData) :
    HilbertBasis (ProductThroatHeatMode data) Complex
      (ProductThroatHeatHilbert data) :=
  HilbertBasis.ofRepr
    (LinearIsometryEquiv.refl Complex (ProductThroatHeatHilbert data))

@[simp]
theorem productThroatHeatBasis_eq_single
    (data : ProductThroatSpectralData) (mode : ProductThroatHeatMode data) :
    productThroatHeatBasis data mode = lp.single 2 mode (1 : Complex) := by
  rw [← HilbertBasis.repr_symm_single (productThroatHeatBasis data) mode]
  change (productThroatHeatBasis data).repr.symm
    (lp.single 2 mode (1 : Complex)) = lp.single 2 mode (1 : Complex)
  rw [show (productThroatHeatBasis data).repr =
      LinearIsometryEquiv.refl Complex (ProductThroatHeatHilbert data) by rfl]
  simpa only [LinearIsometryEquiv.coe_refl, id_eq] using
    (LinearIsometryEquiv.refl Complex
      (ProductThroatHeatHilbert data)).symm_apply_apply
        (lp.single 2 mode (1 : Complex))

theorem productThroatHeatBasis_norm
    (data : ProductThroatSpectralData) (mode : ProductThroatHeatMode data) :
    ‖productThroatHeatBasis data mode‖ = 1 :=
  (HilbertBasis.orthonormal (productThroatHeatBasis data)).1 mode

/-- One rank-one summand of the full product heat operator. -/
def productThroatHeatRankOne
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data :=
  (lp.evalCLM Complex
      (fun _ : ProductThroatHeatMode data => Complex) 2 mode).smulRight
    ((productThroatHeatWeight data time fold twist mode : Complex) •
      productThroatHeatBasis data mode)

@[simp]
theorem productThroatHeatRankOne_apply
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data)
    (state : ProductThroatHeatHilbert data) :
    productThroatHeatRankOne data time fold twist mode state =
      state mode •
        ((productThroatHeatWeight data time fold twist mode : Complex) •
          productThroatHeatBasis data mode) := by
  rfl

private theorem productThroatEvalCLM_opNorm_le_one
    (data : ProductThroatSpectralData) (mode : ProductThroatHeatMode data) :
    ‖lp.evalCLM Complex (fun _ : ProductThroatHeatMode data => Complex) 2 mode‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro state
  change ‖state mode‖ ≤ 1 * ‖state‖
  simpa using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    state mode

theorem productThroatHeatRankOne_opNorm_le
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    ‖productThroatHeatRankOne data time fold twist mode‖ ≤
      productThroatHeatWeight data time fold twist mode := by
  rw [productThroatHeatRankOne, ContinuousLinearMap.norm_smulRight_apply,
    norm_smul, productThroatHeatBasis_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (productThroatHeatWeight_nonnegative data time fold twist mode)]
  exact mul_le_of_le_one_left
    (productThroatHeatWeight_nonnegative data time fold twist mode)
    (productThroatEvalCLM_opNorm_le_one data mode)

theorem productThroatHeatRankOne_norm_summable
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : ProductThroatHeatMode data =>
      ‖productThroatHeatRankOne data time fold twist mode‖) :=
  (productThroatHeatWeight_summable data time fold twist).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (productThroatHeatRankOne_opNorm_le data time fold twist)

theorem productThroatHeatRankOne_summable
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    Summable (productThroatHeatRankOne data time fold twist) :=
  Summable.of_norm
    (productThroatHeatRankOne_norm_summable data time fold twist)

def productThroatHeatNuclearSum
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data :=
  ∑' mode : ProductThroatHeatMode data,
    productThroatHeatRankOne data time fold twist mode

theorem productThroatHeatRankOne_on_basis
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode other : ProductThroatHeatMode data) :
    productThroatHeatRankOne data time fold twist mode
        (productThroatHeatBasis data other) =
      if mode = other then
        (productThroatHeatWeight data time fold twist other : Complex) •
          productThroatHeatBasis data other
      else 0 := by
  by_cases hMode : mode = other
  · subst mode
    simp [productThroatHeatRankOne_apply, productThroatHeatBasis_eq_single]
  · simp [productThroatHeatRankOne_apply, productThroatHeatBasis_eq_single,
      lp.single_apply, hMode]

theorem productThroatHeatNuclearSum_on_basis
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatHeatNuclearSum data time fold twist
        (productThroatHeatBasis data mode) =
      (productThroatHeatWeight data time fold twist mode : Complex) •
        productThroatHeatBasis data mode := by
  rw [productThroatHeatNuclearSum]
  rw [show
      (∑' other : ProductThroatHeatMode data,
        productThroatHeatRankOne data time fold twist other)
          (productThroatHeatBasis data mode) =
        ∑' other : ProductThroatHeatMode data,
          productThroatHeatRankOne data time fold twist other
            (productThroatHeatBasis data mode) by
    simpa only [ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply Complex (ProductThroatHeatHilbert data)
        (productThroatHeatBasis data mode)).map_tsum
          (productThroatHeatRankOne_summable data time fold twist)]
  rw [tsum_eq_single mode]
  · simp
  · intro other hOther
    simp [productThroatHeatRankOne_on_basis, hOther]

/-- The nuclear rank-one series is exactly the bounded product heat operator. -/
theorem productThroatHeatNuclearSum_eq_operator
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    productThroatHeatNuclearSum data time fold twist =
      productThroatHeatOperator data time fold twist := by
  have hDense : Dense
      (Submodule.span Complex (Set.range (productThroatHeatBasis data)) :
        Set (ProductThroatHeatHilbert data)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact HilbertBasis.dense_span (productThroatHeatBasis data)
  apply ContinuousLinearMap.ext_on
    (s := Set.range (productThroatHeatBasis data)) hDense
  rintro _ ⟨mode, rfl⟩
  rw [productThroatHeatNuclearSum_on_basis]
  ext other
  rw [productThroatHeatOperator_apply, productThroatHeatBasis_eq_single]
  by_cases hOther : other = mode
  · subst other
    change (productThroatHeatWeight data time fold twist mode : Complex) *
      ((lp.single 2 mode (1 : Complex) : ProductThroatHeatHilbert data) mode) =
        (productThroatHeatWeight data time fold twist mode : Complex) *
          ((lp.single 2 mode (1 : Complex) : ProductThroatHeatHilbert data) mode)
    rfl
  · change (productThroatHeatWeight data time fold twist mode : Complex) *
      ((lp.single 2 mode (1 : Complex) : ProductThroatHeatHilbert data) other) =
        (productThroatHeatWeight data time fold twist other : Complex) *
          ((lp.single 2 mode (1 : Complex) : ProductThroatHeatHilbert data) other)
    rw [lp.single_apply]
    simp [hOther]

/-- Concrete nuclear certificate on the infinite product-throat Hilbert
space. -/
structure ProductThroatHeatNuclearCertificate
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) where
  components : ProductThroatHeatMode data →
    (ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data)
  summable_norm : Summable (fun mode => ‖components mode‖)
  operator_eq_tsum :
    productThroatHeatOperator data time fold twist = ∑' mode, components mode
  trace_eq :
    productThroatHeatOperatorDiagonalTrace data time fold twist =
      productThroatNuclearHeatTrace data time fold twist

def productThroatHeatNuclearCertificate
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    ProductThroatHeatNuclearCertificate data time fold twist where
  components := productThroatHeatRankOne data time fold twist
  summable_norm := productThroatHeatRankOne_norm_summable data time fold twist
  operator_eq_tsum :=
    (productThroatHeatNuclearSum_eq_operator data time fold twist).symm
  trace_eq :=
    productThroatHeatOperatorDiagonalTrace_eq_nuclearTrace data time fold twist

end

end P0EFTJanusProductThroatHeatOperatorNuclearExpansion4D
end JanusFormal
