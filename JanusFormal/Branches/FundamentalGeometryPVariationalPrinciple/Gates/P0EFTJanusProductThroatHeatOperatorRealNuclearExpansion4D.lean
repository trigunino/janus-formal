import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHeatOperatorNuclearExpansion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceProductThroatRealHeatTraceExpansionFrontend4D

/-!
# Real nuclear expansion of the product-throat heat operator

Each complex spectral mode contributes its two real directions `1` and `I`.
The resulting real rank-one expansion has twice the complex spectral trace.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHeatOperatorRealNuclearExpansion4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatNuclearHeatTrace4D
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatHeatOperatorNuclearExpansion4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPReferenceProductThroatHeatOperatorIdentification4D
open P0EFTJanusProgramPReferenceProductThroatRealHeatTraceContinuity4D
open P0EFTJanusProgramPReferenceProductThroatRealHeatTraceExpansionFrontend4D
open scoped ENNReal lp

universe u v

/-- One of the two real orthonormal directions attached to a complex mode. -/
def productThroatHeatRealBasisVector
    (data : ProductThroatSpectralData)
    (mode : ProductThroatHeatMode data) (axis : Fin 2) :
    ProductThroatHeatHilbert data :=
  lp.single 2 mode (Complex.orthonormalBasisOneI axis)

@[simp] theorem productThroatHeatRealBasisVector_norm
    (data : ProductThroatSpectralData)
    (mode : ProductThroatHeatMode data) (axis : Fin 2) :
    ‖productThroatHeatRealBasisVector data mode axis‖ = 1 := by
  rw [productThroatHeatRealBasisVector, lp.norm_single (by norm_num)]
  exact Complex.orthonormalBasisOneI.norm_eq_one axis

@[simp] theorem productThroatHeatRealBasisVector_inner_self
    (data : ProductThroatSpectralData)
    (mode : ProductThroatHeatMode data) (axis : Fin 2) :
    inner Real (productThroatHeatRealBasisVector data mode axis)
        (productThroatHeatRealBasisVector data mode axis) = 1 := by
  rw [real_inner_self_eq_norm_sq,
    productThroatHeatRealBasisVector_norm]
  norm_num

/-- One real rank-one component, indexed by a complex mode and a real axis. -/
def productThroatHeatRealRankOne
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (index : ProductThroatHeatMode data × Fin 2) :
    ProductThroatHeatHilbert data →L[Real]
      ProductThroatHeatHilbert data :=
  productThroatHeatWeight data time fold twist index.1 •
    InnerProductSpace.rankOne Real
      (productThroatHeatRealBasisVector data index.1 index.2)
      (productThroatHeatRealBasisVector data index.1 index.2)

@[simp] theorem productThroatHeatRealRankOne_norm
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (index : ProductThroatHeatMode data × Fin 2) :
    ‖productThroatHeatRealRankOne data time fold twist index‖ =
      productThroatHeatWeight data time fold twist index.1 := by
  rw [productThroatHeatRealRankOne, norm_smul,
    InnerProductSpace.norm_rankOne,
    productThroatHeatRealBasisVector_norm, Real.norm_eq_abs,
    abs_of_nonneg
      (productThroatHeatWeight_nonnegative data time fold twist index.1)]
  norm_num

theorem productThroatHeatRealWeight_summable
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    Summable (fun index : ProductThroatHeatMode data × Fin 2 =>
      productThroatHeatWeight data time fold twist index.1) := by
  apply (summable_prod_of_nonneg (fun index =>
    productThroatHeatWeight_nonnegative data time fold twist index.1)).2
  constructor
  · intro mode
    exact Summable.of_finite
  · refine
      (productThroatHeatWeight_summable data time fold twist).mul_left 2
        |>.congr ?_
    intro mode
    rw [tsum_fintype, Fin.sum_univ_two]
    ring

theorem productThroatHeatRealRankOne_summable
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    Summable (productThroatHeatRealRankOne data time fold twist) :=
  Summable.of_norm (by
    simpa only [productThroatHeatRealRankOne_norm] using
      productThroatHeatRealWeight_summable data time fold twist)

/-- Restricting one complex spectral projector to real scalars produces its
two real rank-one projectors. -/
theorem productThroatHeatRankOne_restrictScalars_eq_real_sum
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    (productThroatHeatRankOne data time fold twist mode).restrictScalars Real =
      ∑ axis : Fin 2,
        productThroatHeatRealRankOne data time fold twist (mode, axis) := by
  rw [Fin.sum_univ_two]
  apply ContinuousLinearMap.ext
  intro state
  ext other
  change productThroatHeatRankOne data time fold twist mode state other = _
  rw [productThroatHeatRankOne_apply]
  simp only [productThroatHeatRealRankOne, add_apply, smul_apply,
    InnerProductSpace.rankOne_apply]
  have hInnerZero :
      inner Real (productThroatHeatRealBasisVector data mode 0) state =
        (state mode).re := by
    rw [productThroatHeatRealBasisVector, lp.inner_single_left]
    simp [Complex.coe_orthonormalBasisOneI, Complex.inner]
  have hInnerOne :
      inner Real (productThroatHeatRealBasisVector data mode 1) state =
        (state mode).im := by
    rw [productThroatHeatRealBasisVector, lp.inner_single_left]
    simp [Complex.coe_orthonormalBasisOneI, Complex.inner]
  rw [hInnerZero, hInnerOne, productThroatHeatBasis_eq_single,
    ← lp.single_smul]
  by_cases hOther : other = mode
  · subst other
    simp only [productThroatHeatRealBasisVector,
      Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  · simp [productThroatHeatRealBasisVector, lp.single_apply, hOther]

/-- The real rank-one series is the realification of the product heat
operator. -/
theorem productThroatHeatOperatorReal_eq_tsum_rankOne
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    productThroatHeatOperatorReal data time fold twist =
      ∑' index,
        productThroatHeatRealRankOne data time fold twist index := by
  let restriction := ContinuousLinearMap.restrictScalarsIsometry Complex
    (ProductThroatHeatHilbert data) (ProductThroatHeatHilbert data) Real Real
  calc
    productThroatHeatOperatorReal data time fold twist =
        (productThroatHeatNuclearSum data time fold twist).restrictScalars
          Real :=
      congrArg (fun operator => operator.restrictScalars Real)
        (productThroatHeatNuclearSum_eq_operator data time fold twist).symm
    _ = ∑' mode,
          (productThroatHeatRankOne data time fold twist mode).restrictScalars
            Real := by
      change restriction.toContinuousLinearMap
          (∑' mode, productThroatHeatRankOne data time fold twist mode) = _
      exact restriction.toContinuousLinearMap.map_tsum
        (productThroatHeatRankOne_summable data time fold twist)
    _ = ∑' mode, ∑ axis : Fin 2,
          productThroatHeatRealRankOne data time fold twist (mode, axis) := by
      apply tsum_congr
      intro mode
      exact productThroatHeatRankOne_restrictScalars_eq_real_sum
        data time fold twist mode
    _ = ∑' index,
          productThroatHeatRealRankOne data time fold twist index := by
      rw [(productThroatHeatRealRankOne_summable
        data time fold twist).tsum_prod]
      apply tsum_congr
      intro mode
      rw [tsum_fintype]

/-- Explicit intrinsic-trace presentation of the real product heat operator. -/
def productThroatHeatOperatorRealRankOneExpansion
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    SummableRankOneOperatorExpansion.{v}
      (productThroatHeatOperatorReal data time fold twist) where
  Index := ULift.{v} (ProductThroatHeatMode data × Fin 2)
  coefficient := fun index =>
    productThroatHeatWeight data time fold twist index.down.1
  leftVector := fun index =>
    productThroatHeatRealBasisVector data index.down.1 index.down.2
  rightVector := fun index =>
    productThroatHeatRealBasisVector data index.down.1 index.down.2
  summable_nuclearNorm := by
    have hBase : Summable (fun index :
        ProductThroatHeatMode data × Fin 2 =>
        |productThroatHeatWeight data time fold twist index.1| *
          ‖productThroatHeatRealBasisVector data index.1 index.2‖ *
          ‖productThroatHeatRealBasisVector data index.1 index.2‖) := by
      refine
        (productThroatHeatRealWeight_summable data time fold twist).congr ?_
      intro index
      rw [productThroatHeatRealBasisVector_norm, mul_one, mul_one,
        abs_of_nonneg
          (productThroatHeatWeight_nonnegative data time fold twist index.1)]
    exact (Equiv.ulift.summable_iff.mpr hBase).congr fun _ => rfl
  trace_summable := by
    have hBase : Summable (fun index :
        ProductThroatHeatMode data × Fin 2 =>
        productThroatHeatWeight data time fold twist index.1 *
          inner Real (productThroatHeatRealBasisVector data index.1 index.2)
            (productThroatHeatRealBasisVector data index.1 index.2)) := by
      simpa only [productThroatHeatRealBasisVector_inner_self, mul_one] using
        productThroatHeatRealWeight_summable data time fold twist
    exact (Equiv.ulift.summable_iff.mpr hBase).congr fun _ => rfl
  operator_eq_tsum := by
    calc
      productThroatHeatOperatorReal data time fold twist =
          ∑' index : ProductThroatHeatMode data × Fin 2,
            productThroatHeatRealRankOne data time fold twist index :=
        productThroatHeatOperatorReal_eq_tsum_rankOne data time fold twist
      _ = ∑' index : ULift.{v} (ProductThroatHeatMode data × Fin 2),
            productThroatHeatRealRankOne data time fold twist index.down :=
        (Equiv.ulift.tsum_eq
          (productThroatHeatRealRankOne data time fold twist)).symm
      _ = _ := by
        rfl

/-- Realification doubles the explicit complex spectral trace. -/
@[simp] theorem productThroatHeatOperatorRealRankOneExpansion_expansionTrace
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    (productThroatHeatOperatorRealRankOneExpansion.{v}
        data time fold twist).expansionTrace =
      2 * productThroatNuclearHeatTrace data time fold twist := by
  unfold SummableRankOneOperatorExpansion.expansionTrace
    productThroatHeatOperatorRealRankOneExpansion
  change (∑' index : ULift.{v} (ProductThroatHeatMode data × Fin 2),
    productThroatHeatWeight data time fold twist index.down.1 *
      inner Real
        (productThroatHeatRealBasisVector data index.down.1 index.down.2)
        (productThroatHeatRealBasisVector data index.down.1 index.down.2)) = _
  simp only [productThroatHeatRealBasisVector_inner_self, mul_one]
  have hLift :
      (∑' index : ULift.{v} (ProductThroatHeatMode data × Fin 2),
        productThroatHeatWeight data time fold twist index.down.1) =
      ∑' index : ProductThroatHeatMode data × Fin 2,
        productThroatHeatWeight data time fold twist index.1 := by
    simpa only [Function.comp_apply, Equiv.ulift_apply] using
      (Equiv.ulift.tsum_eq (fun index : ProductThroatHeatMode data × Fin 2 =>
        productThroatHeatWeight data time fold twist index.1))
  rw [hLift]
  rw [(productThroatHeatRealWeight_summable
    data time fold twist).tsum_prod]
  simp_rw [tsum_fintype, Fin.sum_univ_two]
  calc
    (∑' mode : ProductThroatHeatMode data,
        (productThroatHeatWeight data time fold twist mode +
          productThroatHeatWeight data time fold twist mode)) =
        ∑' mode : ProductThroatHeatMode data,
          2 * productThroatHeatWeight data time fold twist mode := by
      apply tsum_congr
      intro mode
      ring
    _ = 2 * productThroatHeatOperatorDiagonalTrace data time fold twist := by
      rw [tsum_mul_left]
      rfl
    _ = 2 * productThroatNuclearHeatTrace data time fold twist := by
      rw [productThroatHeatOperatorDiagonalTrace_eq_nuclearTrace]

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Operator conjugacy alone now closes the exact real heat-trace
normalization. -/
def referenceProductThroatRealHeatTraceIdentificationData_of_operatorIdentification
    (productData : ProductThroatSpectralData) (fold : Fold)
    (twist : CircleTwist)
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (operatorIdentification :
      ReferenceProductThroatHeatOperatorIdentificationData productData fold
        (fun _ => twist) nuclear) :
    ReferenceProductThroatRealHeatTraceIdentificationData
      productData fold twist nuclear :=
  referenceProductThroatRealHeatTraceIdentificationData_of_expansion
    productData fold twist nuclear operatorIdentification
    (fun time =>
      productThroatHeatOperatorRealRankOneExpansion.{v}
        productData time fold twist)
    (fun time =>
      productThroatHeatOperatorRealRankOneExpansion_expansionTrace.{v}
        productData time fold twist)

end
end P0EFTJanusProductThroatHeatOperatorRealNuclearExpansion4D
end JanusFormal
