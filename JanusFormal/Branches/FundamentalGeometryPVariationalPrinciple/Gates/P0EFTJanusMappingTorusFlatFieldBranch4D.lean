import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalFieldBridge4D

/-!
# A nonempty PT-invariant flat field branch on the effective mapping torus

This gate supplies an explicit diagonal branch on the actual D8 quotient
bases.  Both metric sectors use the Minkowski matrix, the relative root is the
identity, matter is zero, and the throat embedding is the effective quotient
inclusion.  It proves nonemptiness and PT invariance of this algebraic branch;
no stationarity or stability claim is made.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusFlatFieldBranch4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusLLBraneAuxiliaryActionVariation
open P0EFTJanusGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusGlobalFieldBridge4D

/-- Minkowski metric packaged with the exact determinant-sign and Lorentz
congruence witnesses used by the global field configuration. -/
def minkowskiLorentzMetricPoint4 : LorentzMetricPoint4 where
  metric := minkowskiMetric4
  orientation := -1
  orientation_ne_zero := by norm_num
  metric_symmetric := by
    simp [minkowskiMetric4]
  metric_mem_domain := by
    simp [fixedDeterminantSignDomain, minkowskiMetric4,
      Matrix.det_diagonal]
  lorentzian := by
    refine ⟨1, 1, ?_, ?_⟩
    · constructor <;> simp
    · simp [minkowskiMetric4]

/-- Zero LL point data, sufficient to make the induced slot concrete. -/
def zeroLLPointData : LLBraneAuxiliaryPointData where
  gammaInv := 0
  inducedMetric := 0
  Phi := 0
  gaugeFlux := 0
  gaugeCoupling := 0
  measureConstant := 0
  gammaInvSymmetric := by simp
  inducedMetricSymmetric := by simp

/-- Explicit independent fields on the effective D8 spacetime and throat. -/
def flatDiagonalIndependentFields (period : Real) (hPeriod : period ≠ 0) :
    IndependentFields
      (EffectiveJanusSpacetime period hPeriod)
      (EffectiveJanusThroat period hPeriod)
      Real Unit Unit Unit Unit where
  plusMetric := fun _ ↦ minkowskiLorentzMetricPoint4
  minusMetric := fun _ ↦ minkowskiLorentzMetricPoint4
  plusMatter := fun _ ↦ 0
  minusMatter := fun _ ↦ 0
  plusGauge := fun _ ↦ ()
  minusGauge := fun _ ↦ ()
  plusGhost := fun _ ↦ ()
  minusGhost := fun _ ↦ ()
  plusAuxiliary := fun _ ↦ ()
  minusAuxiliary := fun _ ↦ ()
  throatEmbedding := fixedThroatQuotientInclusion period hPeriod
  llIndependent := fun _ ↦ ()

/-- Explicit induced data for the diagonal branch.  It is not promoted to a
root induction on every independent pair; that stronger global root problem is
kept separate. -/
def flatDiagonalInducedFields (period : Real) (hPeriod : period ≠ 0) :
    InducedFields
      (EffectiveJanusSpacetime period hPeriod)
      (EffectiveJanusThroat period hPeriod) Unit where
  plusInverseMetric := fun _ ↦ minkowskiMetric4⁻¹
  minusInverseMetric := fun _ ↦ minkowskiMetric4⁻¹
  plusVolumeDensity := fun _ ↦ Real.sqrt |Matrix.det minkowskiMetric4|
  minusVolumeDensity := fun _ ↦ Real.sqrt |Matrix.det minkowskiMetric4|
  relativeRoot := fun _ ↦ 1
  throatGeometry := fun _ ↦ ()
  llPointData := fun _ ↦ zeroLLPointData

@[simp] theorem flatDiagonal_plusInverse_exact
    (period : Real) (hPeriod : period ≠ 0)
    (point : EffectiveJanusSpacetime period hPeriod) :
    (flatDiagonalInducedFields period hPeriod).plusInverseMetric point =
      ((flatDiagonalIndependentFields period hPeriod).plusMetric point).metric⁻¹ :=
  rfl

@[simp] theorem flatDiagonal_minusInverse_exact
    (period : Real) (hPeriod : period ≠ 0)
    (point : EffectiveJanusSpacetime period hPeriod) :
    (flatDiagonalInducedFields period hPeriod).minusInverseMetric point =
      ((flatDiagonalIndependentFields period hPeriod).minusMetric point).metric⁻¹ :=
  rfl

@[simp] theorem flatDiagonal_plusVolume_exact
    (period : Real) (hPeriod : period ≠ 0)
    (point : EffectiveJanusSpacetime period hPeriod) :
    (flatDiagonalInducedFields period hPeriod).plusVolumeDensity point =
      Real.sqrt |Matrix.det
        ((flatDiagonalIndependentFields period hPeriod).plusMetric point).metric| :=
  rfl

/-- The identity is an exact relative root on the diagonal branch. -/
theorem flatDiagonal_relativeRoot_square
    (period : Real) (hPeriod : period ≠ 0)
    (point : EffectiveJanusSpacetime period hPeriod) :
    let independent := flatDiagonalIndependentFields period hPeriod
    let induced := flatDiagonalInducedFields period hPeriod
    induced.relativeRoot point * induced.relativeRoot point =
    induced.plusInverseMetric point * (independent.minusMetric point).metric := by
  dsimp [flatDiagonalIndependentFields, flatDiagonalInducedFields]
  change (1 : P0EFTJanusGlobalFieldConfiguration4D.Matrix4) * 1 =
    minkowskiMetric4⁻¹ * minkowskiMetric4
  rw [Matrix.nonsing_inv_mul]
  · simp
  · exact isUnit_iff_ne_zero.mpr minkowskiLorentzMetricPoint4.det_ne_zero

/-- Identity fibre actions combined with the effective base PT actions. -/
def flatIndependentPTData (period : Real) (hPeriod : period ≠ 0) :=
  effectiveIndependentPTData period hPeriod Real Unit Unit Unit Unit
    (AlgebraicInvolution.identity Real)
    (AlgebraicInvolution.identity Unit)
    (AlgebraicInvolution.identity Unit)
    (AlgebraicInvolution.identity Unit)
    (AlgebraicInvolution.identity Unit)

/-- The explicit diagonal branch is fixed by the same effective PT exchange. -/
theorem flatDiagonalIndependentFields_pt_fixed
    (period : Real) (hPeriod : period ≠ 0) :
    independentPTExchange (flatIndependentPTData period hPeriod)
        (flatDiagonalIndependentFields period hPeriod) =
      flatDiagonalIndependentFields period hPeriod := by
  apply IndependentFields.ext
  all_goals funext point
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact effectiveThroatEmbedding_transform_fixed period hPeriod point
  · rfl

/-- Nonempty same-object branch delivered by this gate. -/
theorem effective_flat_diagonal_branch_nonempty
    (period : Real) (hPeriod : period ≠ 0) :
    ∃ independent : IndependentFields
        (EffectiveJanusSpacetime period hPeriod)
        (EffectiveJanusThroat period hPeriod)
        Real Unit Unit Unit Unit,
      ∃ induced : InducedFields
          (EffectiveJanusSpacetime period hPeriod)
          (EffectiveJanusThroat period hPeriod) Unit,
        independent.throatEmbedding =
            fixedThroatQuotientInclusion period hPeriod ∧
          independentPTExchange (flatIndependentPTData period hPeriod) independent =
            independent ∧
          (∀ point,
            induced.relativeRoot point * induced.relativeRoot point =
              induced.plusInverseMetric point * (independent.minusMetric point).metric) := by
  refine ⟨flatDiagonalIndependentFields period hPeriod,
    flatDiagonalInducedFields period hPeriod, rfl,
    flatDiagonalIndependentFields_pt_fixed period hPeriod, ?_⟩
  exact flatDiagonal_relativeRoot_square period hPeriod

end

end P0EFTJanusMappingTorusFlatFieldBranch4D
end JanusFormal
