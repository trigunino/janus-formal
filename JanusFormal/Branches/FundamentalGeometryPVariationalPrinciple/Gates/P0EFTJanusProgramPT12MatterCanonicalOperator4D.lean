import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterGraphRealization4D

namespace JanusFormal.P0EFTJanusProgramPT12MatterCanonicalOperator4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalRealFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D

attribute [local instance] programPPrimitiveSpinCMatterHilbertRealInnerProductSpace
variable (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)

/-- The exact signed Hessian on the canonical coefficient L² space. -/
abbrev matterCanonicalOperator := complexDiagonalRealOperator ProgramPPrimitiveSpinCMatterMode
  (programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared)

theorem matterCanonicalOperator_selfAdjoint : IsSelfAdjoint
    (matterCanonicalOperator period hPeriod massSquared) :=
  complexDiagonalRealOperator_isSelfAdjoint _ _

def matterCanonicalFiniteEmbedding : ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
    ProgramPPrimitiveSpinCMatterHilbert :=
  programPPrimitiveSpinCMatterFiniteHilbertEmbedding.restrictScalars Real

@[simp] theorem matterCanonicalFiniteEmbedding_apply
    (x : ProgramPPrimitiveSpinCMatterFiniteCoefficients) (mode : ProgramPPrimitiveSpinCMatterMode) :
    matterCanonicalFiniteEmbedding x mode = x mode :=
  programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply x mode

theorem matterCanonicalFiniteEmbedding_denseRange : DenseRange matterCanonicalFiniteEmbedding :=
  programPPrimitiveSpinCMatterFiniteHilbertEmbedding_range_dense

def matterCanonicalFiniteDomain (x : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (matterCanonicalOperator period hPeriod massSquared).domain :=
  ⟨matterCanonicalFiniteEmbedding x,
    ⟨matterCanonicalFiniteEmbedding (programPPrimitiveSpinCMatterFiniteHessian period hPeriod massSquared x),
      fun mode => by
        simpa only [matterCanonicalFiniteEmbedding_apply] using
          programPPrimitiveSpinCMatterFiniteHessian_apply period hPeriod massSquared x mode⟩⟩

@[simp] theorem matterCanonicalFiniteDomain_value (x : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (matterCanonicalFiniteDomain period hPeriod massSquared x).val = matterCanonicalFiniteEmbedding x := rfl

theorem matterCanonicalOperator_finite_apply (x : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    matterCanonicalOperator period hPeriod massSquared (matterCanonicalFiniteDomain period hPeriod massSquared x) =
    matterCanonicalFiniteEmbedding (programPPrimitiveSpinCMatterFiniteHessian period hPeriod massSquared x) := by
  ext mode
  rw [complexDiagonalRealOperator_apply]
  change _ * matterCanonicalFiniteEmbedding x mode = matterCanonicalFiniteEmbedding _ mode
  simp only [matterCanonicalFiniteEmbedding_apply]
  exact (programPPrimitiveSpinCMatterFiniteHessian_apply period hPeriod massSquared x mode).symm

theorem matterCanonicalOperator_finite_pairing (x y : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    inner Real (matterCanonicalOperator period hPeriod massSquared
      (matterCanonicalFiniteDomain period hPeriod massSquared x)) (matterCanonicalFiniteEmbedding y) =
    programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
      (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod massSquared x)
      (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod massSquared y) := by
  rw [matterCanonicalOperator_finite_apply, programPPrimitiveSpinCMatterGraphForm_apply]
  change inner Real (matterCanonicalFiniteEmbedding (programPPrimitiveSpinCMatterFiniteHessian period hPeriod massSquared x))
      (matterCanonicalFiniteEmbedding y) = inner Real (matterCanonicalFiniteEmbedding x)
      (matterCanonicalFiniteEmbedding (programPPrimitiveSpinCMatterFiniteHessian period hPeriod massSquared y))
  have h := complexDiagonalRealOperator_isFormalAdjoint_self _ _
    (matterCanonicalFiniteDomain period hPeriod massSquared x)
    (matterCanonicalFiniteDomain period hPeriod massSquared y)
  simpa only [matterCanonicalOperator_finite_apply, matterCanonicalFiniteDomain_value] using h

theorem matterCanonicalOperator_graph_iff (x y : ProgramPPrimitiveSpinCMatterHilbert) :
    (x, y) ∈ (matterCanonicalOperator period hPeriod massSquared).graph ↔
    (x, y) ∈ (complexDiagonalOperator ProgramPPrimitiveSpinCMatterMode
      (programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared)).graph := Iff.rfl

end
end JanusFormal.P0EFTJanusProgramPT12MatterCanonicalOperator4D
