import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRealJordanPartitionSelector4D
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.JordanChevalley

/-!
# Matrix-level bridge to the positive real Jordan selector

The natural raw-matrix hypothesis is that the real characteristic polynomial
splits and that all of its roots are strictly positive.  Mathlib proves that
the minimal polynomial then also splits and has only strictly positive roots.

The current Mathlib API does not provide Jordan normal form or rational
canonical form.  `LinearAlgebra/Eigenspace/Triangularizable.lean` explicitly
lists the definition/construction of triangularizable endomorphisms as a TODO.
`LinearAlgebra/JordanChevalley.lean` supplies a commuting nilpotent plus
semisimple decomposition, but not a basis of Jordan chains or a similarity to
canonical blocks.  Consequently `PositiveRealJordanBasisBridge4` below is the
single external presentation theorem still needed.  It is a proposition and
is never installed as a global assumption.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRealJordanPresentationBridge4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions
open Polynomial
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveRealJordanPartitionSelector4D

abbrev Matrix4 :=
  P0EFTJanusPositiveRealJordanPartitionSelector4D.Matrix4

/-- Natural spectral condition on a raw real matrix.  Since the coefficient
field is `Real`, splitting already says that every algebraic root is real. -/
def PositiveRealSplitCharpoly4 (target : Matrix4) : Prop :=
  target.charpoly.Splits ∧
    ∀ eigenvalue : Real, target.charpoly.IsRoot eigenvalue → 0 < eigenvalue

/-- Redundant but useful charpoly/minpoly formulation of the same condition. -/
def PositiveRealSplitCharMinpoly4 (target : Matrix4) : Prop :=
  target.charpoly.Splits ∧
    (minpoly Real target).Splits ∧
    (∀ eigenvalue : Real,
      target.charpoly.IsRoot eigenvalue → 0 < eigenvalue) ∧
    (∀ eigenvalue : Real,
      (minpoly Real target).IsRoot eigenvalue → 0 < eigenvalue)

theorem positiveRealSplitCharpoly_minpoly_splits
    (target : Matrix4) (hTarget : PositiveRealSplitCharpoly4 target) :
    (minpoly Real target).Splits :=
  hTarget.1.of_dvd (Matrix.charpoly_monic target).ne_zero
    (Matrix.minpoly_dvd_charpoly target)

theorem positiveRealSplitCharpoly_minpoly_root_pos
    (target : Matrix4) (hTarget : PositiveRealSplitCharpoly4 target)
    (eigenvalue : Real) (hRoot : (minpoly Real target).IsRoot eigenvalue) :
    0 < eigenvalue :=
  hTarget.2 eigenvalue
    (hRoot.dvd (Matrix.minpoly_dvd_charpoly target))

theorem positiveRealSplitCharMinpoly_iff
    (target : Matrix4) :
    PositiveRealSplitCharMinpoly4 target ↔
      PositiveRealSplitCharpoly4 target := by
  constructor
  · intro hTarget
    exact ⟨hTarget.1, hTarget.2.2.1⟩
  · intro hTarget
    exact ⟨hTarget.1,
      positiveRealSplitCharpoly_minpoly_splits target hTarget,
      hTarget.2,
      positiveRealSplitCharpoly_minpoly_root_pos target hTarget⟩

/-- What Jordan--Chevalley already supplies over `Real`.  This is strictly
weaker than a Jordan-chain basis and therefore does not construct a member of
`PositiveRealJordanPresentation4`. -/
theorem matrix4_jordanChevalley_available (target : Matrix4) :
    ∃ nilpotent semisimple : Module.End Real (Fin 4 → Real),
      IsNilpotent nilpotent ∧ semisimple.IsSemisimple ∧
        Matrix.toLin' target = nilpotent + semisimple := by
  obtain ⟨nilpotent, _hNilpotentPolynomial, semisimple,
      _hSemisimplePolynomial, hNilpotent, hSemisimple, hSum⟩ :=
    Module.End.exists_isNilpotent_isSemisimple
      (f := Matrix.toLin' target)
  exact ⟨nilpotent, semisimple, hNilpotent, hSemisimple, hSum⟩

/-- Exact external theorem absent from the current Mathlib API: assemble a
real Jordan-chain basis, enumerate its four-dimensional block partition, and
package the resulting similarity in the unified presentation type. -/
def PositiveRealJordanBasisBridge4 : Prop :=
  ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
    HasPositiveRealJordanPresentation target

/-- The bridge is intentionally exposed only as a local hypothesis. -/
theorem hasPositiveRealJordanPresentation_of_bridge
    (bridge : PositiveRealJordanBasisBridge4)
    (target : Matrix4) (hTarget : PositiveRealSplitCharpoly4 target) :
    HasPositiveRealJordanPresentation target :=
  bridge target hTarget

def HasSylvesterRegularRealSquareRoot (target : Matrix4) : Prop :=
  ∃ root : Matrix4,
    root * root = target ∧
      Function.Bijective (sylvesterOperator root)

theorem hasSylvesterRegularRealSquareRoot_of_presentation
    (target : Matrix4) (hPresentation : HasPositiveRealJordanPresentation target) :
    HasSylvesterRegularRealSquareRoot target := by
  let presented : PositiveRealJordanPresentableMatrix :=
    ⟨target, hPresentation⟩
  exact ⟨positiveRealJordanRootOfPresentable presented,
    positiveRealJordanRootOfPresentable_square presented,
    positiveRealJordanRootOfPresentable_sylvester_bijective presented⟩

/-- Complete raw-matrix closure reduced to the one missing Jordan-basis
assembly theorem.  Every analytic and blockwise algebraic obligation after
that bridge is unconditional. -/
theorem positiveRealSplitSpectrum_regularRoot_reduction
    (bridge : PositiveRealJordanBasisBridge4)
    (target : Matrix4) (hTarget : PositiveRealSplitCharpoly4 target) :
    HasSylvesterRegularRealSquareRoot target :=
  hasSylvesterRegularRealSquareRoot_of_presentation target
    (bridge target hTarget)

/-- No hidden second condition remains: the no-go is exactly the universal
presentation bridge displayed above. -/
theorem positiveRealJordanBasisBridge4_iff :
    PositiveRealJordanBasisBridge4 ↔
      ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
        HasPositiveRealJordanPresentation target :=
  Iff.rfl

end

end P0EFTJanusPositiveRealJordanPresentationBridge4D
end JanusFormal
