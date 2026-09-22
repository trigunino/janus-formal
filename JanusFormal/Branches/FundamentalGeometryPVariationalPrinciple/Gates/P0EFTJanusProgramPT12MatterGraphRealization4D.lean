import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterGraphRieszEigen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterGraphModeRieszRatio4D

/-! The concrete Riesz representative of the isolated signed SpinC graph Hessian. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MatterGraphRealization4D

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPT12MatterGraphModeRieszRatio4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)

local instance matterRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

local instance matterL2GraphInnerProductSpace :
    InnerProductSpace Real
      (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared) :=
  Submodule.innerProductSpace
    (programPPrimitiveSpinCMatterL2GraphSubmodule period hPeriod massSquared)

local instance matterL2GraphCompleteSpace :
    CompleteSpace
      (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared) :=
  l2MatterGraphCompleteSpace period hPeriod massSquared

open P0EFTJanusProgramPT12MatterGraphRieszEigen4D
open P0EFTJanusProgramPT12ProductSelfAdjoint4D

theorem matterL2GraphRiesz_symmetric
    (x y : ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared) :
    inner Real (matterL2GraphRiesz period hPeriod massSquared x) y =
      inner Real x (matterL2GraphRiesz period hPeriod massSquared y) := by
  rw [matterL2GraphRiesz_pairing, ← real_inner_comm x, matterL2GraphRiesz_pairing]
  exact programPPrimitiveSpinCMatterGraphForm_comm period hPeriod massSquared _ _

theorem matterL2GraphRiesz_toPMap_selfAdjoint :
    IsSelfAdjoint ((matterL2GraphRiesz period hPeriod massSquared).toPMap ⊤) :=
  bounded_toPMap_selfAdjoint _ (matterL2GraphRiesz_symmetric period hPeriod massSquared)

def matterFiniteGraphEmbedding : ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
    ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared :=
  (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared).symm.toLinearMap.comp
    (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod massSquared)

theorem matterFiniteGraphEmbedding_denseRange :
    DenseRange (matterFiniteGraphEmbedding period hPeriod massSquared) := by
  have h := ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared).symm.surjective.denseRange).comp
    (programPPrimitiveSpinCMatterGraphFiniteLinearMap_denseRange period hPeriod massSquared)
    (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared).symm.continuous
  simpa [matterFiniteGraphEmbedding, programPPrimitiveSpinCMatterGraphFiniteRealLinearMap,
    Function.comp_def] using h

theorem matterFiniteGraphEmbedding_pairing
    (x y : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    matterL2GraphForm period hPeriod massSquared
      (matterFiniteGraphEmbedding period hPeriod massSquared x)
      (matterFiniteGraphEmbedding period hPeriod massSquared y) =
    programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
      (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod massSquared x)
      (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod massSquared y) := by
  simp [matterL2GraphForm, matterFiniteGraphEmbedding]

end
end P0EFTJanusProgramPT12MatterGraphRealization4D
end JanusFormal
