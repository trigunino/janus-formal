import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterGraphModeRieszRatio4D

/-! The concrete Riesz representative of the isolated signed SpinC graph Hessian. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MatterGraphRieszEigen4D

set_option autoImplicit false
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

/-- The same-action matter form transported to its genuine `L²` graph Hilbert space. -/
def matterL2GraphForm :
    ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared →L[Real]
      ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared →L[Real]
        Real :=
  (programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared).bilinearComp
    (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared).toContinuousLinearMap
    (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared).toContinuousLinearMap

/-- Concrete bounded Riesz representative of the isolated matter Hessian. -/
def matterL2GraphRiesz :
    ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared →L[Real]
      ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared :=
  InnerProductSpace.continuousLinearMapOfBilin
    (matterL2GraphForm period hPeriod massSquared)

theorem matterL2GraphRiesz_pairing
    (first second : ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod
      massSquared) :
    inner Real (matterL2GraphRiesz period hPeriod massSquared first) second =
      matterL2GraphForm period hPeriod massSquared first second := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply
    (matterL2GraphForm period hPeriod massSquared) first second

/-- A signed spectral singleton is an eigenvector of the concrete graph Riesz map. -/
theorem matterL2GraphRiesz_single_eigen
    (sector : Sector) (mode : PrimitiveSpinCGeometricSignedMode) :
    let w := programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared (sector, mode)
    let x := (programPPrimitiveSpinCMatterL2GraphEquiv
      period hPeriod massSquared).symm
        (programPPrimitiveSpinCMatterGraphSingle
          period hPeriod massSquared sector mode 1)
    matterL2GraphRiesz period hPeriod massSquared x =
      (w / (1 + w ^ 2)) • x := by
  dsimp only
  apply ext_inner_right Real
  intro state
  calc
    inner Real
        (matterL2GraphRiesz period hPeriod massSquared
          ((programPPrimitiveSpinCMatterL2GraphEquiv
            period hPeriod massSquared).symm
            (programPPrimitiveSpinCMatterGraphSingle
              period hPeriod massSquared sector mode 1))) state =
      matterL2GraphForm period hPeriod massSquared
        ((programPPrimitiveSpinCMatterL2GraphEquiv
          period hPeriod massSquared).symm
          (programPPrimitiveSpinCMatterGraphSingle
            period hPeriod massSquared sector mode 1)) state :=
        matterL2GraphRiesz_pairing period hPeriod massSquared _ _
    _ = (programPPrimitiveSpinCMatterHessianWeight
          period hPeriod massSquared (sector, mode) /
          (1 + (programPPrimitiveSpinCMatterHessianWeight
            period hPeriod massSquared (sector, mode)) ^ 2)) *
        inner Real
          ((programPPrimitiveSpinCMatterL2GraphEquiv
            period hPeriod massSquared).symm
            (programPPrimitiveSpinCMatterGraphSingle
              period hPeriod massSquared sector mode 1)) state := by
        exact matterL2GraphHessian_single_mode_ratio
          period hPeriod massSquared sector mode state
    _ = _ := by
      exact (real_inner_smul_left
        ((programPPrimitiveSpinCMatterL2GraphEquiv
          period hPeriod massSquared).symm
          (programPPrimitiveSpinCMatterGraphSingle
            period hPeriod massSquared sector mode 1))
        state
        (programPPrimitiveSpinCMatterHessianWeight
          period hPeriod massSquared (sector, mode) /
          (1 + (programPPrimitiveSpinCMatterHessianWeight
            period hPeriod massSquared (sector, mode)) ^ 2))).symm

end
end P0EFTJanusProgramPT12MatterGraphRieszEigen4D
end JanusFormal
