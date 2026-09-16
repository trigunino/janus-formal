import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D

/-!
# Exact modal Riesz coefficient of the primitive SpinC graph Hessian

On a signed matter mode of Hessian weight `w`, the graph inner product has
weight `1 + w²`.  The same-action Hessian therefore has modal Riesz
coefficient `w / (1 + w²)`.  This is a statement about the isolated matter
graph form, not the full augmented Candidate-A operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MatterGraphModeRieszRatio4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalGraphFredholm4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D

variable (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)

local instance matterRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

local instance matterModeDecidableEq :
    DecidableEq ProgramPPrimitiveSpinCMatterMode := Classical.decEq _

/-- The `L²` graph inner product, written in the two ambient coordinates. -/
def matterGraphInner
    (first second : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared) : Real :=
  inner Real first.1.1 second.1.1 + inner Real first.1.2 second.1.2

local instance matterL2GraphInnerProductSpace :
    InnerProductSpace Real
      (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared) :=
  Submodule.innerProductSpace
    (programPPrimitiveSpinCMatterL2GraphSubmodule
      period hPeriod massSquared)

/-- The coordinate formula is precisely the inherited inner product of the
genuine `L²` matter graph Hilbert space. -/
theorem matterGraphInner_eq_l2GraphInner
    (first second : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared) :
    matterGraphInner period hPeriod massSquared first second =
      inner Real
        ((programPPrimitiveSpinCMatterL2GraphEquiv
          period hPeriod massSquared).symm first)
        ((programPPrimitiveSpinCMatterL2GraphEquiv
          period hPeriod massSquared).symm second) := by
  rfl

/-- Exact Riesz eigenrelation on a single signed SpinC mode. -/
theorem matterGraphHessian_single_mode_ratio
    (sector : Sector) (mode : PrimitiveSpinCGeometricSignedMode)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared) :
    let w := programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared (sector, mode)
    programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
        (programPPrimitiveSpinCMatterGraphSingle
          period hPeriod massSquared sector mode 1) state =
      (w / (1 + w ^ 2)) *
        matterGraphInner period hPeriod massSquared
          (programPPrimitiveSpinCMatterGraphSingle
            period hPeriod massSquared sector mode 1) state := by
  dsimp only
  let w := programPPrimitiveSpinCMatterHessianWeight
    period hPeriod massSquared (sector, mode)
  let x := programPPrimitiveSpinCMatterGraphSingle
    period hPeriod massSquared sector mode 1
  have hFst : x.1.1 = lp.single 2 (sector, mode) (1 : Complex) := by
    dsimp [x, programPPrimitiveSpinCMatterGraphSingle]
  have hSnd : x.1.2 = lp.single 2 (sector, mode) (w : Complex) := by
    dsimp [x, programPPrimitiveSpinCMatterGraphSingle]
    simp [w]
  have hRelation := complexDiagonalGraphDomain_relation
    ProgramPPrimitiveSpinCMatterMode
    (programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared) state (sector, mode)
  change state.1.2 (sector, mode) = (w : Complex) * state.1.1 (sector, mode)
    at hRelation
  rw [programPPrimitiveSpinCMatterGraphForm_apply]
  unfold matterGraphInner
  rw [hFst, hSnd]
  repeat rw [real_inner_eq_re_inner]
  repeat rw [lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one] at *
  rw [hRelation]
  simp
  have hden : 1 + w ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The same modal eigenrelation against the actual inherited Hilbert inner
product of the `L²` graph domain. -/
theorem matterL2GraphHessian_single_mode_ratio
    (sector : Sector) (mode : PrimitiveSpinCGeometricSignedMode)
    (state : ProgramPPrimitiveSpinCMatterL2GraphDomain
      period hPeriod massSquared) :
    let w := programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared (sector, mode)
    programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
        (programPPrimitiveSpinCMatterGraphSingle
          period hPeriod massSquared sector mode 1)
        (programPPrimitiveSpinCMatterL2GraphEquiv
          period hPeriod massSquared state) =
      (w / (1 + w ^ 2)) *
        inner Real
          ((programPPrimitiveSpinCMatterL2GraphEquiv
            period hPeriod massSquared).symm
            (programPPrimitiveSpinCMatterGraphSingle
              period hPeriod massSquared sector mode 1)) state := by
  have h := matterGraphHessian_single_mode_ratio period hPeriod massSquared
    sector mode
    (programPPrimitiveSpinCMatterL2GraphEquiv
      period hPeriod massSquared state)
  rw [matterGraphInner_eq_l2GraphInner] at h
  simpa using h

end
end P0EFTJanusProgramPT12MatterGraphModeRieszRatio4D
end JanusFormal
