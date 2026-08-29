import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D

/-!
# Canonical six-block chart Hessian

After H10 removes the Robin/GHY block from the independent analytic input, the
remaining physical Hessian is the sum of exactly six genuine action blocks:
Candidate-A interaction, the two Einstein--Hilbert terms, the two Maxwell
terms and finite/null-BV.

This file does not accept six bilinear forms as data. It differentiates the six
scalar fields already present in `FullCoupledActionBlocks`, proves the second
Frechet derivative of their sum is the sum of their six canonical Hessians,
and proves that the seven-block physical Hessian is this canonical six-block
sum plus the Robin Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCanonicalSixPhysicalChartHessian4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Filter Topology
open scoped Topology
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D

universe u

/-- The six physical blocks not supplied by matter, LL or the H10 Robin
closure. -/
inductive CanonicalSixPhysicalBlock
  | candidateA
  | einsteinHilbertPlus
  | einsteinHilbertMinus
  | maxwellPlus
  | maxwellMinus
  | finiteBV
  deriving DecidableEq, Fintype

/-- Scalar action selected by one of the six canonical physical labels. -/
def canonicalSixPhysicalBlockAction
    {Model : Type u}
    (blocks : FullCoupledActionBlocks Model) :
    CanonicalSixPhysicalBlock → Model → Real
  | .candidateA => blocks.candidateA
  | .einsteinHilbertPlus => blocks.einsteinHilbertPlus
  | .einsteinHilbertMinus => blocks.einsteinHilbertMinus
  | .maxwellPlus => blocks.maxwellPlus
  | .maxwellMinus => blocks.maxwellMinus
  | .finiteBV => blocks.finiteBV

/-- Right-associated sum of the six actual scalar action blocks. -/
def canonicalSixPhysicalAction
    {Model : Type u}
    (blocks : FullCoupledActionBlocks Model) (point : Model) : Real :=
  blocks.candidateA point +
    (blocks.einsteinHilbertPlus point +
      (blocks.einsteinHilbertMinus point +
        (blocks.maxwellPlus point +
          (blocks.maxwellMinus point + blocks.finiteBV point))))

/-- The seven-block physical action is exactly the six-block action plus the
Robin action. -/
theorem fullCoupledPhysicalAction_eq_six_add_robin
    {Model : Type u}
    (blocks : FullCoupledActionBlocks Model) :
    fullCoupledPhysicalAction blocks = fun point =>
      canonicalSixPhysicalAction blocks point + blocks.robin point := by
  funext point
  unfold fullCoupledPhysicalAction canonicalSixPhysicalAction
  ring

/-- Genuine second Frechet derivative of one selected scalar block. -/
def canonicalSixPhysicalBlockHessian
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model)
    (block : CanonicalSixPhysicalBlock)
    (point : Model) :
    Model →L[Real] Model →L[Real] Real :=
  fderiv Real
    (actionGradient (canonicalSixPhysicalBlockAction blocks block)) point

/-- Genuine second Frechet derivative of the six-block scalar sum. -/
def canonicalSixPhysicalHessian
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model)
    (point : Model) :
    Model →L[Real] Model →L[Real] Real :=
  fderiv Real (actionGradient (canonicalSixPhysicalAction blocks)) point

/-- Explicit sum of the six canonical block Hessians. -/
def canonicalSixPhysicalHessianSum
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model)
    (point : Model) :
    Model →L[Real] Model →L[Real] Real :=
  canonicalSixPhysicalBlockHessian blocks .candidateA point +
    (canonicalSixPhysicalBlockHessian blocks .einsteinHilbertPlus point +
      (canonicalSixPhysicalBlockHessian blocks .einsteinHilbertMinus point +
        (canonicalSixPhysicalBlockHessian blocks .maxwellPlus point +
          (canonicalSixPhysicalBlockHessian blocks .maxwellMinus point +
            canonicalSixPhysicalBlockHessian blocks .finiteBV point))))

/-- Generic second-Frechet additivity helper. -/
theorem secondFrechet_add
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    {first second : Model → Real}
    {point : Model}
    (hFirst : ContDiffAt Real 2 first point)
    (hSecond : ContDiffAt Real 2 second point) :
    fderiv Real (actionGradient (fun state => first state + second state)) point =
      fderiv Real (actionGradient first) point +
        fderiv Real (actionGradient second) point := by
  have hGradient :
      actionGradient (fun state => first state + second state) =ᶠ[𝓝 point]
        fun state => actionGradient first state + actionGradient second state := by
    change
      fderiv Real (fun state => first state + second state) =ᶠ[𝓝 point]
        fun state => fderiv Real first state + fderiv Real second state
    filter_upwards [hFirst.eventually (by norm_num),
      hSecond.eventually (by norm_num)] with state hFirstState hSecondState
    exact fderiv_add
      (hFirstState.differentiableAt (by norm_num))
      (hSecondState.differentiableAt (by norm_num))
  have hFirstGradient : DifferentiableAt Real (actionGradient first) point :=
    (hFirst.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hSecondGradient : DifferentiableAt Real (actionGradient second) point :=
    (hSecond.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [hGradient.fderiv_eq]
  exact fderiv_add hFirstGradient hSecondGradient

/-- `C2` regularity of the six-block scalar sum. -/
theorem canonicalSixPhysicalAction_contDiffAt
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model)
    (point : Model)
    (hC2 : FullCoupledC2At blocks point) :
    ContDiffAt Real 2 (canonicalSixPhysicalAction blocks) point := by
  exact hC2.candidateA.add
    (hC2.einsteinHilbertPlus.add
      (hC2.einsteinHilbertMinus.add
        (hC2.maxwellPlus.add (hC2.maxwellMinus.add hC2.finiteBV))))

/-- The six-block Hessian is generated by the six genuine scalar summands. -/
theorem canonicalSixPhysicalHessian_eq_sum
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model)
    (point : Model)
    (hC2 : FullCoupledC2At blocks point) :
    canonicalSixPhysicalHessian blocks point =
      canonicalSixPhysicalHessianSum blocks point := by
  unfold canonicalSixPhysicalHessian canonicalSixPhysicalHessianSum
    canonicalSixPhysicalAction canonicalSixPhysicalBlockHessian
    canonicalSixPhysicalBlockAction
  rw [secondFrechet_add hC2.candidateA
      (hC2.einsteinHilbertPlus.add
        (hC2.einsteinHilbertMinus.add
          (hC2.maxwellPlus.add (hC2.maxwellMinus.add hC2.finiteBV))))]
  rw [secondFrechet_add hC2.einsteinHilbertPlus
      (hC2.einsteinHilbertMinus.add
        (hC2.maxwellPlus.add (hC2.maxwellMinus.add hC2.finiteBV)))]
  rw [secondFrechet_add hC2.einsteinHilbertMinus
      (hC2.maxwellPlus.add (hC2.maxwellMinus.add hC2.finiteBV))]
  rw [secondFrechet_add hC2.maxwellPlus
      (hC2.maxwellMinus.add hC2.finiteBV)]
  rw [secondFrechet_add hC2.maxwellMinus hC2.finiteBV]

/-- Exact decomposition of the genuine seven-block physical Hessian into the
canonical six-block sum and the Robin Hessian. -/
theorem fullCoupledPhysicalHessian_eq_six_add_robin
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model)
    (point : Model)
    (hC2 : FullCoupledC2At blocks point) :
    fderiv Real (actionGradient (fullCoupledPhysicalAction blocks)) point =
      canonicalSixPhysicalHessianSum blocks point +
        fderiv Real (actionGradient blocks.robin) point := by
  rw [fullCoupledPhysicalAction_eq_six_add_robin]
  rw [secondFrechet_add
    (canonicalSixPhysicalAction_contDiffAt blocks point hC2) hC2.robin]
  change canonicalSixPhysicalHessian blocks point + _ = _
  rw [canonicalSixPhysicalHessian_eq_sum blocks point hC2]

/-- Public checkpoint: no six physical bilinear forms are accepted as input. -/
theorem canonical_six_physical_chart_hessian_gate
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model)
    (point : Model)
    (hC2 : FullCoupledC2At blocks point) :
    canonicalSixPhysicalHessian blocks point =
        canonicalSixPhysicalHessianSum blocks point ∧
      fderiv Real (actionGradient (fullCoupledPhysicalAction blocks)) point =
        canonicalSixPhysicalHessianSum blocks point +
          fderiv Real (actionGradient blocks.robin) point :=
  ⟨canonicalSixPhysicalHessian_eq_sum blocks point hC2,
    fullCoupledPhysicalHessian_eq_six_add_robin blocks point hC2⟩

end
end P0EFTJanusProgramPCanonicalSixPhysicalChartHessian4D
end JanusFormal
