import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatFiniteSectorFamilyNuclearTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatNuclearTraceDerivative

/-!
# Positive-time regularity of a heterogeneous finite-sector nuclear trace

The total trace of the genuine finite block family is continuous on every
positive half-line and differentiable at every positive time.  Its derivative
is the finite sum of the component spectral derivatives, is nonpositive and
continuous away from zero.  Simultaneous PT preserves both trace and
derivative.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatFiniteSectorFamilyTraceRegularity4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleHeatNuclearTraceClass
open P0EFTJanusCircleHeatNuclearTraceContinuity
open P0EFTJanusCircleHeatNuclearTraceDerivative
open P0EFTJanusCircleHeatFiniteSectorFamilyNuclearTrace4D

variable {Internal : Type} [Fintype Internal]

/-- Real-time total nuclear trace of the heterogeneous finite family. -/
def circleFiniteSectorFamilyNuclearTraceReal
    (time : Real) (sector : Internal → CircleFiniteSector) : Real :=
  ∑ component : Internal,
    circleHeatNuclearTraceReal time (sector component).fold
      (sector component).twist

theorem circleFiniteSectorFamilyNuclearTraceReal_of_heatTime
    (time : HeatTime) (sector : Internal → CircleFiniteSector) :
    circleFiniteSectorFamilyNuclearTraceReal time sector =
      circleFiniteSectorFamilyNuclearTrace time sector := by
  unfold circleFiniteSectorFamilyNuclearTraceReal
    circleFiniteSectorFamilyNuclearTrace
  apply Finset.sum_congr rfl
  intro component _
  exact circleHeatNuclearTraceReal_of_heatTime time
    (sector component).fold (sector component).twist

theorem circleFiniteSectorFamilyNuclearTraceReal_continuousOn_Ici
    (epsilon : HeatTime) (sector : Internal → CircleFiniteSector) :
    ContinuousOn (fun time : Real =>
      circleFiniteSectorFamilyNuclearTraceReal time sector) (Ici epsilon.1) := by
  unfold circleFiniteSectorFamilyNuclearTraceReal
  apply continuousOn_finsetSum Finset.univ
  intro component _
  exact circleHeatNuclearTraceReal_continuousOn_Ici epsilon
    (sector component).fold (sector component).twist

/-- Finite sum of the component spectral trace derivatives. -/
def circleFiniteSectorFamilyNuclearTraceRealDerivative
    (time : Real) (sector : Internal → CircleFiniteSector) : Real :=
  ∑ component : Internal,
    circleHeatNuclearTraceRealDerivative time (sector component).fold
      (sector component).twist

theorem circleFiniteSectorFamilyNuclearTraceRealDerivative_continuousOn_Ici
    (epsilon : HeatTime) (sector : Internal → CircleFiniteSector) :
    ContinuousOn (fun time : Real =>
      circleFiniteSectorFamilyNuclearTraceRealDerivative time sector)
      (Ici epsilon.1) := by
  unfold circleFiniteSectorFamilyNuclearTraceRealDerivative
  apply continuousOn_finsetSum Finset.univ
  intro component _
  exact circleHeatNuclearTraceRealDerivative_continuousOn_Ici epsilon
    (sector component).fold (sector component).twist

theorem circleFiniteSectorFamilyNuclearTraceReal_hasDerivAt
    (time : HeatTime) (sector : Internal → CircleFiniteSector) :
    HasDerivAt
      (fun s : Real => circleFiniteSectorFamilyNuclearTraceReal s sector)
      (circleFiniteSectorFamilyNuclearTraceRealDerivative time.1 sector)
      time.1 := by
  unfold circleFiniteSectorFamilyNuclearTraceReal
    circleFiniteSectorFamilyNuclearTraceRealDerivative
  exact HasDerivAt.fun_sum fun component _ =>
    circleHeatNuclearTraceReal_hasDerivAt time (sector component).fold
      (sector component).twist

theorem circleFiniteSectorFamilyNuclearTraceReal_deriv_eq
    (time : HeatTime) (sector : Internal → CircleFiniteSector) :
    deriv (fun s : Real => circleFiniteSectorFamilyNuclearTraceReal s sector)
        time.1 =
      circleFiniteSectorFamilyNuclearTraceRealDerivative time.1 sector :=
  (circleFiniteSectorFamilyNuclearTraceReal_hasDerivAt time sector).deriv

theorem circleFiniteSectorFamilyNuclearTraceRealDerivative_nonpositive
    (time : HeatTime) (sector : Internal → CircleFiniteSector) :
    circleFiniteSectorFamilyNuclearTraceRealDerivative time.1 sector ≤ 0 := by
  unfold circleFiniteSectorFamilyNuclearTraceRealDerivative
  apply Finset.sum_nonpos
  intro component _
  exact circleHeatNuclearTraceRealDerivative_nonpositive time
    (sector component).fold (sector component).twist

theorem circleFiniteSectorFamilyNuclearTraceReal_deriv_nonpositive
    (time : HeatTime) (sector : Internal → CircleFiniteSector) :
    deriv (fun s : Real => circleFiniteSectorFamilyNuclearTraceReal s sector)
        time.1 ≤ 0 := by
  rw [circleFiniteSectorFamilyNuclearTraceReal_deriv_eq time sector]
  exact circleFiniteSectorFamilyNuclearTraceRealDerivative_nonpositive time sector

theorem circleFiniteSectorFamilyNuclearTraceReal_deriv_continuousOn_Ici
    (epsilon : HeatTime) (sector : Internal → CircleFiniteSector) :
    ContinuousOn (fun time : Real =>
      deriv (fun s : Real =>
        circleFiniteSectorFamilyNuclearTraceReal s sector) time)
      (Ici epsilon.1) := by
  apply (circleFiniteSectorFamilyNuclearTraceRealDerivative_continuousOn_Ici
    epsilon sector).congr
  intro time hTime
  exact circleFiniteSectorFamilyNuclearTraceReal_deriv_eq
    ⟨time, epsilon.2.trans_le hTime⟩ sector

theorem circleHeatNuclearTraceReal_ptFlip
    (time : Real) (fold : Fold) (twist : CircleTwist) :
    circleHeatNuclearTraceReal time (foldPTFlip fold) twist =
      circleHeatNuclearTraceReal time fold twist := by
  cases fold
  · exact circleHeatNuclearTraceReal_pt_eq_positive time twist
  · exact (circleHeatNuclearTraceReal_pt_eq_positive time twist).symm

theorem circleHeatNuclearTraceRealDerivative_ptFlip
    (time : Real) (fold : Fold) (twist : CircleTwist) :
    circleHeatNuclearTraceRealDerivative time (foldPTFlip fold) twist =
      circleHeatNuclearTraceRealDerivative time fold twist := by
  cases fold
  · exact circleHeatNuclearTraceRealDerivative_pt_eq_positive time twist
  · exact (circleHeatNuclearTraceRealDerivative_pt_eq_positive time twist).symm

theorem circleFiniteSectorFamilyNuclearTraceReal_pt_eq
    (time : Real) (sector : Internal → CircleFiniteSector) :
    circleFiniteSectorFamilyNuclearTraceReal time (fun i => (sector i).pt) =
      circleFiniteSectorFamilyNuclearTraceReal time sector := by
  unfold circleFiniteSectorFamilyNuclearTraceReal CircleFiniteSector.pt
  apply Finset.sum_congr rfl
  intro component _
  exact circleHeatNuclearTraceReal_ptFlip time (sector component).fold
    (sector component).twist

theorem circleFiniteSectorFamilyNuclearTraceRealDerivative_pt_eq
    (time : Real) (sector : Internal → CircleFiniteSector) :
    circleFiniteSectorFamilyNuclearTraceRealDerivative time
        (fun i => (sector i).pt) =
      circleFiniteSectorFamilyNuclearTraceRealDerivative time sector := by
  unfold circleFiniteSectorFamilyNuclearTraceRealDerivative CircleFiniteSector.pt
  apply Finset.sum_congr rfl
  intro component _
  exact circleHeatNuclearTraceRealDerivative_ptFlip time
    (sector component).fold (sector component).twist

end

end P0EFTJanusCircleHeatFiniteSectorFamilyTraceRegularity4D
end JanusFormal
