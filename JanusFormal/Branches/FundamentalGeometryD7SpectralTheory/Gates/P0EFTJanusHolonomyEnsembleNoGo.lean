import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusHolonomyDeterminantNoGo

namespace JanusFormal
namespace P0EFTJanusHolonomyEnsembleNoGo

set_option autoImplicit false

open P0EFTJanusHolonomyDeterminantNoGo

/--
One positive-weight determinant sector after local subtraction.  `radial` is
`exp(-x)>0`, while `cosPhase` is the cosine of the circle holonomy angle.
The positive determinant factor is stored explicitly so the sign theorem is
independent of a particular trigonometric parametrization.
-/
structure HolonomySector where
  weight : ℝ
  radial : ℝ
  cosPhase : ℝ
  weightPositive : 0 < weight
  radialPositive : 0 < radial
  determinantFactorPositive :
    0 < holonomyDeterminantFactor cosPhase radial

/-- Logarithmic modulus derivative of one sector. -/
noncomputable def sectorLogDerivative
    (sector : HolonomySector) : ℝ :=
  sector.weight *
    (holonomyDerivativeNumerator sector.cosPhase sector.radial /
      holonomyDeterminantFactor sector.cosPhase sector.radial)

/-- Every sector with nonpositive holonomy cosine has strictly negative slope. -/
theorem sector_derivative_negative_of_cosine_nonpositive
    (sector : HolonomySector)
    (hCosine : sector.cosPhase ≤ 0) :
    sectorLogDerivative sector < 0 := by
  have hDifference : sector.cosPhase - sector.radial < 0 := by
    linarith [sector.radialPositive]
  have hNumerator :
      holonomyDerivativeNumerator
        sector.cosPhase sector.radial < 0 := by
    unfold holonomyDerivativeNumerator
    exact mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) sector.radialPositive)
      hDifference
  unfold sectorLogDerivative
  exact mul_neg_of_pos_of_neg sector.weightPositive
    (div_neg_of_neg_of_pos hNumerator
      sector.determinantFactorPositive)

/-- Finite determinant-ensemble derivative. -/
noncomputable def ensembleLogDerivative :
    List HolonomySector → ℝ
  | [] => 0
  | sector :: rest =>
      sectorLogDerivative sector + ensembleLogDerivative rest

/-- If every holonomy cosine is nonpositive, the finite ensemble slope is nonpositive. -/
theorem ensemble_derivative_nonpositive_of_all_cosines_nonpositive
    (sectors : List HolonomySector)
    (hCosines : ∀ sector ∈ sectors, sector.cosPhase ≤ 0) :
    ensembleLogDerivative sectors ≤ 0 := by
  induction sectors with
  | nil => simp [ensembleLogDerivative]
  | cons head tail ih =>
      have hHead : head.cosPhase ≤ 0 :=
        hCosines head (by simp)
      have hTail : ∀ sector ∈ tail, sector.cosPhase ≤ 0 := by
        intro sector hMembership
        exact hCosines sector (by simp [hMembership])
      have hHeadDerivative :=
        sector_derivative_negative_of_cosine_nonpositive head hHead
      have hTailDerivative := ih hTail
      simp [ensembleLogDerivative]
      linarith

/-- A nonempty all-nonpositive-cosine ensemble is strictly monotone. -/
theorem nonempty_ensemble_derivative_negative_of_all_cosines_nonpositive
    (head : HolonomySector)
    (tail : List HolonomySector)
    (hCosines : ∀ sector ∈ head :: tail, sector.cosPhase ≤ 0) :
    ensembleLogDerivative (head :: tail) < 0 := by
  have hHead : head.cosPhase ≤ 0 :=
    hCosines head (by simp)
  have hTail : ∀ sector ∈ tail, sector.cosPhase ≤ 0 := by
    intro sector hMembership
    exact hCosines sector (by simp [hMembership])
  have hHeadDerivative :=
    sector_derivative_negative_of_cosine_nonpositive head hHead
  have hTailDerivative :=
    ensemble_derivative_nonpositive_of_all_cosines_nonpositive tail hTail
  simp [ensembleLogDerivative]
  linarith

/--
A stationary nonempty positive-weight determinant ensemble must contain at least
one sector with strictly positive holonomy cosine.
-/
theorem stationary_nonempty_ensemble_requires_positive_cosine
    (head : HolonomySector)
    (tail : List HolonomySector)
    (hStationary : ensembleLogDerivative (head :: tail) = 0) :
    ∃ sector ∈ head :: tail, 0 < sector.cosPhase := by
  by_contra hNoPositive
  have hAllNonpositive :
      ∀ sector ∈ head :: tail, sector.cosPhase ≤ 0 := by
    intro sector hMembership
    apply le_of_not_gt
    intro hPositive
    exact hNoPositive ⟨sector, hMembership, hPositive⟩
  have hNegative :=
    nonempty_ensemble_derivative_negative_of_all_cosines_nonpositive
      head tail hAllNonpositive
  linarith

/--
Consequently, exact-quarter (`cos=0`) and antiperiodic (`cos=-1`) sectors,
even in arbitrary positive multiplicities, cannot stabilize a finite circle by
their determinant magnitudes alone.  At least one periodic or interior
positive-cosine holonomy sector, or a non-determinant interaction/local term,
is mathematically necessary.
-/
structure HolonomyEnsemblePhysicalStatus where
  determinantSectorsDerived : Prop
  allWeightsAndStatisticsComputed : Prop
  positiveDeterminantFactorsProved : Prop
  positiveCosineSectorDerived : Prop
  fullRenormalizedDerivativeComputed : Prop
  stationaryModulusDerived : Prop
  stabilityProved : Prop
  finiteCountertermsFixedMicroscopically : Prop


def holonomyEnsemblePhysicalClosure
    (s : HolonomyEnsemblePhysicalStatus) : Prop :=
  s.determinantSectorsDerived /\
  s.allWeightsAndStatisticsComputed /\
  s.positiveDeterminantFactorsProved /\
  s.positiveCosineSectorDerived /\
  s.fullRenormalizedDerivativeComputed /\
  s.stationaryModulusDerived /\
  s.stabilityProved /\
  s.finiteCountertermsFixedMicroscopically

end P0EFTJanusHolonomyEnsembleNoGo
end JanusFormal
