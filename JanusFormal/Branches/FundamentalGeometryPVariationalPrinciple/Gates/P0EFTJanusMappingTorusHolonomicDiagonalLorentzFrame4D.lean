import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusHolonomicDiagonalMusical4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzTensor4D

/-!
# Lorentz frame of the holonomic diagonal model metric

Positive diagonal magnitudes define an explicit continuous Lorentz frame in
the exact time-first model coordinates.  This is a pointwise model-space
certificate, not a global smooth tangent frame on the quotient.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusHolonomicDiagonalLorentzFrame4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusMappingTorusHolonomicDiagonalSharp4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D

/-- Positive square-root scaling of all four holonomic coefficients. -/
def holonomicSqrtScale
    (magnitude : HolonomicCoefficients)
    (hPositive : ∀ index, 0 < magnitude index) :
    HolonomicCoefficients ≃L[Real] HolonomicCoefficients :=
  ContinuousLinearEquiv.piCongrRight (fun index =>
    ContinuousLinearEquiv.smulLeft
      (Units.mk0 (Real.sqrt (magnitude index))
        (Real.sqrt_ne_zero'.2 (hPositive index))))

/-- Model Lorentz frame obtained by square-root scaling in the exact
holonomic coordinate equivalence. -/
def holonomicDiagonalLorentzFrame
    (magnitude : HolonomicCoefficients)
    (hPositive : ∀ index, 0 < magnitude index) :
    CoverCoordinates ≃L[Real] CoverCoordinates :=
  holonomicCoordinateEquiv.trans
    ((holonomicSqrtScale magnitude hPositive).trans
      holonomicCoordinateEquiv.symm)

@[simp]
theorem holonomicDiagonalLorentzFrame_coefficient
    (magnitude : HolonomicCoefficients)
    (hPositive : ∀ index, 0 < magnitude index)
    (vector : CoverCoordinates) (index : Fin 4) :
    holonomicVectorCoefficient
        (holonomicDiagonalLorentzFrame magnitude hPositive vector) index =
      Real.sqrt (magnitude index) *
        holonomicVectorCoefficient vector index := by
  change holonomicCoordinateEquiv
      (holonomicDiagonalLorentzFrame magnitude hPositive vector) index = _
  simp [holonomicDiagonalLorentzFrame, holonomicSqrtScale]
  change holonomicCoefficientLinearMap
    (∑ basisIndex : Fin 4,
      (Real.sqrt (magnitude basisIndex) *
        holonomicVectorCoefficient vector basisIndex) •
        tangentCoordinate basisIndex) index = _
  rw [map_sum]
  simp [holonomicVectorCoefficient_tangentCoordinate]

private theorem modelMinkowskiPair_eq_signature_sum
    (first second : CoverCoordinates) :
    modelMinkowskiPair first second =
      ∑ index : Fin 4,
        signature index * holonomicVectorCoefficient first index *
          holonomicVectorCoefficient second index := by
  rw [Fin.sum_univ_succ]
  simp [modelMinkowskiPair, signature, holonomicVectorCoefficient,
    PiLp.inner_apply]
  rw [show
    (∑ index : Fin 3, second.1.ofLp index * first.1.ofLp index) =
      ∑ index : Fin 3, first.1.ofLp index * second.1.ofLp index by
    apply Finset.sum_congr rfl
    intro index _
    ring]
  ring

/-- The positive diagonal pairing has Lorentz inertia `(3,1)` in the
explicit square-root-scaled holonomic frame. -/
theorem holonomicDiagonalPair_eq_modelMinkowskiPair
    (magnitude : HolonomicCoefficients)
    (hPositive : ∀ index, 0 < magnitude index)
    (first second : CoverCoordinates) :
    holonomicDiagonalPair magnitude first second =
      modelMinkowskiPair
        (holonomicDiagonalLorentzFrame magnitude hPositive first)
        (holonomicDiagonalLorentzFrame magnitude hPositive second) := by
  rw [modelMinkowskiPair_eq_signature_sum]
  unfold holonomicDiagonalPair
  simp_rw [holonomicDiagonalLorentzFrame_coefficient]
  apply Finset.sum_congr rfl
  intro index _
  have hSqrt :
      Real.sqrt (magnitude index) * Real.sqrt (magnitude index) =
        magnitude index :=
    Real.mul_self_sqrt (le_of_lt (hPositive index))
  conv_lhs => rw [← hSqrt]
  ring

end

end P0EFTJanusMappingTorusHolonomicDiagonalLorentzFrame4D
end JanusFormal
