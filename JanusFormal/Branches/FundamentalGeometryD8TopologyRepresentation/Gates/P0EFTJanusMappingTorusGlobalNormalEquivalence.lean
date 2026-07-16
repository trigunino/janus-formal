import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusIsSmoothEmbedding
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalVectorBundle

/-!
# Global algebraic normal equivalence for the effective D8 throat

Mathlib currently has no normal-vector-bundle construction attached to a
`Manifold.IsSmoothEmbedding`.  In particular, the differential normal
quotients form a dependent family, but their total space has no independently
constructed bundle topology or smooth atlas.

This gate closes the strongest non-circular part of the comparison.  It
chooses the already proved fiber equivalences simultaneously, packages them as
one base-preserving equivalence of dependent total spaces, and proves exact
fiberwise linearity.  Smoothness is deliberately not claimed: it still
requires a quotient-bundle atlas whose transition functions are shown to agree
with the analytic sign-clutching transitions.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalNormalEquivalence

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusIsSmoothEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance ambientBaseChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotientChartedSpace period hPeriod

/-- The actual differential normal quotient of the smooth throat embedding at
one base point. -/
abbrev DifferentialNormalFiber (point : ThroatBase period hPeriod) :=
  HasQuotient.Quotient
    (TangentSpace coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod point))
    (LinearMap.range
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap)

/-- The range being quotiented is closed.  Consequently each differential
normal quotient carries its genuine Hausdorff normed-space topology. -/
theorem differentialNormalRange_isClosed
    (point : ThroatBase period hPeriod) :
    IsClosed
      (LinearMap.range
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap :
        Set (TangentSpace coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod point))) := by
  let targetTangent := TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)
  let targetEquiv : targetTangent ≃L[ℝ] CoverCoordinates :=
    ContinuousLinearEquiv.refl ℝ CoverCoordinates
  letI : FiniteDimensional ℝ targetTangent :=
    targetEquiv.toLinearEquiv.symm.finiteDimensional
  letI : T2Space targetTangent := by
    change T2Space CoverCoordinates
    infer_instance
  exact (LinearMap.range
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap)
    |>.closed_of_finiteDimensional

/-- The differential normal fiber has the expected real rank one. -/
theorem differentialNormalFiber_finrank
    (point : ThroatBase period hPeriod) :
    Module.finrank ℝ (DifferentialNormalFiber period hPeriod point) = 1 :=
  mfderiv_fixedThroatQuotientInclusion_normal_finrank period hPeriod point

/-- One simultaneous family of the proved pointwise linear equivalences.  The
choice is global as a dependent function; no regularity of that choice is
asserted. -/
noncomputable def differentialNormalFiberEquiv
    (point : ThroatBase period hPeriod) :
    FixedThroatNormalFiber period hPeriod point ≃ₗ[ℝ]
      DifferentialNormalFiber period hPeriod point :=
  Classical.choice
    (fixedThroatNormalFiber_equiv_differentialNormal period hPeriod point)

/-- At each fixed point the algebraic comparison is automatically a
continuous linear equivalence, since both sides are finite-dimensional real
spaces.  This is still pointwise continuity, not smooth dependence on the
base. -/
theorem differentialNormalFiber_continuousEquiv
    (point : ThroatBase period hPeriod) :
    Nonempty
      (FixedThroatNormalFiber period hPeriod point ≃L[ℝ]
        DifferentialNormalFiber period hPeriod point) := by
  let targetTangent := TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)
  let targetEquiv : targetTangent ≃L[ℝ] CoverCoordinates :=
    ContinuousLinearEquiv.refl ℝ CoverCoordinates
  letI : FiniteDimensional ℝ targetTangent :=
    targetEquiv.toLinearEquiv.symm.finiteDimensional
  letI : T2Space targetTangent := by
    change T2Space CoverCoordinates
    infer_instance
  letI : IsTopologicalAddGroup targetTangent := by
    change IsTopologicalAddGroup CoverCoordinates
    infer_instance
  letI : ContinuousSMul ℝ targetTangent := by
    change ContinuousSMul ℝ CoverCoordinates
    infer_instance
  let derivative :=
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap
  letI : IsClosed (LinearMap.range derivative : Set targetTangent) :=
    (LinearMap.range derivative).closed_of_finiteDimensional
  letI : FiniteDimensional ℝ
      (FixedThroatNormalFiber period hPeriod point) := by
    change FiniteDimensional ℝ ℝ
    infer_instance
  letI : IsTopologicalAddGroup
      (FixedThroatNormalFiber period hPeriod point) := by
    change IsTopologicalAddGroup ℝ
    infer_instance
  letI : ContinuousSMul ℝ
      (FixedThroatNormalFiber period hPeriod point) := by
    change ContinuousSMul ℝ ℝ
    infer_instance
  letI : T2Space (FixedThroatNormalFiber period hPeriod point) := by
    change T2Space ℝ
    infer_instance
  exact ⟨(differentialNormalFiberEquiv period hPeriod point)
    |>.toContinuousLinearEquiv⟩

/-- The global algebraic comparison transports the proved analytic one-loop
transition to multiplication by `-1` in the actual differential quotient.
This is the exact cocycle that an independently constructed smooth quotient
atlas must recover. -/
theorem differentialNormalFiberEquiv_oneLoop
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod))
    (normal : ℝ) :
    let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
    differentialNormalFiberEquiv period hPeriod base
        ((fixedThroatNormalVectorBundleCore period hPeriod).coordChange
          anchor ((1 : ℤ) +ᵥ anchor) base normal) =
      -differentialNormalFiberEquiv period hPeriod base normal := by
  dsimp only
  rw [one_loop_coordChange_eq_neg_id]
  exact map_neg (differentialNormalFiberEquiv period hPeriod _) normal

@[simp] theorem differentialNormalFiberEquiv_apply_symm_apply
    (point : ThroatBase period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point) :
    differentialNormalFiberEquiv period hPeriod point
        ((differentialNormalFiberEquiv period hPeriod point).symm normal) =
      normal :=
  (differentialNormalFiberEquiv period hPeriod point).apply_symm_apply normal

@[simp] theorem differentialNormalFiberEquiv_symm_apply_apply
    (point : ThroatBase period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    (differentialNormalFiberEquiv period hPeriod point).symm
        (differentialNormalFiberEquiv period hPeriod point normal) = normal :=
  (differentialNormalFiberEquiv period hPeriod point).symm_apply_apply normal

/-- The total space of the differential normal family.  This is intentionally
only a sigma type: a smooth bundle topology is the remaining frontier. -/
abbrev DifferentialNormalTotalSpace :=
  Bundle.TotalSpace ℝ (DifferentialNormalFiber period hPeriod)

/-- The analytic sign-clutched normal line and the differential normal family
are globally equivalent as dependent, fiberwise-linear families. -/
noncomputable def differentialNormalTotalEquiv :
    Bundle.TotalSpace ℝ (FixedThroatNormalFiber period hPeriod) ≃
      DifferentialNormalTotalSpace period hPeriod where
  toFun normal :=
    ⟨normal.1, differentialNormalFiberEquiv period hPeriod normal.1 normal.2⟩
  invFun normal :=
    ⟨normal.1, (differentialNormalFiberEquiv period hPeriod normal.1).symm normal.2⟩
  left_inv normal := by
    cases normal
    simp
  right_inv normal := by
    cases normal
    simp

@[simp] theorem differentialNormalTotalEquiv_base
    (normal : Bundle.TotalSpace ℝ
      (FixedThroatNormalFiber period hPeriod)) :
    (differentialNormalTotalEquiv period hPeriod normal).1 = normal.1 :=
  rfl

@[simp] theorem differentialNormalTotalEquiv_fiber
    (point : ThroatBase period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    (differentialNormalTotalEquiv period hPeriod ⟨point, normal⟩).2 =
      differentialNormalFiberEquiv period hPeriod point normal :=
  rfl

@[simp] theorem differentialNormalTotalEquiv_zero
    (point : ThroatBase period hPeriod) :
    differentialNormalTotalEquiv period hPeriod
        (⟨point, 0⟩ : Bundle.TotalSpace ℝ
          (FixedThroatNormalFiber period hPeriod)) =
      (⟨point, 0⟩ : DifferentialNormalTotalSpace period hPeriod) := by
  ext <;> simp [differentialNormalTotalEquiv]

theorem differentialNormalTotalEquiv_add
    (point : ThroatBase period hPeriod)
    (first second : FixedThroatNormalFiber period hPeriod point) :
    differentialNormalTotalEquiv period hPeriod ⟨point, first + second⟩ =
      ⟨point,
        differentialNormalFiberEquiv period hPeriod point first +
          differentialNormalFiberEquiv period hPeriod point second⟩ := by
  ext <;> simp [differentialNormalTotalEquiv]

theorem differentialNormalTotalEquiv_smul
    (point : ThroatBase period hPeriod) (scalar : ℝ)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    differentialNormalTotalEquiv period hPeriod ⟨point, scalar • normal⟩ =
      ⟨point, scalar •
        differentialNormalFiberEquiv period hPeriod point normal⟩ := by
  ext <;> simp [differentialNormalTotalEquiv]

/-- Exact non-smooth closure reached here: one global total-space equivalence,
base preservation, and linearity on every fiber. -/
theorem differentialNormalGlobalAlgebraicClosure :
    Nonempty
        (Bundle.TotalSpace ℝ (FixedThroatNormalFiber period hPeriod) ≃
          DifferentialNormalTotalSpace period hPeriod) ∧
      (∀ normal : Bundle.TotalSpace ℝ
          (FixedThroatNormalFiber period hPeriod),
        (differentialNormalTotalEquiv period hPeriod normal).1 = normal.1) ∧
      (∀ point (first second : FixedThroatNormalFiber period hPeriod point),
        differentialNormalTotalEquiv period hPeriod ⟨point, first + second⟩ =
          ⟨point,
            differentialNormalFiberEquiv period hPeriod point first +
              differentialNormalFiberEquiv period hPeriod point second⟩) ∧
      ∀ point (scalar : ℝ)
          (normal : FixedThroatNormalFiber period hPeriod point),
        differentialNormalTotalEquiv period hPeriod ⟨point, scalar • normal⟩ =
          ⟨point, scalar •
            differentialNormalFiberEquiv period hPeriod point normal⟩ := by
  exact ⟨⟨differentialNormalTotalEquiv period hPeriod⟩,
    differentialNormalTotalEquiv_base period hPeriod,
    differentialNormalTotalEquiv_add period hPeriod,
    differentialNormalTotalEquiv_smul period hPeriod⟩

end

end P0EFTJanusMappingTorusGlobalNormalEquivalence
end JanusFormal
