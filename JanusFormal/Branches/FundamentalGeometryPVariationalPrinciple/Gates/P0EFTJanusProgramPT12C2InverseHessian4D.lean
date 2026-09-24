import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverseDerivative4D

/-! # Exact second derivative of inversion in the finite C² matrix algebra -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12C2InverseHessian4D

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix (dimension : Nat) :=
  C2FiniteMatrix period hPeriod dimension

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverseDerivative4D

theorem c2Inverse_hessian (dimension : Nat)
    (matrix first second : C2Matrix period hPeriod dimension)
    (hMatrix : matrix ∈ c2FiniteMatrixUnitSet period hPeriod dimension) :
    let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) dimension
    let inverse := c2FiniteMatrixInverse period hPeriod dimension matrix
    fderiv Real (fderiv Real (c2FiniteMatrixInverse period hPeriod dimension))
        matrix first second =
      product inverse (product second (product inverse (product first inverse))) +
      product (product inverse (product first inverse)) (product second inverse) := by
  let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) dimension
  let inverse := c2FiniteMatrixInverse period hPeriod dimension
  have hInv := c2FiniteMatrixInverse_hasFDerivAt period hPeriod dimension matrix hMatrix
  have hLeft := product.hasFDerivAt.comp matrix hInv
  have hRight := product.flip.hasFDerivAt.comp matrix hInv
  have hDerivative := (hLeft.clm_comp hRight).neg
  have hNear : fderiv Real inverse =ᶠ[nhds matrix]
      c2FiniteMatrixInverseDerivative period hPeriod dimension := by
    filter_upwards [(c2FiniteMatrixUnitSet_isOpen period hPeriod dimension).mem_nhds hMatrix]
      with current hCurrent
    exact (c2FiniteMatrixInverse_hasFDerivAt period hPeriod dimension current hCurrent).fderiv
  rw [hNear.fderiv_eq]
  change fderiv Real (fun current => -((product (inverse current)).comp
    (product.flip (inverse current)))) matrix first second = _
  simp only [Function.comp_def, Pi.neg_def] at hDerivative
  rw [hDerivative.fderiv]
  simp [product,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    c2FiniteMatrixInverseDerivative]
  exact add_comm _ _

theorem c2Inverse_hessian_identity (dimension : Nat)
    (first second : C2Matrix period hPeriod dimension) :
    let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) dimension
    fderiv Real (fderiv Real (c2FiniteMatrixInverse period hPeriod dimension))
        (c2FiniteMatrixIdentity period hPeriod dimension) first second =
      product second first + product first second := by
  have hInverse : c2FiniteMatrixInverse period hPeriod dimension
      (c2FiniteMatrixIdentity period hPeriod dimension) =
      c2FiniteMatrixIdentity period hPeriod dimension := by
    have h := c2FiniteMatrixProduct_inverse_right period hPeriod dimension
      (c2FiniteMatrixIdentity period hPeriod dimension)
      (c2FiniteMatrixIdentity_mem_unitSet period hPeriod dimension)
    simpa only [c2FiniteMatrixProduct_identity_left] using h
  simpa only [hInverse, c2FiniteMatrixProduct_identity_left,
    c2FiniteMatrixProduct_identity_right] using
    c2Inverse_hessian period hPeriod dimension
      (c2FiniteMatrixIdentity period hPeriod dimension) first second
      (c2FiniteMatrixIdentity_mem_unitSet period hPeriod dimension)

end
end P0EFTJanusProgramPT12C2InverseHessian4D
end JanusFormal
