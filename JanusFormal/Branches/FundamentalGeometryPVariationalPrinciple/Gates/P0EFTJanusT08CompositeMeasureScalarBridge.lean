import Mathlib
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLLBraneCompositeMeasureFrechet

/-!
# T08: scalar measure coefficient versus signed composite density

Relative to a supplied nonzero coordinate-volume density rho, chi=det(J)/rho
is a scalar. Both densities must transform together. The induced variation
is derived from the actual determinant derivative. At nondegenerate jets,
every scalar tangent value is realized pointwise by a matrix variation.
This does not assert that arbitrary matrix fields are globally integrable
Jacobians, or that independent and composite field variations coincide.
-/

namespace JanusFormal
namespace P0EFTJanusT08CompositeMeasureScalarBridge

set_option autoImplicit false
noncomputable section

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

open scoped Matrix.Norms.Frobenius
open P0EFTJanusLLBraneCompositeMeasureVariation
open P0EFTJanusLLBraneCompositeMeasureFrechet
open P0EFTJanusExplicitBoundaryDensityLocalVariations

local instance (priority := 3000) realScalarAddGroup : AddCommGroup Real :=
  NormedField.toNormedCommRing.toAddCommGroup
local instance (priority := 3000) realNormedModule : Module Real Real :=
  (NormedAlgebra.toNormedSpace Real : NormedSpace Real Real).toModule

def scalarCoefficient (jet : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3)
    (volumeDensity : Real) : Real := compositeMeasure jet / volumeDensity

theorem scalarCoefficient_times_volume (jet : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3)
    (rho : Real) (hRho : rho ≠ 0) : scalarCoefficient jet rho * rho = compositeMeasure jet :=
  div_mul_cancel₀ _ hRho

/-- This oriented statement transforms both numerator and reference density. -/
theorem scalarCoefficient_coordinate_invariant
    (inverseJacobian jet : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3)
    (rho : Real) (hJacobian : Matrix.det inverseJacobian ≠ 0) :
    scalarCoefficient (coordinateReparametrizedJet inverseJacobian jet)
      (Matrix.det inverseJacobian * rho) = scalarCoefficient jet rho := by
  unfold scalarCoefficient
  rw [compositeMeasure_coordinateReparametrized]
  exact mul_div_mul_left _ _ hJacobian

/-- Varying the reference volume contributes the quotient-rule term. -/
theorem scalarCoefficient_curve_hasDerivAt
    (jet variation : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3)
    (rho deltaRho : Real) (hRho : rho ≠ 0) :
    HasDerivAt (fun t : Real => scalarCoefficient (auxiliaryJetCurve jet variation t)
        (rho + t * deltaRho))
      ((compositeMeasureVariation jet variation * rho - compositeMeasure jet * deltaRho) /
        rho ^ 2) 0 := by
  simpa only [scalarCoefficient, auxiliaryJetCurve, zero_mul, add_zero, zero_smul] using
    (compositeMeasure_curve_hasDerivAt jet variation).fun_div
      (affineScalar_hasDerivAt rho deltaRho) (by simpa using hRho)

theorem determinant_radial_variation
    (jet : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3) :
    compositeMeasureVariation jet jet = 3 * compositeMeasure jet := by
  simp only [compositeMeasureVariation, compositeMeasure, Matrix.det_fin_three]
  ring

/-- Pointwise realization of every scalar direction at a nondegenerate jet;
the word pointwise is essential for the later global variational problem. -/
theorem scalar_tangent_surjective
    (jet : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3)
    (rho : Real) (hRho : rho ≠ 0) (hJet : compositeMeasure jet ≠ 0) :
    Function.Surjective (fun variation => compositeMeasureVariation jet variation / rho) := by
  intro direction
  refine ⟨(rho * direction / (3 * compositeMeasure jet)) • jet, ?_⟩
  dsimp only
  rw [← compositeMeasureFrechetDerivative_apply, map_smul,
    compositeMeasureFrechetDerivative_apply, determinant_radial_variation]
  simp only [smul_eq_mul]
  field_simp

/-- Singular jets cannot be silently included in the nondegenerate argument. -/
theorem zero_jet_has_no_scalar_tangent (rho : Real) :
    ∀ variation : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3,
      compositeMeasureVariation 0 variation / rho = 0 := by
  intro variation
  simp [compositeMeasureVariation]

/-- Pulling back a differentiable scalar potential gives the actual composite
variation, not an assumed independent variation of chi. -/
theorem composite_potential_curve_hasDerivAt
    (jet variation : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3)
    (rho : Real) (hRho : rho ≠ 0) (potential : Real → Real) (slope : Real)
    (hPotential : HasDerivAt potential slope (scalarCoefficient jet rho)) :
    HasDerivAt (fun t : Real => potential (scalarCoefficient (auxiliaryJetCurve jet variation t) rho))
      (slope * (compositeMeasureVariation jet variation / rho)) 0 := by
  have hRatio := scalarCoefficient_curve_hasDerivAt jet variation rho 0 hRho
  have hFixed : HasDerivAt
      (fun t : Real => scalarCoefficient (auxiliaryJetCurve jet variation t) rho)
      (compositeMeasureVariation jet variation / rho) 0 := by
    convert hRatio using 1 <;> simp
    field_simp
  have h := hPotential.comp_of_eq (0 : Real) hFixed (by simp [auxiliaryJetCurve])
  exact h

/-- Coordinate density matching chi * fluxEnergy + U(chi) after multiplication
by the supplied oriented reference volume density. -/
def chartDensity (jet : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3)
    (rho fluxEnergy : Real) (potential : Real → Real) : Real :=
  compositeMeasure jet * fluxEnergy + rho * potential (scalarCoefficient jet rho)

theorem chartDensity_eq_scalar_density
    (jet : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3)
    (rho fluxEnergy : Real) (hRho : rho ≠ 0) (potential : Real → Real) :
    chartDensity jet rho fluxEnergy potential =
      rho * (scalarCoefficient jet rho * fluxEnergy + potential (scalarCoefficient jet rho)) := by
  unfold chartDensity scalarCoefficient
  field_simp

/-- Varying the composite measure and reference volume together yields both
the multiplier coefficient and the volume coefficient U - chi U'. The flux
energy is held fixed here; no global auxiliary-field Euler PDE is inferred. -/
theorem chartDensity_curve_hasDerivAt
    (jet variation : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3)
    (rho deltaRho fluxEnergy : Real) (hRho : rho ≠ 0)
    (potential : Real → Real) (slope : Real)
    (hPotential : HasDerivAt potential slope (scalarCoefficient jet rho)) :
    HasDerivAt (fun t : Real => chartDensity (auxiliaryJetCurve jet variation t)
        (rho + t * deltaRho) fluxEnergy potential)
      ((fluxEnergy + slope) * compositeMeasureVariation jet variation +
        (potential (scalarCoefficient jet rho) - scalarCoefficient jet rho * slope) * deltaRho) 0 := by
  have hRhoCurve := affineScalar_hasDerivAt rho deltaRho
  have hRatio := scalarCoefficient_curve_hasDerivAt jet variation rho deltaRho hRho
  have hPot := hPotential.comp_of_eq (0 : Real) hRatio (by simp [auxiliaryJetCurve])
  have hTotal := ((compositeMeasure_curve_hasDerivAt jet variation).mul_const fluxEnergy).fun_add
    (hRhoCurve.fun_mul hPot)
  apply hTotal.congr_deriv
  simp only [Function.comp_def, auxiliaryJetCurve, zero_smul, add_zero, zero_mul]
  unfold scalarCoefficient
  field_simp
  ring

end
end P0EFTJanusT08CompositeMeasureScalarBridge
end JanusFormal
