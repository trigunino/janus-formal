import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08CompositeMeasureScalarBridge
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D

/-!
# T08: genuine global auxiliary fields and their induced measure variations

Three globally defined smooth real fields on the actual throat supply their
jets by manifold differentiation. A tangent triple evaluates the resulting
three-form; it is supplied, and need not be a global basis. Variations are
smooth auxiliary fields, not arbitrary matrix-valued functions. This module
does not claim existence of an everywhere nondegenerate composite measure.
-/
namespace JanusFormal
namespace P0EFTJanusT08GlobalCompositeAuxiliaryVariation4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusLLBraneCompositeMeasureVariation
open P0EFTJanusT08CompositeMeasureScalarBridge

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (Throat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (Throat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

abbrev AuxiliaryFields := Fin 3 → SmoothThroatField period hPeriod Real
abbrev TangentTriple (point : Throat period hPeriod) :=
  Fin 3 → TangentSpace throatCoverModelWithCorners point

/-- Coordinate index first, auxiliary-field index second, matching the
existing determinant model. Entries are actual manifold derivatives. -/
def auxiliaryJet (fields : AuxiliaryFields period hPeriod)
    (point : Throat period hPeriod) (vectors : TangentTriple period hPeriod point) :
    P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3 :=
  fun row column => mvfderiv throatCoverModelWithCorners (fields column).toFun point
    (vectors row)

theorem auxiliaryJet_add (fields variation : AuxiliaryFields period hPeriod)
    (point : Throat period hPeriod) (vectors : TangentTriple period hPeriod point) :
    auxiliaryJet period hPeriod (fields + variation) point vectors =
      auxiliaryJet period hPeriod fields point vectors +
        auxiliaryJet period hPeriod variation point vectors := by
  funext row column
  change mvfderiv throatCoverModelWithCorners
    ((fields column).toFun + (variation column).toFun) point (vectors row) = _
  rw [mvfderiv_add
    (((fields column).contMDiff_toFun.mdifferentiable (by simp)) point)
    (((variation column).contMDiff_toFun.mdifferentiable (by simp)) point)]
  rfl

theorem auxiliaryJet_smul (fields : AuxiliaryFields period hPeriod) (scalar : Real)
    (point : Throat period hPeriod) (vectors : TangentTriple period hPeriod point) :
    auxiliaryJet period hPeriod (scalar • fields) point vectors =
      scalar • auxiliaryJet period hPeriod fields point vectors := by
  funext row column
  change mvfderiv throatCoverModelWithCorners
    (scalar • (fields column).toFun) point (vectors row) = _
  unfold mvfderiv
  rw [const_smul_mfderiv
    (((fields column).contMDiff_toFun.mdifferentiable (by simp)) point) scalar]
  rfl

theorem auxiliaryJet_change_vectors (fields : AuxiliaryFields period hPeriod)
    (point : Throat period hPeriod) (vectors : TangentTriple period hPeriod point)
    (changeOfVectors : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3) :
    auxiliaryJet period hPeriod fields point
      (fun row => ∑ index : Fin 3, changeOfVectors row index • vectors index) =
      changeOfVectors * auxiliaryJet period hPeriod fields point vectors := by
  funext row column
  simp [auxiliaryJet, Matrix.mul_apply, map_sum, map_smul, smul_eq_mul]

/-- The scalar ratio is independent of an invertible change of tangent
triple when the reference volume is evaluated on the same new triple. -/
theorem global_scalar_change_vectors (fields : AuxiliaryFields period hPeriod)
    (point : Throat period hPeriod) (vectors : TangentTriple period hPeriod point)
    (changeOfVectors : P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3)
    (hChange : Matrix.det changeOfVectors ≠ 0) (rho : Real) :
    scalarCoefficient (auxiliaryJet period hPeriod fields point
      (fun row => ∑ index : Fin 3, changeOfVectors row index • vectors index))
      (Matrix.det changeOfVectors * rho) =
      scalarCoefficient (auxiliaryJet period hPeriod fields point vectors) rho := by
  rw [auxiliaryJet_change_vectors]
  exact scalarCoefficient_coordinate_invariant changeOfVectors
    (auxiliaryJet period hPeriod fields point vectors) rho hChange

/-- Every matrix curve used below is induced by an admissible global smooth
auxiliary-field curve, not postulated independently at each point. -/
theorem auxiliaryJet_affine (fields variation : AuxiliaryFields period hPeriod)
    (point : Throat period hPeriod) (vectors : TangentTriple period hPeriod point) (t : Real) :
    auxiliaryJet period hPeriod (fields + t • variation) point vectors =
      auxiliaryJetCurve (auxiliaryJet period hPeriod fields point vectors)
        (auxiliaryJet period hPeriod variation point vectors) t := by
  rw [auxiliaryJet_add, auxiliaryJet_smul]
  rfl

theorem induced_measure_hasDerivAt (fields variation : AuxiliaryFields period hPeriod)
    (point : Throat period hPeriod) (vectors : TangentTriple period hPeriod point) :
    HasDerivAt (fun t : Real => compositeMeasure
      (auxiliaryJet period hPeriod (fields + t • variation) point vectors))
      (compositeMeasureVariation (auxiliaryJet period hPeriod fields point vectors)
        (auxiliaryJet period hPeriod variation point vectors)) 0 := by
  simpa only [auxiliaryJet_affine] using
    compositeMeasure_curve_hasDerivAt (auxiliaryJet period hPeriod fields point vectors)
      (auxiliaryJet period hPeriod variation point vectors)

/-- Pullback of the independent-scalar formula along actual auxiliary fields.
The reference volume may vary; flux energy is held fixed. -/
theorem induced_density_hasDerivAt (fields variation : AuxiliaryFields period hPeriod)
    (point : Throat period hPeriod) (vectors : TangentTriple period hPeriod point)
    (rho deltaRho fluxEnergy : Real) (hRho : rho ≠ 0)
    (potential : Real → Real) (slope : Real)
    (hPotential : HasDerivAt potential slope
      (scalarCoefficient (auxiliaryJet period hPeriod fields point vectors) rho)) :
    HasDerivAt (fun t : Real => chartDensity
      (auxiliaryJet period hPeriod (fields + t • variation) point vectors)
      (rho + t * deltaRho) fluxEnergy potential)
      ((fluxEnergy + slope) * compositeMeasureVariation
          (auxiliaryJet period hPeriod fields point vectors)
          (auxiliaryJet period hPeriod variation point vectors) +
        (potential (scalarCoefficient (auxiliaryJet period hPeriod fields point vectors) rho) -
          scalarCoefficient (auxiliaryJet period hPeriod fields point vectors) rho * slope) * deltaRho) 0 := by
  simpa only [auxiliaryJet_affine] using chartDensity_curve_hasDerivAt
    (auxiliaryJet period hPeriod fields point vectors)
    (auxiliaryJet period hPeriod variation point vectors)
    rho deltaRho fluxEnergy hRho potential slope hPotential

/-- A single admissible global radial variation induces three times the
composite density at every point. This does not prove arbitrary prescribed
scalar variations can be realized globally. -/
theorem global_radial_measure_variation (fields : AuxiliaryFields period hPeriod)
    (point : Throat period hPeriod) (vectors : TangentTriple period hPeriod point) :
    HasDerivAt (fun t : Real => compositeMeasure
      (auxiliaryJet period hPeriod (fields + t • fields) point vectors))
      (3 * compositeMeasure (auxiliaryJet period hPeriod fields point vectors)) 0 := by
  simpa only [determinant_radial_variation] using
    induced_measure_hasDerivAt period hPeriod fields fields point vectors

/-- Constant translations of all auxiliary fields have zero induced jet. -/
def constantAuxiliary (values : Fin 3 → Real) : AuxiliaryFields period hPeriod :=
  fun index => ⟨fun _ => values index, contMDiff_const⟩

theorem auxiliaryJet_constant (values : Fin 3 → Real)
    (point : Throat period hPeriod) (vectors : TangentTriple period hPeriod point) :
    auxiliaryJet period hPeriod (constantAuxiliary period hPeriod values) point vectors = 0 := by
  funext row column
  change mvfderiv throatCoverModelWithCorners (fun _ => values column) point (vectors row) = 0
  rw [mvfderiv_const]
  rfl

theorem constant_translation_preserves_measure (fields : AuxiliaryFields period hPeriod)
    (values : Fin 3 → Real) (point : Throat period hPeriod)
    (vectors : TangentTriple period hPeriod point) :
    compositeMeasure (auxiliaryJet period hPeriod
      (fields + constantAuxiliary period hPeriod values) point vectors) =
      compositeMeasure (auxiliaryJet period hPeriod fields point vectors) := by
  rw [auxiliaryJet_add, auxiliaryJet_constant, add_zero]

end
end P0EFTJanusT08GlobalCompositeAuxiliaryVariation4D
end JanusFormal
