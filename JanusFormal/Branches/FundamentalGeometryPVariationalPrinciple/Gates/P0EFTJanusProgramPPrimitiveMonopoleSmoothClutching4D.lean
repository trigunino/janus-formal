import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D

/-!
# Smooth primitive monopole clutching

The clutching phase used by the topological principal bundle is smooth on
the north/south overlap.  The proof factors it through normalization on the
open set of nonzero complex numbers.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveMonopoleSmoothClutching4D

set_option autoImplicit false
noncomputable section

open Set Metric Topology
open scoped Manifold ContDiff
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D

local instance monopoleSphereChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 2)) MonopoleSphere :=
  inferInstance

local instance euclideanR3Finrank :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

local instance complexRealFinrank :
    Fact (Module.finrank Real Complex = 1 + 1) :=
  finrank_real_complex_fact'

/-- Ambient real-linear map selecting `x + i y`. -/
def monopoleSphereXYCLM :
    EuclideanSpace Real (Fin 3) →L[Real] Complex :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).prod
      (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)))

@[simp]
theorem monopoleSphereXYCLM_apply
    (point : EuclideanSpace Real (Fin 3)) :
    monopoleSphereXYCLM point = ⟨point 0, point 1⟩ := by
  apply Complex.ext <;> rfl

/-- Analytic inclusion for the concrete `S² ⊂ ℝ³` chart instance. -/
theorem monopoleSphereCoe_contMDiff :
    ContMDiff (𝓡 2)
      𝓘(Real, EuclideanSpace Real (Fin 3)) ∞
      ((↑) : MonopoleSphere →
        EuclideanSpace Real (Fin 3)) := by
  rw [contMDiff_iff]
  constructor
  · exact continuous_subtype_val
  · intro point _
    let coordinates :
        (Real ∙ (↑(-point) :
          EuclideanSpace Real (Fin 3)))ᗮ ≃ₗᵢ[Real]
            EuclideanSpace Real (Fin 2) :=
      (OrthonormalBasis.fromOrthogonalSpanSingleton
        2 (ne_zero_of_mem_unit_sphere (-point))).repr
    exact
      ((contDiff_stereoInvFunAux.comp
          (Real ∙ (↑(-point) :
            EuclideanSpace Real (Fin 3)))ᗮ.subtypeL.contDiff).comp
        coordinates.symm.contDiff).contDiffOn

/-- Every ambient coordinate restricts to an analytic scalar on `S²`. -/
theorem monopoleSphereCoordinate_contMDiff (index : Fin 3) :
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (fun point : MonopoleSphere =>
        monopoleSphereCoordinate point index) := by
  have hSmooth :=
    (EuclideanSpace.proj (𝕜 := Real) index).contDiff.contMDiff.comp
      monopoleSphereCoe_contMDiff
  convert hSmooth using 1
  funext point
  rfl

/-- The equatorial complex coordinate is analytic on the sphere. -/
theorem monopoleSphereXY_contMDiff :
    ContMDiff (𝓡 2) 𝓘(Real, Complex) ∞ monopoleSphereXY := by
  have hSmooth :=
    monopoleSphereXYCLM.contDiff.contMDiff.comp
      monopoleSphereCoe_contMDiff
  convert hSmooth using 1
  funext point
  simp [monopoleSphereXY, monopoleSphereCoordinate,
    Function.comp_def]

private def complexNonzeroOpen : TopologicalSpace.Opens Complex :=
  ⟨{0}ᶜ, isOpen_compl_singleton⟩

/-- Smooth unit normalization on the nonzero complex plane. -/
def complexUnitNormalization
    (value : complexNonzeroOpen) : Circle := by
  refine ⟨NormedSpace.normalize (value : Complex), ?_⟩
  simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using
    NormedSpace.norm_normalize value.2

theorem complexUnitNormalization_contMDiff :
    ContMDiff 𝓘(Real, Complex) (𝓡 1) ∞
      complexUnitNormalization := by
  have hValue :
      ContMDiff 𝓘(Real, Complex) 𝓘(Real, Complex) ∞
        (fun value : complexNonzeroOpen => (value : Complex)) :=
    contMDiff_subtype_val
  have hNorm :
      ContMDiff 𝓘(Real, Complex) 𝓘(Real) ∞
        (fun value : complexNonzeroOpen =>
          ‖(value : Complex)‖) := by
    intro value
    exact
      (contDiffAt_norm Real value.2).comp_contMDiffAt
        hValue.contMDiffAt
  have hInvNorm :
      ContMDiff 𝓘(Real, Complex) 𝓘(Real) ∞
        (fun value : complexNonzeroOpen =>
          ‖(value : Complex)‖⁻¹) :=
    hNorm.inv₀ fun value => norm_ne_zero_iff.mpr value.2
  have hNormalized :
      ContMDiff 𝓘(Real, Complex) 𝓘(Real, Complex) ∞
        (fun value : complexNonzeroOpen =>
          ‖(value : Complex)‖⁻¹ • (value : Complex)) :=
    hInvNorm.smul hValue
  apply ContMDiff.codRestrict_sphere
  simpa [complexUnitNormalization, NormedSpace.normalize] using
    hNormalized

private def monopoleOverlapOpen :
    TopologicalSpace.Opens MonopoleSphere :=
  ⟨monopoleChartDomain .north ∩ monopoleChartDomain .south,
    (monopoleChartDomain_isOpen .north).inter
      (monopoleChartDomain_isOpen .south)⟩

private def monopoleOverlapXY
    (point : monopoleOverlapOpen) : complexNonzeroOpen :=
  ⟨monopoleSphereXY point.1,
    monopoleSphereXY_ne_zero_of_mem_overlap
      point.1 point.2.1 point.2.2⟩

private theorem monopoleOverlapXY_contMDiff :
    ContMDiff (𝓡 2) 𝓘(Real, Complex) ∞ monopoleOverlapXY := by
  rw [← ContMDiff.subtypeVal_comp_iff
    complexNonzeroOpen monopoleOverlapXY]
  exact monopoleSphereXY_contMDiff.comp contMDiff_subtype_val

private theorem monopoleOverlap_normalization_eq_phase
    (point : monopoleOverlapOpen) :
    complexUnitNormalization (monopoleOverlapXY point) =
      monopoleSphereXYPhase point.1 := by
  apply Circle.ext
  rw [monopoleSphereXYPhase_coe_of_ne_zero
    point.1 (monopoleOverlapXY point).2]
  rfl

private theorem monopoleSphereXYPhase_contMDiff_restrict :
    ContMDiff (𝓡 2) (𝓡 1) ∞
      (fun point : monopoleOverlapOpen =>
        monopoleSphereXYPhase point.1) := by
  exact
    (complexUnitNormalization_contMDiff.comp
      monopoleOverlapXY_contMDiff).congr fun point =>
        (monopoleOverlap_normalization_eq_phase point).symm

/-- The clutching phase is smooth exactly where it is used. -/
theorem monopoleSphereXYPhase_contMDiffOn_overlap :
    ContMDiffOn (𝓡 2) (𝓡 1) ∞ monopoleSphereXYPhase
      (monopoleChartDomain .north ∩ monopoleChartDomain .south) := by
  intro point hPoint
  let restricted : monopoleOverlapOpen := ⟨point, hPoint⟩
  have hRestricted :=
    monopoleSphereXYPhase_contMDiff_restrict.contMDiffAt
      (x := restricted)
  exact (contMDiffAt_subtype_iff.mp hRestricted).contMDiffWithinAt

end
end P0EFTJanusProgramPPrimitiveMonopoleSmoothClutching4D
end JanusFormal
