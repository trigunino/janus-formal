import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08GlobalCompositeAuxiliaryVariation4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient

/-!
# T08: obstruction to an everywhere regular measure from global real auxiliaries

A real smooth function on the compact boundaryless throat has a critical
point. Applied to the first auxiliary field, this forces the composite
three-form to vanish there, for every tangent triple. Global real auxiliary
fields therefore cannot realize an everywhere nonzero scalar measure.
-/
namespace JanusFormal
namespace P0EFTJanusT08CompactCompositeMeasureObstruction4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusLLBraneCompositeMeasureVariation
open P0EFTJanusT08CompositeMeasureScalarBridge
open P0EFTJanusT08GlobalCompositeAuxiliaryVariation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (Throat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (Throat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (Throat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

/-- Fermat's theorem in the actual throat charts; their model has no boundary. -/
theorem scalar_derivative_zero_at_global_max
    (field : SmoothThroatField period hPeriod Real) (point : Throat period hPeriod)
    (hMax : ∀ other, field other ≤ field point) :
    mvfderiv throatCoverModelWithCorners field.toFun point = 0 := by
  let g : ThroatCoverCoordinates → Real :=
    field.toFun ∘ (extChartAt throatCoverModelWithCorners point).symm
  have hLocal : IsLocalMax g ((extChartAt throatCoverModelWithCorners point) point) := by
    apply Filter.Eventually.of_forall
    intro y
    simpa only [g, Function.comp_apply, extChartAt_to_inv] using
      hMax ((extChartAt throatCoverModelWithCorners point).symm y)
  have hZero := hLocal.fderiv_eq_zero
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    change Set.range (id : ThroatCoverCoordinates → ThroatCoverCoordinates) = Set.univ
    exact Set.range_id
  unfold mvfderiv
  rw [(field.contMDiff_toFun.mdifferentiable (by simp) point).mfderiv]
  simp only [hRange, fderivWithin_univ]
  have hWritten : writtenInExtChartAt throatCoverModelWithCorners 𝓘(Real, Real)
      point field.toFun = g := by
    simp only [writtenInExtChartAt, extChartAt_self_eq, modelWithCornersSelf_coe,
      Function.id_comp, g]
  rw [hWritten, hZero]
  rfl

theorem exists_critical_point (base : Throat period hPeriod)
    (field : SmoothThroatField period hPeriod Real) :
    ∃ point, mvfderiv throatCoverModelWithCorners field.toFun point = 0 := by
  obtain ⟨point, _, hMax⟩ := isCompact_univ.exists_isMaxOn ⟨base, mem_univ base⟩
    field.contMDiff_toFun.continuous.continuousOn
  exact ⟨point, scalar_derivative_zero_at_global_max period hPeriod field point
    (fun other => hMax (mem_univ other))⟩

/-- The zero is independent of the chosen tangent triple. -/
theorem composite_measure_has_zero (base : Throat period hPeriod)
    (fields : AuxiliaryFields period hPeriod) :
    ∃ point, ∀ vectors : TangentTriple period hPeriod point,
      compositeMeasure (auxiliaryJet period hPeriod fields point vectors) = 0 := by
  obtain ⟨point, hCritical⟩ := exists_critical_point period hPeriod base (fields 0)
  refine ⟨point, fun vectors => ?_⟩
  have hColumn : ∀ row : Fin 3, auxiliaryJet period hPeriod fields point vectors row 0 = 0 := by
    intro row
    simp [auxiliaryJet, hCritical]
  simp [compositeMeasure, Matrix.det_fin_three, hColumn]

/-- No globally real auxiliary triple realizes an everywhere nonzero chi,
regardless of the supplied reference density and tangent triples. -/
theorem no_everywhere_nonzero_scalar_realization (base : Throat period hPeriod)
    (fields : AuxiliaryFields period hPeriod)
    (vectors : ∀ point : Throat period hPeriod, TangentTriple period hPeriod point)
    (rho chi : Throat period hPeriod → Real) (hChi : ∀ point, chi point ≠ 0) :
    ¬ (∀ point, scalarCoefficient (auxiliaryJet period hPeriod fields point (vectors point))
      (rho point) = chi point) := by
  intro hRealizes
  obtain ⟨point, hZero⟩ := composite_measure_has_zero period hPeriod base fields
  apply hChi point
  rw [← hRealizes point]
  simp [scalarCoefficient, hZero]

end
end P0EFTJanusT08CompactCompositeMeasureObstruction4D
end JanusFormal
