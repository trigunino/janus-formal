import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureOperator4D

/-! Exact transport of a minimal graph closure under a bounded change of volume. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedFeatureVolumeTransport4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
variable {D H : Type*} [AddCommGroup D] [Module Real D]
  [NormedAddCommGroup H] [InnerProductSpace Real H]

theorem linearFeatureGraphClosure_volume_transport
    (inclusion first second : D →ₗ[Real] H) (weight : H ≃L[Real] H)
    (smoothWeight : D →ₗ[Real] D) (hSurjective : Function.Surjective smoothWeight)
    (hInclusion : ∀ field, inclusion (smoothWeight field) = weight (inclusion field))
    (hOperator : ∀ field, second (smoothWeight field) = weight (first field)) :
    linearFeatureGraphClosure inclusion second =
      (linearFeatureGraphClosure inclusion first).map (weight.prodCongr weight).toLinearMap := by
  apply SetLike.coe_injective
  change closure ((inclusion.prod second).range : Set (H × H)) =
    (weight.prodCongr weight) '' closure ((inclusion.prod first).range : Set (H × H))
  rw [(weight.prodCongr weight).image_closure]
  congr 1
  ext pair
  constructor
  · rintro ⟨field, rfl⟩
    obtain ⟨source, rfl⟩ := hSurjective field
    exact ⟨(inclusion source, first source), ⟨source, rfl⟩,
      Prod.ext (hInclusion source).symm (hOperator source).symm⟩
  · rintro ⟨_, ⟨field, rfl⟩, rfl⟩
    exact ⟨smoothWeight field, Prod.ext (hInclusion field) (hOperator field)⟩

end
end JanusFormal.P0EFTJanusProgramPT12ClosedFeatureVolumeTransport4D
