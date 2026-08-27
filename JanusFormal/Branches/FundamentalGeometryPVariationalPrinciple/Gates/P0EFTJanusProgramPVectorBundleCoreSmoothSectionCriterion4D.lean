import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Local criterion for smooth sections of a vector-bundle core

A section of the bundle defined by a smooth `VectorBundleCore` is smooth as
soon as its fiber coordinate is smooth on every core patch.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPVectorBundleCoreSmoothSectionCriterion4D

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

/-- Smoothness of all core-chart representatives implies smoothness of the
global section. -/
theorem vectorBundleCore_section_contMDiff_of_localCoordinates
    {𝕜 B F ι EB HB : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    [TopologicalSpace HB]
    (IB : ModelWithCorners 𝕜 EB HB)
    [TopologicalSpace B] [ChartedSpace HB B]
    (core : VectorBundleCore 𝕜 B F ι)
    {n : ℕ∞ω}
    [core.IsContMDiff IB n]
    (s : ∀ base, core.Fiber base)
    (hLocal : ∀ index,
      ContMDiffOn IB (modelWithCornersSelf 𝕜 F) n
        (fun base ↦ ((core.localTriv index) ⟨base, s base⟩).2)
        (core.baseSet index)) :
    ContMDiff IB (IB.prod (modelWithCornersSelf 𝕜 F)) n
      (fun base ↦ TotalSpace.mk' F base (s base)) := by
  intro base
  let index := core.indexAt base
  let localTriv := core.localTriv index
  letI : MemTrivializationAtlas localTriv := ⟨⟨index, rfl⟩⟩
  have hBase : base ∈ localTriv.baseSet := core.mem_baseSet_at base
  rw [localTriv.contMDiffAt_section_iff hBase]
  exact (hLocal index).contMDiffAt
    ((core.isOpen_baseSet index).mem_nhds hBase)

end
end P0EFTJanusProgramPVectorBundleCoreSmoothSectionCriterion4D
end JanusFormal
