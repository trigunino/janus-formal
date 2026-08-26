import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPVectorBundleCoreSmoothSectionCriterion4D

/-!
# Sections assembled from compatible vector-bundle core representatives

Compatible local representatives determine a global section by choosing the
core index at each base point.  Its coordinate in every core chart is the
prescribed representative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff
open P0EFTJanusProgramPVectorBundleCoreSmoothSectionCriterion4D

variable {𝕜 B F ι : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace B]

/-- The section selected from a family of local representatives using the
preferred core index at each point. -/
def vectorBundleCoreSectionOfLocalRepresentatives
    (core : VectorBundleCore 𝕜 B F ι)
    (localRep : ι → B → F) (base : B) : core.Fiber base :=
  localRep (core.indexAt base) base

/-- Compatibility on overlaps identifies the selected section with every
prescribed local representative in that chart. -/
theorem vectorBundleCoreSectionOfLocalRepresentatives_localCoordinate
    (core : VectorBundleCore 𝕜 B F ι)
    (localRep : ι → B → F)
    (hCompatible : ∀ first second base,
      base ∈ core.baseSet first ∩ core.baseSet second →
        core.coordChange first second base (localRep first base) =
          localRep second base)
    (index : ι) (base : B) (hBase : base ∈ core.baseSet index) :
    ((core.localTriv index)
      ⟨base, vectorBundleCoreSectionOfLocalRepresentatives core localRep base⟩).2 =
        localRep index base := by
  rw [core.localTriv_apply]
  exact hCompatible (core.indexAt base) index base
    ⟨core.mem_baseSet_at base, hBase⟩

/-- Smooth compatible local representatives assemble into a smooth global
section of the smooth vector bundle defined by the core. -/
theorem vectorBundleCoreSectionOfLocalRepresentatives_contMDiff
    {EB HB : Type*}
    [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    [TopologicalSpace HB]
    (IB : ModelWithCorners 𝕜 EB HB)
    [ChartedSpace HB B]
    (core : VectorBundleCore 𝕜 B F ι)
    {n : ℕ∞ω}
    [core.IsContMDiff IB n]
    (localRep : ι → B → F)
    (hCompatible : ∀ first second base,
      base ∈ core.baseSet first ∩ core.baseSet second →
        core.coordChange first second base (localRep first base) =
          localRep second base)
    (hSmooth : ∀ index,
      ContMDiffOn IB (modelWithCornersSelf 𝕜 F) n
        (localRep index) (core.baseSet index)) :
    ContMDiff IB (IB.prod (modelWithCornersSelf 𝕜 F)) n
      (fun base ↦ TotalSpace.mk' F base
        (vectorBundleCoreSectionOfLocalRepresentatives core localRep base)) := by
  apply vectorBundleCore_section_contMDiff_of_localCoordinates IB core
    (vectorBundleCoreSectionOfLocalRepresentatives core localRep)
  intro index
  apply (hSmooth index).congr
  intro base hBase
  exact vectorBundleCoreSectionOfLocalRepresentatives_localCoordinate
    core localRep hCompatible index base hBase

end
end P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D
end JanusFormal
