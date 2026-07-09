import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4DeterminantMeasureVariation
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4FullActionAssemblyTarget

namespace JanusFormal
namespace P0EFTJanusZ4DeterminantMeasureAssemblyBridge

set_option autoImplicit false

abbrev DeterminantMeasureVariation :=
  P0EFTJanusZ4DeterminantMeasureVariation.DeterminantMeasureVariation

abbrev FullActionAssemblyTarget :=
  P0EFTJanusZ4FullActionAssemblyTarget.FullActionAssemblyTarget

def determinantMeasureInsertedByAssembly
    (m : DeterminantMeasureVariation)
    (a : FullActionAssemblyTarget) : Prop :=
  P0EFTJanusZ4DeterminantMeasureVariation.measureVariationScaffoldReady m /\
  P0EFTJanusZ4FullActionAssemblyTarget.fullActionAssemblyScaffoldReady a /\
  m.insertedIntoFullActionVariation /\
  a.determinantMeasureVariationInserted

theorem assembly_bridge_closes_determinant_measure_physical_ready
    (m : DeterminantMeasureVariation)
    (a : FullActionAssemblyTarget)
    (h : determinantMeasureInsertedByAssembly m a) :
    P0EFTJanusZ4DeterminantMeasureVariation.measureVariationPhysicalReady m := by
  exact And.intro h.left h.right.right.left

theorem missing_measure_insertion_blocks_bridge
    (m : DeterminantMeasureVariation)
    (a : FullActionAssemblyTarget)
    (hMissing : Not m.insertedIntoFullActionVariation) :
    Not (determinantMeasureInsertedByAssembly m a) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTJanusZ4DeterminantMeasureAssemblyBridge
end JanusFormal
