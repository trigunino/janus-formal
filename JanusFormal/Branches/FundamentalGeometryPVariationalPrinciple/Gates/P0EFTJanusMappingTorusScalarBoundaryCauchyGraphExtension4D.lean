import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D

/-!
# Bounded smooth Cauchy extensions and completed trace surjectivity

Let smooth value and normal cores be dense in the two boundary Hilbert
components.  Suppose a linear smooth bulk extension realizes each pair of core
Cauchy data and satisfies a graph-norm estimate controlled by the boundary norm.

The extension then prolongs continuously from the dense boundary core to the
entire boundary Hilbert pair.  Agreement on the dense core and continuity prove
that the prolonged map is a right inverse of the completed Cauchy trace.
Therefore completed trace surjectivity follows from a concrete smooth collar
extension estimate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarBoundaryCauchyGraphExtension4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D

universe u v w x y

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  {ValueCore : Type x} {NormalCore : Type y}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  [AddCommGroup ValueCore] [Module Real ValueCore]
  [AddCommGroup NormalCore] [Module Real NormalCore]

/-- Smooth Cauchy extension with a graph-norm estimate. -/
structure CanonicalScalarBoundedSmoothCauchyExtensionData
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) where
  smooth : CanonicalScalarSmoothCauchyExtensionData
    (ValueCore := ValueCore) (NormalCore := NormalCore) core.boundaryTrace
  constant : Real
  nonnegative : 0 ≤ constant
  graph_bound : ∀ data : ValueCore × NormalCore,
    ‖canonicalScalarGreenCoreToGraph core (smooth.extension data)‖ ≤
      constant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          smooth.valueEmbedding smooth.normalEmbedding data‖

namespace CanonicalScalarBoundedSmoothCauchyExtensionData

/-- Dense boundary-core embedding. -/
def boundaryCoreEmbedding
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    ValueCore × NormalCore →ₗ[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace) :=
  canonicalScalarBoundaryCorePairEmbedding
    extensionData.smooth.valueEmbedding extensionData.smooth.normalEmbedding

/-- Smooth graph lift of boundary-core data. -/
def smoothGraphExtension
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    ValueCore × NormalCore →ₗ[Real]
      CanonicalScalarGreenCoreGraphSpace core :=
  (canonicalScalarGreenCoreToGraph core).comp extensionData.smooth.extension

/-- The boundary-core embedding has dense range. -/
theorem boundaryCoreEmbedding_denseRange
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    DenseRange extensionData.boundaryCoreEmbedding :=
  extensionData.smooth.pairEmbedding_denseRange

/-- The smooth graph extension obeys the extension norm estimate. -/
theorem smoothGraphExtension_norm_le
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (data : ValueCore × NormalCore) :
    ‖extensionData.smoothGraphExtension data‖ ≤
      extensionData.constant * ‖extensionData.boundaryCoreEmbedding data‖ :=
  extensionData.graph_bound data

/-- Continuous Cauchy extension from the full boundary Hilbert pair to the
completed maximal graph. -/
def completedExtension
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    CanonicalScalarHilbertBoundaryDatum (Trace := Trace) →L[Real]
      CanonicalScalarGreenCoreGraphSpace core :=
  extensionData.smoothGraphExtension.extendOfNorm
    extensionData.boundaryCoreEmbedding

/-- Agreement of the completed extension with the smooth graph lift on core
boundary data. -/
theorem completedExtension_core
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (data : ValueCore × NormalCore) :
    extensionData.completedExtension
        (extensionData.boundaryCoreEmbedding data) =
      extensionData.smoothGraphExtension data :=
  LinearMap.extendOfNorm_eq
    extensionData.boundaryCoreEmbedding_denseRange
    ⟨extensionData.constant, extensionData.smoothGraphExtension_norm_le⟩ data

/-- Norm estimate for the completed extension. -/
theorem completedExtension_norm_le
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (boundary : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    ‖extensionData.completedExtension boundary‖ ≤
      extensionData.constant * ‖boundary‖ :=
  LinearMap.norm_extendOfNorm_apply_le
    extensionData.boundaryCoreEmbedding_denseRange
    extensionData.constant extensionData.smoothGraphExtension_norm_le boundary

/-- The completed extension is a right inverse of the completed Cauchy trace. -/
theorem completedBoundaryTrace_extension
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core)
    (boundary : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarGreenCoreCompletedBoundaryTrace core traceBound
        (extensionData.completedExtension boundary) = boundary := by
  let good : Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :=
    {candidate |
      canonicalScalarGreenCoreCompletedBoundaryTrace core traceBound
          (extensionData.completedExtension candidate) = candidate}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range extensionData.boundaryCoreEmbedding ⊆ good := by
    rintro candidate ⟨data, rfl⟩
    rw [extensionData.completedExtension_core]
    change canonicalScalarGreenCoreCompletedBoundaryTrace core traceBound
        (canonicalScalarGreenCoreToGraph core
          (extensionData.smooth.extension data)) = _
    rw [canonicalScalarGreenCoreCompletedBoundaryTrace_smooth]
    exact extensionData.smooth.boundary_extension data
  have hClosure : closure
      (Set.range extensionData.boundaryCoreEmbedding) = Set.univ :=
    extensionData.boundaryCoreEmbedding_denseRange.closure_range
  have hBoundary : boundary ∈ closure
      (Set.range extensionData.boundaryCoreEmbedding) := by
    rw [hClosure]
    trivial
  exact (closure_minimal hRange hGoodClosed) hBoundary

/-- Completed trace surjectivity. -/
theorem completedBoundaryTrace_surjective
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core) :
    Function.Surjective
      (canonicalScalarGreenCoreCompletedBoundaryTrace core traceBound) := by
  intro boundary
  exact ⟨extensionData.completedExtension boundary,
    extensionData.completedBoundaryTrace_extension traceBound boundary⟩

/-- Convert the bounded smooth extension to the generic completed-extension
package. -/
def toCompletedCauchyExtensionData
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core) :
    CanonicalScalarCompletedCauchyExtensionData core traceBound where
  extension := extensionData.completedExtension
  boundary_extension := extensionData.completedBoundaryTrace_extension traceBound

/-- Bounded smooth extension certificate. -/
theorem certificate
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core) :
    Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace core traceBound) ∧
      (∀ boundary : CanonicalScalarHilbertBoundaryDatum (Trace := Trace),
        ‖extensionData.completedExtension boundary‖ ≤
          extensionData.constant * ‖boundary‖) :=
  ⟨extensionData.completedBoundaryTrace_surjective traceBound,
    extensionData.completedExtension_norm_le⟩

end CanonicalScalarBoundedSmoothCauchyExtensionData

end
end P0EFTJanusMappingTorusScalarBoundaryCauchyGraphExtension4D
end JanusFormal
