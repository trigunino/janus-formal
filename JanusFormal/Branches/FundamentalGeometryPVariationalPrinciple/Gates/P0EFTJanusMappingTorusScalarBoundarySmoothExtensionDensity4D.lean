import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

/-!
# Dense smooth boundary trace from a Cauchy extension operator

For an infinite-dimensional boundary Hilbert space, smooth boundary data form a
dense proper subspace.  To prove density of the smooth bulk Cauchy trace it is
enough to:

* choose dense smooth value and normal cores;
* embed them linearly into the boundary Hilbert space;
* construct a smooth bulk extension realizing every pair of core data.

This file proves that reduction abstractly.  It also records the stronger
completed extension operator that implies surjectivity of the graph-completed
Cauchy trace.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

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

/-- Product embedding of dense smooth value and normal cores. -/
def canonicalScalarBoundaryCorePairEmbedding
    (valueEmbedding : ValueCore →ₗ[Real] Trace)
    (normalEmbedding : NormalCore →ₗ[Real] Trace) :
    ValueCore × NormalCore →ₗ[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace) where
  toFun data := (valueEmbedding data.1, normalEmbedding data.2)
  map_add' first second := by ext <;> simp
  map_smul' scalar data := by ext <;> simp

/-- Product of two dense linear ranges is dense. -/
theorem canonicalScalarBoundaryCorePairEmbedding_denseRange
    (valueEmbedding : ValueCore →ₗ[Real] Trace)
    (normalEmbedding : NormalCore →ₗ[Real] Trace)
    (hValueDense : DenseRange valueEmbedding)
    (hNormalDense : DenseRange normalEmbedding) :
    DenseRange
      (canonicalScalarBoundaryCorePairEmbedding
        valueEmbedding normalEmbedding) := by
  intro boundary
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨value, hValue⟩ :=
    (Metric.mem_closure_iff.mp (hValueDense boundary.1)) ε hε
  obtain ⟨normal, hNormal⟩ :=
    (Metric.mem_closure_iff.mp (hNormalDense boundary.2)) ε hε
  refine ⟨(value, normal), ?_⟩
  change max
      (dist (valueEmbedding value) boundary.1)
      (dist (normalEmbedding normal) boundary.2) < ε
  exact max_lt hValue hNormal

/-- Smooth Cauchy-extension data for one Hilbert Green core. -/
structure CanonicalScalarSmoothCauchyExtensionData
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) where
  valueEmbedding : ValueCore →ₗ[Real] Trace
  normalEmbedding : NormalCore →ₗ[Real] Trace
  valueDense : DenseRange valueEmbedding
  normalDense : DenseRange normalEmbedding
  extension : ValueCore × NormalCore →ₗ[Real] Domain
  boundary_extension : ∀ data,
    core.boundaryTrace (extension data) =
      canonicalScalarBoundaryCorePairEmbedding
        valueEmbedding normalEmbedding data

namespace CanonicalScalarSmoothCauchyExtensionData

/-- The embedded smooth boundary-pair core has dense range. -/
theorem pairEmbedding_denseRange
    (extensionData : CanonicalScalarSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    DenseRange
      (canonicalScalarBoundaryCorePairEmbedding
        extensionData.valueEmbedding extensionData.normalEmbedding) :=
  canonicalScalarBoundaryCorePairEmbedding_denseRange
    extensionData.valueEmbedding extensionData.normalEmbedding
    extensionData.valueDense extensionData.normalDense

/-- A smooth Cauchy extension proves density of the smooth bulk boundary trace. -/
theorem boundaryTrace_denseRange
    (extensionData : CanonicalScalarSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    DenseRange core.boundaryTrace := by
  intro boundary
  have hPairClosure := extensionData.pairEmbedding_denseRange boundary
  apply closure_mono ?_ hPairClosure
  intro boundaryCore hBoundaryCore
  rcases hBoundaryCore with ⟨data, rfl⟩
  refine ⟨extensionData.extension data, ?_⟩
  exact extensionData.boundary_extension data

/-- Build the corrected smooth Green core once the Cauchy extension is known. -/
def installBoundaryDensity
    (inclusion : Domain →ₗ[Real] Ambient)
    (operator : Domain →ₗ[Real] Ambient)
    (boundaryTrace : Domain →ₗ[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace))
    (greenIdentity : ∀ first second : Domain,
      inner Real (operator first) (inclusion second) -
          inner Real (inclusion first) (operator second) =
        2 * canonicalScalarHilbertBoundarySymplecticForm
          (boundaryTrace first) (boundaryTrace second))
    (extensionData : CanonicalScalarSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore)
      ({ inclusion := inclusion
         operator := operator
         boundaryTrace := boundaryTrace
         boundary_dense := by
           exact fun boundary => by
             simpa using extensionData.boundaryTrace_denseRange boundary
         green_identity := greenIdentity } :
        CanonicalScalarHilbertGreenCore
          (Domain := Domain) (Ambient := Ambient) (Trace := Trace))) :
    CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace) where
  inclusion := inclusion
  operator := operator
  boundaryTrace := boundaryTrace
  boundary_dense := extensionData.boundaryTrace_denseRange
  green_identity := greenIdentity

end CanonicalScalarSmoothCauchyExtensionData

/-- Continuous right inverse of the completed Cauchy trace. -/
structure CanonicalScalarCompletedCauchyExtensionData
    (core : CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core) where
  extension : CanonicalScalarHilbertBoundaryDatum (Trace := Trace) →L[Real]
    CanonicalScalarGreenCoreGraphSpace core
  boundary_extension : ∀ boundary,
    canonicalScalarGreenCoreCompletedBoundaryTrace core traceBound
        (extension boundary) = boundary

namespace CanonicalScalarCompletedCauchyExtensionData

/-- A continuous completed extension implies completed trace surjectivity. -/
theorem boundaryTrace_surjective
    (extensionData : CanonicalScalarCompletedCauchyExtensionData
      core traceBound) :
    Function.Surjective
      (canonicalScalarGreenCoreCompletedBoundaryTrace core traceBound) := by
  intro boundary
  exact ⟨extensionData.extension boundary,
    extensionData.boundary_extension boundary⟩

/-- Install the corrected completed boundary triple once minimal-core
closability is known. -/
def toBoundaryTriple
    (extensionData : CanonicalScalarCompletedCauchyExtensionData
      core traceBound)
    (hInclusion : Function.Injective
      (canonicalScalarGreenCoreGraphInclusion core)) :
    CanonicalScalarCompletedBoundaryTripleData core traceBound where
  boundary_surjective := extensionData.boundaryTrace_surjective
  inclusion_injective := hInclusion

/-- Completed extension certificate. -/
theorem certificate
    (extensionData : CanonicalScalarCompletedCauchyExtensionData
      core traceBound) :
    Function.Surjective
      (canonicalScalarGreenCoreCompletedBoundaryTrace core traceBound) ∧
      (∀ boundary,
        canonicalScalarGreenCoreCompletedBoundaryTrace core traceBound
            (extensionData.extension boundary) = boundary) :=
  ⟨extensionData.boundaryTrace_surjective,
    extensionData.boundary_extension⟩

end CanonicalScalarCompletedCauchyExtensionData

end
end P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
end JanusFormal
