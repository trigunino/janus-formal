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
  change DenseRange (Prod.map (fun value => valueEmbedding value)
    (fun normal => normalEmbedding normal))
  exact hValueDense.prodMap hNormalDense

/-- Smooth Cauchy-extension data for one raw smooth boundary trace.  Density is
a conclusion of this structure, not one of its inputs. -/
structure CanonicalScalarSmoothCauchyExtensionData
    (boundaryTrace : Domain →ₗ[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) where
  valueEmbedding : ValueCore →ₗ[Real] Trace
  normalEmbedding : NormalCore →ₗ[Real] Trace
  valueDense : DenseRange valueEmbedding
  normalDense : DenseRange normalEmbedding
  extension : ValueCore × NormalCore →ₗ[Real] Domain
  boundary_extension : ∀ data,
    boundaryTrace (extension data) =
      canonicalScalarBoundaryCorePairEmbedding
        valueEmbedding normalEmbedding data

namespace CanonicalScalarSmoothCauchyExtensionData

variable {boundaryTrace : Domain →ₗ[Real]
  CanonicalScalarHilbertBoundaryDatum (Trace := Trace)}

/-- The embedded smooth boundary-pair core has dense range. -/
theorem pairEmbedding_denseRange
    (extensionData : CanonicalScalarSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) boundaryTrace) :
    DenseRange
      (canonicalScalarBoundaryCorePairEmbedding
        extensionData.valueEmbedding extensionData.normalEmbedding) :=
  canonicalScalarBoundaryCorePairEmbedding_denseRange
    extensionData.valueEmbedding extensionData.normalEmbedding
    extensionData.valueDense extensionData.normalDense

/-- A smooth Cauchy extension proves density of the smooth bulk boundary trace. -/
theorem boundaryTrace_denseRange
    (extensionData : CanonicalScalarSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) boundaryTrace) :
    DenseRange boundaryTrace := by
  intro boundary
  have hPairClosure := pairEmbedding_denseRange extensionData boundary
  apply closure_mono ?_ hPairClosure
  intro boundaryCore hBoundaryCore
  rcases hBoundaryCore with ⟨data, rfl⟩
  refine ⟨extensionData.extension data, ?_⟩
  exact extensionData.boundary_extension data

/-- Build the corrected smooth Green core once the Cauchy extension is known. -/
def installGreenCore
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
      (ValueCore := ValueCore) (NormalCore := NormalCore) boundaryTrace) :
    CanonicalScalarHilbertGreenCore
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace) where
  inclusion := inclusion
  operator := operator
  boundaryTrace := boundaryTrace
  boundary_dense := boundaryTrace_denseRange extensionData
  green_identity := greenIdentity

/-- Smooth Cauchy-extension certificate. -/
theorem certificate
    (extensionData : CanonicalScalarSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) boundaryTrace) :
    DenseRange boundaryTrace ∧
      (∀ data,
        boundaryTrace (extensionData.extension data) =
          canonicalScalarBoundaryCorePairEmbedding
            extensionData.valueEmbedding extensionData.normalEmbedding data) :=
  ⟨boundaryTrace_denseRange extensionData,
    extensionData.boundary_extension⟩

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

variable
  {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core}

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
  boundary_surjective := boundaryTrace_surjective extensionData
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
  ⟨boundaryTrace_surjective extensionData,
    extensionData.boundary_extension⟩

end CanonicalScalarCompletedCauchyExtensionData

end
end P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
end JanusFormal
