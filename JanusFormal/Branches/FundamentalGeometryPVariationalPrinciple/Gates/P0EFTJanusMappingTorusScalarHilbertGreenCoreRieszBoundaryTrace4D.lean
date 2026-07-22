import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarBoundaryCauchyGraphExtension4D

/-!
# Reconstructing the completed Cauchy trace by Riesz duality

A separate graph estimate for the normal trace is unnecessary once a bounded
Cauchy extension is available.

Let `E : B → G` be the completed Cauchy extension from the boundary Hilbert pair
`B = Trace × Trace` to the completed maximal graph `G`.  Write `I : G → H` and
`A : G → H` for the ambient and operator coordinates.  The Green defect against
`E b` is represented on `B` by

`R x = (I E)† (A x) - (A E)† (I x)`.

The boundary symplectic form is the Hilbert pairing after the complex structure
`J(u,n)=(-n,u)`.  Hence

`Γ_R x = -J ((1/2) R x)`

is the unique boundary datum satisfying

`2 ω(Γ_R x,b) = <A x,I E b> - <I x,A E b>`.

On the dense smooth boundary core, the original Green identity proves that
`Γ_R` agrees with the smooth Cauchy trace.  Therefore:

* its operator norm gives the missing graph trace bound;
* it is equal to the standard `extendOfNorm` completed trace;
* the completed extension is its right inverse;
* completed trace surjectivity follows automatically.

Thus a bounded graph-valued Cauchy extension can replace an independent normal
trace regularity theorem in the boundary-triple construction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarHilbertGreenCoreRieszBoundaryTrace4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped InnerProduct
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusScalarBoundaryCauchyGraphExtension4D

universe u v w x y z

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  {ValueCore : Type x} {NormalCore : Type y} {BoundaryCore : Type z}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  [AddCommGroup ValueCore] [Module Real ValueCore]
  [AddCommGroup NormalCore] [Module Real NormalCore]
  [AddCommGroup BoundaryCore] [Module Real BoundaryCore]

private abbrev Boundary :=
  CanonicalScalarHilbertBoundaryDatum (Trace := Trace)

/-- Boundary complex structure `J(u,n)=(-n,u)`. -/
def canonicalScalarHilbertBoundaryComplexStructure :
    Boundary (Trace := Trace) →L[Real] Boundary (Trace := Trace) :=
  (-(ContinuousLinearMap.snd Real Trace Trace)).prod
    (ContinuousLinearMap.fst Real Trace Trace)

/-- Inverse complex structure `-J(u,n)=(n,-u)`. -/
def canonicalScalarHilbertBoundaryComplexStructureInv :
    Boundary (Trace := Trace) →L[Real] Boundary (Trace := Trace) :=
  (ContinuousLinearMap.snd Real Trace Trace).prod
    (-(ContinuousLinearMap.fst Real Trace Trace))

@[simp] theorem canonicalScalarHilbertBoundaryComplexStructure_apply
    (boundary : Boundary (Trace := Trace)) :
    canonicalScalarHilbertBoundaryComplexStructure boundary =
      (-boundary.2, boundary.1) :=
  rfl

@[simp] theorem canonicalScalarHilbertBoundaryComplexStructureInv_apply
    (boundary : Boundary (Trace := Trace)) :
    canonicalScalarHilbertBoundaryComplexStructureInv boundary =
      (boundary.2, -boundary.1) :=
  rfl

@[simp] theorem canonicalScalarHilbertBoundaryComplexStructureInv_apply_complexStructure
    (boundary : Boundary (Trace := Trace)) :
    canonicalScalarHilbertBoundaryComplexStructureInv
        (canonicalScalarHilbertBoundaryComplexStructure boundary) = boundary := by
  ext <;> simp

@[simp] theorem canonicalScalarHilbertBoundaryComplexStructure_apply_inv
    (boundary : Boundary (Trace := Trace)) :
    canonicalScalarHilbertBoundaryComplexStructure
        (canonicalScalarHilbertBoundaryComplexStructureInv boundary) = boundary := by
  ext <;> simp

/-- The boundary complex structure is injective. -/
theorem canonicalScalarHilbertBoundaryComplexStructure_injective :
    Function.Injective
      (canonicalScalarHilbertBoundaryComplexStructure
        (Trace := Trace)) := by
  intro first second hEqual
  have hApplied := congrArg
    (canonicalScalarHilbertBoundaryComplexStructureInv (Trace := Trace)) hEqual
  simpa using hApplied

/-- The symplectic form is the Hilbert pairing after `J`. -/
theorem canonicalScalarHilbertBoundarySymplecticForm_eq_inner_complexStructure
    (first second : Boundary (Trace := Trace)) :
    canonicalScalarHilbertBoundarySymplecticForm first second =
      inner Real
        (canonicalScalarHilbertBoundaryComplexStructure first) second := by
  simp [canonicalScalarHilbertBoundarySymplecticForm,
    canonicalScalarHilbertBoundaryComplexStructure,
    real_inner_neg_left, add_comm]

/-- Applying `-J` converts the Hilbert pairing back to the symplectic form. -/
theorem canonicalScalarHilbertBoundarySymplecticForm_complexStructureInv
    (first second : Boundary (Trace := Trace)) :
    canonicalScalarHilbertBoundarySymplecticForm
        (canonicalScalarHilbertBoundaryComplexStructureInv first) second =
      inner Real first second := by
  simp [canonicalScalarHilbertBoundarySymplecticForm,
    canonicalScalarHilbertBoundaryComplexStructureInv,
    real_inner_neg_left, add_comm]

/-- Equality of symplectic pairings on a dense boundary core separates boundary
vectors. -/
theorem canonicalScalarHilbertBoundary_eq_of_symplectic_eq_on_dense
    (embedding : BoundaryCore →ₗ[Real] Boundary (Trace := Trace))
    (hDense : DenseRange embedding)
    (first second : Boundary (Trace := Trace))
    (hPairing : ∀ data,
      canonicalScalarHilbertBoundarySymplecticForm first (embedding data) =
        canonicalScalarHilbertBoundarySymplecticForm second (embedding data)) :
    first = second := by
  let good : Set (Boundary (Trace := Trace)) :=
    {boundary |
      canonicalScalarHilbertBoundarySymplecticForm first boundary =
        canonicalScalarHilbertBoundarySymplecticForm second boundary}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq
    · unfold canonicalScalarHilbertBoundarySymplecticForm
      fun_prop
    · unfold canonicalScalarHilbertBoundarySymplecticForm
      fun_prop
  have hRange : Set.range embedding ⊆ good := by
    rintro boundary ⟨data, rfl⟩
    exact hPairing data
  have hClosure : closure (Set.range embedding) = Set.univ :=
    hDense.closure_range
  have hAll (boundary : Boundary (Trace := Trace)) :
      canonicalScalarHilbertBoundarySymplecticForm first boundary =
        canonicalScalarHilbertBoundarySymplecticForm second boundary := by
    have hBoundary : boundary ∈ closure (Set.range embedding) := by
      rw [hClosure]
      trivial
    exact (closure_minimal hRange hGoodClosed) hBoundary
  let differenceJ : Boundary (Trace := Trace) :=
    canonicalScalarHilbertBoundaryComplexStructure first -
      canonicalScalarHilbertBoundaryComplexStructure second
  have hAt := hAll differenceJ
  have hInner : inner Real differenceJ differenceJ = 0 := by
    dsimp [differenceJ]
    rw [inner_sub_left,
      ← canonicalScalarHilbertBoundarySymplecticForm_eq_inner_complexStructure,
      ← canonicalScalarHilbertBoundarySymplecticForm_eq_inner_complexStructure]
    exact sub_eq_zero.mpr hAt
  have hNormSq : ‖differenceJ‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hInner
  have hDifferenceJ : differenceJ = 0 := by
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖differenceJ‖]
  apply canonicalScalarHilbertBoundaryComplexStructure_injective
  exact sub_eq_zero.mp hDifferenceJ

namespace CanonicalScalarBoundedSmoothCauchyExtensionData

variable {core : CanonicalScalarHilbertGreenCore
  (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}

local instance : CompleteSpace (CanonicalScalarGreenCoreGraphSpace core) :=
  canonicalScalarGreenCoreGraphCompleteSpace core

/-- Ambient inclusion after the completed Cauchy extension. -/
def extensionInclusion
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    Boundary (Trace := Trace) →L[Real] Ambient :=
  (canonicalScalarGreenCoreGraphInclusion core).comp
    extensionData.completedExtension

/-- Operator coordinate after the completed Cauchy extension. -/
def extensionOperator
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    Boundary (Trace := Trace) →L[Real] Ambient :=
  (canonicalScalarGreenCoreGraphOperator core).comp
    extensionData.completedExtension

/-- Riesz representative of the Green defect against the completed extension. -/
def greenRieszMap
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    CanonicalScalarGreenCoreGraphSpace core →L[Real]
      Boundary (Trace := Trace) :=
  ((extensionData.extensionInclusion)†).comp
      (canonicalScalarGreenCoreGraphOperator core) -
    ((extensionData.extensionOperator)†).comp
      (canonicalScalarGreenCoreGraphInclusion core)

/-- Riesz-constructed completed Cauchy trace. -/
def rieszBoundaryTrace
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    CanonicalScalarGreenCoreGraphSpace core →L[Real]
      Boundary (Trace := Trace) :=
  canonicalScalarHilbertBoundaryComplexStructureInv.comp
    ((1 / 2 : Real) • extensionData.greenRieszMap)

/-- Inner-product formula for the Green Riesz representative. -/
theorem greenRieszMap_inner
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (field : CanonicalScalarGreenCoreGraphSpace core)
    (boundary : Boundary (Trace := Trace)) :
    inner Real (extensionData.greenRieszMap field) boundary =
      inner Real (canonicalScalarGreenCoreGraphOperator core field)
          (extensionData.extensionInclusion boundary) -
        inner Real (canonicalScalarGreenCoreGraphInclusion core field)
          (extensionData.extensionOperator boundary) := by
  unfold greenRieszMap
  rw [ContinuousLinearMap.sub_apply, inner_sub_left,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]

/-- The Riesz trace represents the completed Green defect. -/
theorem rieszBoundaryTrace_green_pairing
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (field : CanonicalScalarGreenCoreGraphSpace core)
    (boundary : Boundary (Trace := Trace)) :
    2 * canonicalScalarHilbertBoundarySymplecticForm
        (extensionData.rieszBoundaryTrace field) boundary =
      inner Real (canonicalScalarGreenCoreGraphOperator core field)
          (extensionData.extensionInclusion boundary) -
        inner Real (canonicalScalarGreenCoreGraphInclusion core field)
          (extensionData.extensionOperator boundary) := by
  unfold rieszBoundaryTrace
  rw [canonicalScalarHilbertBoundarySymplecticForm_complexStructureInv]
  rw [real_inner_smul_left, extensionData.greenRieszMap_inner]
  ring

/-- The Riesz trace agrees with the original smooth Cauchy trace. -/
theorem rieszBoundaryTrace_smooth
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (field : Domain) :
    extensionData.rieszBoundaryTrace
        (canonicalScalarGreenCoreToGraph core field) =
      core.boundaryTrace field := by
  apply canonicalScalarHilbertBoundary_eq_of_symplectic_eq_on_dense
    extensionData.boundaryCoreEmbedding
    extensionData.boundaryCoreEmbedding_denseRange
  intro data
  have hRiesz := extensionData.rieszBoundaryTrace_green_pairing
    (canonicalScalarGreenCoreToGraph core field)
    (extensionData.boundaryCoreEmbedding data)
  rw [extensionData.completedExtension_core] at hRiesz
  have hRiesz' :
      2 * canonicalScalarHilbertBoundarySymplecticForm
          (extensionData.rieszBoundaryTrace
            (canonicalScalarGreenCoreToGraph core field))
          (extensionData.boundaryCoreEmbedding data) =
        inner Real (core.operator field)
            (core.inclusion (extensionData.smooth.extension data)) -
          inner Real (core.inclusion field)
            (core.operator (extensionData.smooth.extension data)) := by
    simpa [extensionInclusion, extensionOperator,
      smoothGraphExtension] using hRiesz
  have hGreen := core.green_identity field
    (extensionData.smooth.extension data)
  rw [extensionData.smooth.boundary_extension data] at hGreen
  nlinarith [hRiesz', hGreen]

/-- The operator norm of the Riesz trace supplies the complete smooth graph
trace estimate. -/
def rieszBoundaryGraphBound
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core where
  constant := ‖extensionData.rieszBoundaryTrace‖
  nonnegative := norm_nonneg _
  bound := by
    intro field
    rw [← extensionData.rieszBoundaryTrace_smooth field]
    exact extensionData.rieszBoundaryTrace.le_opNorm _

/-- The standard completed trace generated by the Riesz norm bound is exactly
the Riesz trace. -/
theorem completedBoundaryTrace_eq_rieszBoundaryTrace
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    canonicalScalarGreenCoreCompletedBoundaryTrace core
        extensionData.rieszBoundaryGraphBound =
      extensionData.rieszBoundaryTrace := by
  apply ContinuousLinearMap.ext
  intro field
  let good : Set (CanonicalScalarGreenCoreGraphSpace core) :=
    {candidate |
      canonicalScalarGreenCoreCompletedBoundaryTrace core
          extensionData.rieszBoundaryGraphBound candidate =
        extensionData.rieszBoundaryTrace candidate}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range (canonicalScalarGreenCoreToGraph core) ⊆ good := by
    rintro candidate ⟨smoothField, rfl⟩
    rw [canonicalScalarGreenCoreCompletedBoundaryTrace_smooth,
      extensionData.rieszBoundaryTrace_smooth]
  have hClosure : closure
      (Set.range (canonicalScalarGreenCoreToGraph core)) = Set.univ :=
    (canonicalScalarGreenCoreToGraph_denseRange core).closure_range
  have hField : field ∈ closure
      (Set.range (canonicalScalarGreenCoreToGraph core)) := by
    rw [hClosure]
    trivial
  exact (closure_minimal hRange hGoodClosed) hField

/-- The completed Cauchy extension is a right inverse of the Riesz trace. -/
theorem rieszBoundaryTrace_extension
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (boundary : Boundary (Trace := Trace)) :
    extensionData.rieszBoundaryTrace
        (extensionData.completedExtension boundary) = boundary := by
  rw [← extensionData.completedBoundaryTrace_eq_rieszBoundaryTrace]
  exact extensionData.completedBoundaryTrace_extension
    extensionData.rieszBoundaryGraphBound boundary

/-- The Riesz trace is surjective. -/
theorem rieszBoundaryTrace_surjective
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core) :
    Function.Surjective extensionData.rieszBoundaryTrace := by
  intro boundary
  exact ⟨extensionData.completedExtension boundary,
    extensionData.rieszBoundaryTrace_extension boundary⟩

/-- Install the corrected completed boundary triple without an independent
normal-trace estimate. -/
def toRieszBoundaryTriple
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (hInclusion : Function.Injective
      (canonicalScalarGreenCoreGraphInclusion core)) :
    CanonicalScalarCompletedBoundaryTripleData
      core extensionData.rieszBoundaryGraphBound where
  boundary_surjective := by
    rw [extensionData.completedBoundaryTrace_eq_rieszBoundaryTrace]
    exact extensionData.rieszBoundaryTrace_surjective
  inclusion_injective := hInclusion

/-- Riesz boundary-trace closure certificate. -/
theorem rieszBoundaryTrace_certificate
    (extensionData : CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore) core)
    (hInclusion : Function.Injective
      (canonicalScalarGreenCoreGraphInclusion core)) :
    (∀ field : Domain,
      extensionData.rieszBoundaryTrace
          (canonicalScalarGreenCoreToGraph core field) =
        core.boundaryTrace field) ∧
      Function.Surjective extensionData.rieszBoundaryTrace ∧
      Function.Injective (canonicalScalarGreenCoreGraphInclusion core) ∧
      (∀ boundary : Boundary (Trace := Trace),
        extensionData.rieszBoundaryTrace
          (extensionData.completedExtension boundary) = boundary) :=
  ⟨extensionData.rieszBoundaryTrace_smooth,
    extensionData.rieszBoundaryTrace_surjective,
    hInclusion,
    extensionData.rieszBoundaryTrace_extension⟩

end CanonicalScalarBoundedSmoothCauchyExtensionData

end
end P0EFTJanusMappingTorusScalarHilbertGreenCoreRieszBoundaryTrace4D
end JanusFormal
