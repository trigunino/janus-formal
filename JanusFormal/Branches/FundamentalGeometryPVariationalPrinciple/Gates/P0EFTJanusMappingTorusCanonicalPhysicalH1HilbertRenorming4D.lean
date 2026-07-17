import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1DirichletSpace4D
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Canonical Hilbert renorming of the physical first-jet graph

The existing graph space uses the ordinary product norm on the finite first-jet
fiber.  Replacing both finite products by their `ℓ²` norms gives a genuine
Hilbert fiber.  The canonical finite-dimensional norm equivalences lift to the
spacetime `L²` spaces and identify the closures of the same smooth jets.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D

set_option autoImplicit false

noncomputable section

open scoped ENNReal InnerProductSpace
open MeasureTheory Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev physicalFrame := finiteSmoothTangentFrame period hPeriod
private abbrev physicalMeasure :=
  intrinsicCanonicalLorentzVolumeMeasure period hPeriod

local instance physicalMeasureFinite :
    IsFiniteMeasure (physicalMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

private abbrev GraphJetFiber :=
  Real × (Fin (physicalFrame period hPeriod).count → Real)

/-- The same scalar first-jet fiber with canonical nested finite `ℓ²` norms. -/
abbrev CanonicalPhysicalHilbertJetFiber :=
  WithLp 2
    (Real × PiLp 2
      (fun _ : Fin (physicalFrame period hPeriod).count => Real))

private abbrev GraphJetL2 :=
  Lp (GraphJetFiber period hPeriod) (2 : ENNReal)
    (physicalMeasure period hPeriod)

/-- Hilbert-valued spacetime `L²` containing the renormed first jets. -/
abbrev CanonicalPhysicalHilbertJetL2 :=
  Lp (CanonicalPhysicalHilbertJetFiber period hPeriod) (2 : ENNReal)
    (physicalMeasure period hPeriod)

/-- Canonical finite-dimensional equivalence from the nested `ℓ²` jet fiber
to the ordinary product-norm jet fiber. -/
def canonicalPhysicalHilbertJetFiberToGraph :
    CanonicalPhysicalHilbertJetFiber period hPeriod ≃L[Real]
      GraphJetFiber period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real Real
      (PiLp 2
        (fun _ : Fin (physicalFrame period hPeriod).count => Real))).trans
    ((ContinuousLinearEquiv.refl Real Real).prodCongr
      (PiLp.continuousLinearEquiv 2 Real
        (fun _ : Fin (physicalFrame period hPeriod).count => Real)))

/-- The fiber norm equivalence lifted pointwise to spacetime `L²`. -/
def canonicalPhysicalHilbertJetL2ToGraph :
    CanonicalPhysicalHilbertJetL2 period hPeriod ≃L[Real]
      GraphJetL2 period hPeriod := by
  let fiberEquiv := canonicalPhysicalHilbertJetFiberToGraph period hPeriod
  let forward := fiberEquiv.toContinuousLinearMap.compLpL
    (2 : ENNReal) (physicalMeasure period hPeriod)
  let inverse := fiberEquiv.symm.toContinuousLinearMap.compLpL
    (2 : ENNReal) (physicalMeasure period hPeriod)
  exact ContinuousLinearEquiv.equivOfInverse forward inverse
    (by
      intro field
      apply Lp.ext
      filter_upwards
        [fiberEquiv.symm.toContinuousLinearMap.coeFn_compLpL
          (p := (2 : ENNReal)) (μ := physicalMeasure period hPeriod)
          (forward field),
         fiberEquiv.toContinuousLinearMap.coeFn_compLpL
          (p := (2 : ENNReal)) (μ := physicalMeasure period hPeriod) field]
        with point hInverse hForward
      rw [hInverse, hForward]
      exact fiberEquiv.symm_apply_apply (field point))
    (by
      intro field
      apply Lp.ext
      filter_upwards
        [fiberEquiv.toContinuousLinearMap.coeFn_compLpL
          (p := (2 : ENNReal)) (μ := physicalMeasure period hPeriod)
          (inverse field),
         fiberEquiv.symm.toContinuousLinearMap.coeFn_compLpL
          (p := (2 : ENNReal)) (μ := physicalMeasure period hPeriod) field]
        with point hForward hInverse
      rw [hForward, hInverse]
      exact fiberEquiv.apply_symm_apply (field point))

/-- Smooth first jets transported into the canonical Hilbert jet `L²`. -/
def canonicalPhysicalHilbertFirstJet :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalPhysicalHilbertJetL2 period hPeriod :=
  (canonicalPhysicalHilbertJetL2ToGraph period hPeriod).symm.toLinearMap.comp
    (smoothFirstJetL2LinearMap period hPeriod Real
      (physicalFrame period hPeriod) (physicalMeasure period hPeriod))

theorem canonicalPhysicalHilbertJetL2ToGraph_firstJet
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalHilbertJetL2ToGraph period hPeriod
        (canonicalPhysicalHilbertFirstJet period hPeriod field) =
      smoothFirstJetL2LinearMap period hPeriod Real
        (physicalFrame period hPeriod) (physicalMeasure period hPeriod) field := by
  simp [canonicalPhysicalHilbertFirstJet]

/-- Closure of the smooth first jets inside the canonical Hilbert ambient
`L²`. -/
def canonicalPhysicalHilbertH1Submodule :
    Submodule Real (CanonicalPhysicalHilbertJetL2 period hPeriod) :=
  (LinearMap.range
    (canonicalPhysicalHilbertFirstJet period hPeriod)).topologicalClosure

/-- Canonically Hilbert-renormed physical scalar graph-`H¹`. -/
abbrev CanonicalPhysicalScalarHilbertH1 :=
  canonicalPhysicalHilbertH1Submodule period hPeriod

theorem canonicalPhysicalScalarHilbertH1_isClosed :
    IsClosed
      (CanonicalPhysicalScalarHilbertH1 period hPeriod :
        Set (CanonicalPhysicalHilbertJetL2 period hPeriod)) :=
  Submodule.isClosed_topologicalClosure _

@[implicit_reducible]
def canonicalPhysicalScalarHilbertH1CompleteSpace :
    CompleteSpace (CanonicalPhysicalScalarHilbertH1 period hPeriod) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range (canonicalPhysicalHilbertFirstJet period hPeriod))

/-- The renormed graph completion is a genuine real Hilbert space. -/
@[implicit_reducible]
def canonicalPhysicalScalarHilbertH1HilbertSpace :
    let _ : CompleteSpace (CanonicalPhysicalScalarHilbertH1 period hPeriod) :=
      canonicalPhysicalScalarHilbertH1CompleteSpace period hPeriod
    HilbertSpace Real (CanonicalPhysicalScalarHilbertH1 period hPeriod) := by
  exact @HilbertSpace.mk Real
    (CanonicalPhysicalScalarHilbertH1 period hPeriod)
    inferInstance inferInstance inferInstance
    (canonicalPhysicalScalarHilbertH1CompleteSpace period hPeriod)

/-- The lifted `L²` equivalence maps the Hilbert jet closure exactly onto the
existing product-graph closure. -/
theorem canonicalPhysicalHilbertH1Submodule_map_eq_graph :
    (canonicalPhysicalHilbertH1Submodule period hPeriod).map
        (canonicalPhysicalHilbertJetL2ToGraph period hPeriod).toLinearMap =
      h1GraphSubmodule period hPeriod Real
        (physicalFrame period hPeriod) (physicalMeasure period hPeriod) := by
  apply SetLike.coe_injective
  change
    canonicalPhysicalHilbertJetL2ToGraph period hPeriod ''
        closure
          (LinearMap.range
            (canonicalPhysicalHilbertFirstJet period hPeriod) :
              Set (CanonicalPhysicalHilbertJetL2 period hPeriod)) =
      closure
        (LinearMap.range
          (smoothFirstJetL2LinearMap period hPeriod Real
            (physicalFrame period hPeriod) (physicalMeasure period hPeriod)) :
              Set (GraphJetL2 period hPeriod))
  rw [(canonicalPhysicalHilbertJetL2ToGraph period hPeriod).image_closure]
  congr 1
  ext value
  constructor
  · rintro ⟨hilbertJet, ⟨field, rfl⟩, rfl⟩
    exact ⟨field,
      canonicalPhysicalHilbertJetL2ToGraph_firstJet
        period hPeriod field⟩
  · rintro ⟨field, rfl⟩
    exact ⟨canonicalPhysicalHilbertFirstJet period hPeriod field,
      ⟨field, rfl⟩,
      canonicalPhysicalHilbertJetL2ToGraph_firstJet
        period hPeriod field⟩

/-- Continuous linear equivalence between the canonical Hilbert renorming and
the existing complete physical graph norm. -/
def canonicalPhysicalScalarHilbertH1EquivGraph :
    CanonicalPhysicalScalarHilbertH1 period hPeriod ≃L[Real]
      CanonicalPhysicalScalarH1 period hPeriod :=
  (canonicalPhysicalHilbertJetL2ToGraph period hPeriod).ofSubmodules
    (canonicalPhysicalHilbertH1Submodule period hPeriod)
    (h1GraphSubmodule period hPeriod Real
      (physicalFrame period hPeriod) (physicalMeasure period hPeriod))
    (canonicalPhysicalHilbertH1Submodule_map_eq_graph period hPeriod)

/-- Smooth fields represent the same first jet under the Hilbert renorming
and the original graph completion. -/
theorem canonicalPhysicalScalarHilbertH1EquivGraph_agrees_on_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarHilbertH1EquivGraph period hPeriod
        ⟨canonicalPhysicalHilbertFirstJet period hPeriod field,
          (LinearMap.range
            (canonicalPhysicalHilbertFirstJet period hPeriod)).le_topologicalClosure
              (LinearMap.mem_range_self
                (canonicalPhysicalHilbertFirstJet period hPeriod) field)⟩ =
      smoothToCanonicalPhysicalScalarH1 period hPeriod field := by
  apply Subtype.ext
  exact canonicalPhysicalHilbertJetL2ToGraph_firstJet period hPeriod field

end

end P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
end JanusFormal
