import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetOpenCoverSmoothness4D

/-!
# `L²` membership of explicit Cauchy boundary representatives

The boundary-core structure stores an actual `Lp` embedding and an almost
everywhere identification with its smooth representative.  Hence the smooth
representative automatically satisfies `MemLp`.  This small bridge lets product
Fubini estimates use the representatives directly while retaining the exact
norm of the bundled `Lp` vector.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetBoundaryCoreLp4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetOpenCoverSmoothness4D

universe x y

variable (period : Real)

namespace CanonicalPhysicalScalarCauchyJetBoundaryCoreData

/-- The smooth value representative belongs to boundary `L²`. -/
theorem valueRepresentative_memLp
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (core : CanonicalPhysicalScalarCauchyJetBoundaryCoreData
      period ValueCore NormalCore)
    (value : ValueCore) :
    MemLp (core.valueRepresentative value) (2 : ENNReal)
      (canonicalLatitudeBaseMeasure period) :=
  (Lp.memLp (core.valueEmbedding value)).congr
    (core.valueEmbedding_ae value)

/-- The smooth normal representative belongs to boundary `L²`. -/
theorem normalRepresentative_memLp
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (core : CanonicalPhysicalScalarCauchyJetBoundaryCoreData
      period ValueCore NormalCore)
    (normal : NormalCore) :
    MemLp (core.normalRepresentative normal) (2 : ENNReal)
      (canonicalLatitudeBaseMeasure period) :=
  (Lp.memLp (core.normalEmbedding normal)).congr
    (core.normalEmbedding_ae normal)

/-- Integrability of the squared value representative. -/
theorem valueRepresentative_sq_integrable
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (core : CanonicalPhysicalScalarCauchyJetBoundaryCoreData
      period ValueCore NormalCore)
    (value : ValueCore) :
    Integrable (fun base => core.valueRepresentative value base ^ 2)
      (canonicalLatitudeBaseMeasure period) :=
  (core.valueRepresentative_memLp value).integrable_sq

/-- Integrability of the squared normal representative. -/
theorem normalRepresentative_sq_integrable
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (core : CanonicalPhysicalScalarCauchyJetBoundaryCoreData
      period ValueCore NormalCore)
    (normal : NormalCore) :
    Integrable (fun base => core.normalRepresentative normal base ^ 2)
      (canonicalLatitudeBaseMeasure period) :=
  (core.normalRepresentative_memLp normal).integrable_sq

/-- Boundary representative `L²` certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (core : CanonicalPhysicalScalarCauchyJetBoundaryCoreData
      period ValueCore NormalCore) :
    (∀ value,
      MemLp (core.valueRepresentative value) (2 : ENNReal)
        (canonicalLatitudeBaseMeasure period)) ∧
      (∀ normal,
        MemLp (core.normalRepresentative normal) (2 : ENNReal)
          (canonicalLatitudeBaseMeasure period)) :=
  ⟨core.valueRepresentative_memLp,
    core.normalRepresentative_memLp⟩

end CanonicalPhysicalScalarCauchyJetBoundaryCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetBoundaryCoreLp4D
end JanusFormal
