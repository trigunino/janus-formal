import Mathlib.MeasureTheory.Measure.SeparableMeasure
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalBulkDirichletCompactRegulator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLL2SeparableReferenceNuclearRegulator4D

/-!
# Nuclear reference regulator on the global bulk L2 space

The canonical physical bulk measure is separable, hence the finite bulk
`PiLp` Hilbert space is separable.  This instantiates the existing generic
separable-Hilbert reference regulator.  It is not identified with the
physical Hessian or its heat operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalBulkReferenceNuclearRegulator4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalBulkDirichletCompactRegulator4D
open P0EFTJanusProgramPLL2SeparableReferenceNuclearRegulator4D
open P0EFTJanusCircleDiracHeatTraceCancellation

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveBulk :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveBulkIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveBulk period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveBulkCompactSpace :
    CompactSpace (EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveBulkSecondCountable :
    SecondCountableTopology (EffectiveBulk period hPeriod) :=
  (mappingTorusMk_isCoveringMap
      (reflectedSphereData period hPeriod)).isQuotientMap
    (mappingTorusMk_surjective (reflectedSphereData period hPeriod))
  |>.secondCountableTopology
      (mappingTorusMk_isCoveringMap
        (reflectedSphereData period hPeriod)).isOpenMap

local instance effectiveBulkMeasurableSpace :
    MeasurableSpace (EffectiveBulk period hPeriod) := borel _

local instance effectiveBulkBorelSpace :
    BorelSpace (EffectiveBulk period hPeriod) where
  measurable_eq := rfl

local instance lpTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

local instance canonicalBulkMeasureIsFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance canonicalBulkMeasureIsSeparable :
    MeasureTheory.IsSeparable
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  infer_instance

local instance canonicalPhysicalBulkL2SecondCountable :
    SecondCountableTopology
      (CanonicalPhysicalBulkL2 period hPeriod) := by
  infer_instance

local instance globalBulkHilbertL2SecondCountable :
    SecondCountableTopology
      (GlobalBulkHilbertL2 period hPeriod) := by
  infer_instance

/-- Public separability witness for the finite global bulk `L2` Hilbert
space.  Downstream gates can install it with `letI`. -/
@[reducible] def globalBulkHilbertL2SeparableSpace :
    TopologicalSpace.SeparableSpace
      (GlobalBulkHilbertL2 period hPeriod) :=
  TopologicalSpace.SecondCountableTopology.to_separableSpace

local instance globalBulkHilbertL2Separable :
    TopologicalSpace.SeparableSpace
      (GlobalBulkHilbertL2 period hPeriod) :=
  globalBulkHilbertL2SeparableSpace period hPeriod

local instance globalBulkHilbertL2InnerProductSpace :
    InnerProductSpace Real (GlobalBulkHilbertL2 period hPeriod) :=
  PiLp.innerProductSpace fun _ : GlobalBulkSobolevSlot period hPeriod =>
    CanonicalPhysicalBulkL2 period hPeriod

/-- The existing generic separable-Hilbert construction gives an
unconditional compact, injective, nuclear reference regulator on global
bulk `L2`. -/
theorem programP_global_bulk_reference_regulator_gate
    (time : HeatTime) :
    IsCompactOperator
        (referenceOperator
          (H := GlobalBulkHilbertL2 period hPeriod) time) ∧
      Function.Injective
        (referenceOperator
          (H := GlobalBulkHilbertL2 period hPeriod) time) ∧
      Nonempty
        (ReferenceNuclearCertificate
          (H := GlobalBulkHilbertL2 period hPeriod) time) := by
  exact ⟨referenceOperator_isCompact
      (H := GlobalBulkHilbertL2 period hPeriod) time,
    referenceOperator_injective
      (H := GlobalBulkHilbertL2 period hPeriod) time,
    ⟨referenceNuclearCertificate
      (H := GlobalBulkHilbertL2 period hPeriod) time⟩⟩

end
end P0EFTJanusProgramPGlobalBulkReferenceNuclearRegulator4D
end JanusFormal
