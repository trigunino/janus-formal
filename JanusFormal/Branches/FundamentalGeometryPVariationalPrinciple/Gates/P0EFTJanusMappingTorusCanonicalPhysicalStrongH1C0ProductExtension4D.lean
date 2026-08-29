import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Continuous product on the canonical strong `C⁰ ∩ H¹` core

The existing smooth scalar product and its exact Leibniz first jet satisfy a
uniform strong-norm estimate.  Hölder multiplication `L∞ · L² → L²`, the
existing Hilbert/graph jet equivalence, and density then give a canonical
continuous bilinear product on the complete strong core.  No Sobolev
embedding, smoothing axiom, or new physical hypothesis is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0ProductExtension4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMetrizableSpace :
    MetrizableSpace (EffectiveQuotient period hPeriod) :=
  Manifold.metrizableSpace coverModelWithCorners _

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev physicalFrame := finiteSmoothTangentFrame period hPeriod
private abbrev physicalMeasure :=
  intrinsicCanonicalLorentzVolumeMeasure period hPeriod

local instance physicalMeasureFinite :
    IsFiniteMeasure (physicalMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance strongCoreCompleteSpace :
    CompleteSpace
      (CanonicalPhysicalScalarStrongH1C0Core period hPeriod) :=
  canonicalPhysicalScalarStrongH1C0CoreCompleteSpace period hPeriod

local instance strongCoreSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (CanonicalPhysicalScalarStrongH1C0Core period hPeriod) :=
  Submodule.seminormedAddCommGroup
    (canonicalPhysicalScalarStrongH1C0CoreSubmodule period hPeriod)

local instance strongCoreTopologicalSpace :
    TopologicalSpace
      (CanonicalPhysicalScalarStrongH1C0Core period hPeriod) :=
  strongCoreSeminormedAddCommGroup period hPeriod
    |>.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance strongCoreNormedSpace :
    NormedSpace Real
      (CanonicalPhysicalScalarStrongH1C0Core period hPeriod) where
  norm_smul_le scalar field := by
    change ‖scalar • field.1.1‖ ≤ ‖scalar‖ * ‖field.1.1‖
    exact norm_smul_le scalar field.1.1

local instance strongCoreIsBoundedSMul :
    IsBoundedSMul Real
      (CanonicalPhysicalScalarStrongH1C0Core period hPeriod) :=
  { dist_smul_pair' := by
      intro scalar first second
      change dist (scalar • first.1.1) (scalar • second.1.1) ≤
        dist scalar 0 * dist first.1.1 second.1.1
      exact dist_smul_pair scalar first.1.1 second.1.1
    dist_pair_smul' := by
      intro firstScalar secondScalar field
      change dist (firstScalar • field.1.1) (secondScalar • field.1.1) ≤
        dist firstScalar secondScalar * dist field.1.1 0
      exact dist_pair_smul firstScalar secondScalar field.1.1 }

private abbrev StrongCoreEnd :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod →L[Real]
    CanonicalPhysicalScalarStrongH1C0Core period hPeriod

local instance strongCoreEndSeminormedAddCommGroup :
    SeminormedAddCommGroup (StrongCoreEnd period hPeriod) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance strongCoreEndUniformSpace :
    UniformSpace (StrongCoreEnd period hPeriod) :=
  strongCoreEndSeminormedAddCommGroup period hPeriod
    |>.toPseudoMetricSpace.toUniformSpace

local instance strongCoreEndTopologicalSpace :
    TopologicalSpace (StrongCoreEnd period hPeriod) :=
  strongCoreEndUniformSpace period hPeriod |>.toTopologicalSpace

local instance strongCoreEndNormedAddCommGroup :
    NormedAddCommGroup (StrongCoreEnd period hPeriod) :=
  NormedAddCommGroup.ofSeparation fun f : StrongCoreEnd period hPeriod => by
    intro hf
    apply ContinuousLinearMap.ext
    intro field
    change f field = 0
    have hZero : ‖f field‖ = 0 := le_antisymm
      (calc
        ‖f field‖ ≤ ‖f‖ * ‖field‖ := f.le_opNorm field
        _ = 0 := by rw [hf, zero_mul])
      (norm_nonneg _)
    apply @eq_of_dist_eq_zero _
      (canonicalPhysicalScalarStrongH1C0CoreSubmodule
        period hPeriod).normedAddCommGroup.toMetricSpace
    simpa [dist_eq_norm] using hZero

local instance strongCoreEndNormedSpace :
    NormedSpace Real (StrongCoreEnd period hPeriod) :=
  ContinuousLinearMap.toNormedSpace

local instance strongCoreEndCompleteSpace :
    CompleteSpace (StrongCoreEnd period hPeriod) :=
  ContinuousLinearMap.instCompleteSpace

private abbrev GraphDerivativeFiber :=
  Fin (physicalFrame period hPeriod).count → Real

private abbrev GraphJetFiber :=
  Real × GraphDerivativeFiber period hPeriod

private abbrev GraphJetL2 :=
  Lp (GraphJetFiber period hPeriod) (2 : ENNReal)
    (physicalMeasure period hPeriod)

/-- Continuous scalars regarded as essentially bounded fields. -/
def continuousScalarToLInfinity :
    C(EffectiveQuotient period hPeriod, Real) →L[Real]
      Lp Real ⊤ (physicalMeasure period hPeriod) :=
  ContinuousMap.toLp ⊤ (physicalMeasure period hPeriod) Real

/-- Keep only the derivative coordinates of an ordinary graph jet. -/
def graphJetTail :
    GraphJetFiber period hPeriod →L[Real]
      GraphJetFiber period hPeriod :=
  (ContinuousLinearMap.inr Real Real
    (GraphDerivativeFiber period hPeriod)).comp
      (ContinuousLinearMap.snd Real Real
        (GraphDerivativeFiber period hPeriod))

/-- Pointwise derivative-coordinate projection on graph-jet `L²`. -/
def graphJetTailL2 :
    GraphJetL2 period hPeriod →L[Real]
      GraphJetL2 period hPeriod :=
  (graphJetTail period hPeriod).compLpL
    (2 : ENNReal) (physicalMeasure period hPeriod)

theorem smoothFirstJetToL2_mul_decomposition
    (first second : SmoothQuotientField period hPeriod Real) :
    smoothFirstJetToL2 period hPeriod Real
        (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
        (smoothScalarFieldMul period hPeriod first second) =
      continuousScalarToLInfinity period hPeriod
          (smoothToCanonicalPhysicalContinuousScalar
            period hPeriod first) •
        smoothFirstJetToL2 period hPeriod Real
          (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
          second +
      continuousScalarToLInfinity period hPeriod
          (smoothToCanonicalPhysicalContinuousScalar
            period hPeriod second) •
        graphJetTailL2 period hPeriod
          (smoothFirstJetToL2 period hPeriod Real
            (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
            first) := by
  apply Lp.ext
  have hProduct :
      (smoothFirstJetToL2 period hPeriod Real
          (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
          (smoothScalarFieldMul period hPeriod first second) :
        EffectiveQuotient period hPeriod → GraphJetFiber period hPeriod) =ᵐ[
          physicalMeasure period hPeriod]
        smoothFirstJet period hPeriod Real (physicalFrame period hPeriod)
          (smoothScalarFieldMul period hPeriod first second) := by
    simpa only [smoothFirstJetToL2] using
      (smoothFirstJet_memLp period hPeriod Real
        (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
        (smoothScalarFieldMul period hPeriod first second)).coeFn_toLp
  have hFirst :
      (smoothFirstJetToL2 period hPeriod Real
          (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
          first : EffectiveQuotient period hPeriod →
            GraphJetFiber period hPeriod) =ᵐ[physicalMeasure period hPeriod]
        smoothFirstJet period hPeriod Real
          (physicalFrame period hPeriod) first := by
    simpa only [smoothFirstJetToL2] using
      (smoothFirstJet_memLp period hPeriod Real
        (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
        first).coeFn_toLp
  have hSecond :
      (smoothFirstJetToL2 period hPeriod Real
          (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
          second : EffectiveQuotient period hPeriod →
            GraphJetFiber period hPeriod) =ᵐ[physicalMeasure period hPeriod]
        smoothFirstJet period hPeriod Real
          (physicalFrame period hPeriod) second := by
    simpa only [smoothFirstJetToL2] using
      (smoothFirstJet_memLp period hPeriod Real
        (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
        second).coeFn_toLp
  have hFirstInfinity := ContinuousMap.coeFn_toLp
    (p := ⊤) (μ := physicalMeasure period hPeriod) (𝕜 := Real)
    (smoothToCanonicalPhysicalContinuousScalar period hPeriod first)
  have hSecondInfinity := ContinuousMap.coeFn_toLp
    (p := ⊤) (μ := physicalMeasure period hPeriod) (𝕜 := Real)
    (smoothToCanonicalPhysicalContinuousScalar period hPeriod second)
  have hTail := (graphJetTail period hPeriod).coeFn_compLpL
    (p := (2 : ENNReal)) (μ := physicalMeasure period hPeriod)
    (smoothFirstJetToL2 period hPeriod Real
      (physicalFrame period hPeriod) (physicalMeasure period hPeriod) first)
  have hFirstSmul := Lp.coeFn_lpSMul
    (r := (2 : ENNReal))
    (continuousScalarToLInfinity period hPeriod
      (smoothToCanonicalPhysicalContinuousScalar period hPeriod first))
    (smoothFirstJetToL2 period hPeriod Real
      (physicalFrame period hPeriod) (physicalMeasure period hPeriod) second)
  have hSecondSmul := Lp.coeFn_lpSMul
    (r := (2 : ENNReal))
    (continuousScalarToLInfinity period hPeriod
      (smoothToCanonicalPhysicalContinuousScalar period hPeriod second))
    (graphJetTailL2 period hPeriod
      (smoothFirstJetToL2 period hPeriod Real
        (physicalFrame period hPeriod) (physicalMeasure period hPeriod) first))
  have hAdd := Lp.coeFn_add
    (continuousScalarToLInfinity period hPeriod
        (smoothToCanonicalPhysicalContinuousScalar period hPeriod first) •
      smoothFirstJetToL2 period hPeriod Real
        (physicalFrame period hPeriod) (physicalMeasure period hPeriod) second)
    (continuousScalarToLInfinity period hPeriod
        (smoothToCanonicalPhysicalContinuousScalar period hPeriod second) •
      graphJetTailL2 period hPeriod
        (smoothFirstJetToL2 period hPeriod Real
          (physicalFrame period hPeriod) (physicalMeasure period hPeriod) first))
  filter_upwards [hProduct, hFirst, hSecond, hFirstInfinity,
    hSecondInfinity, hTail, hFirstSmul, hSecondSmul, hAdd]
    with point hProduct hFirst hSecond hFirstInfinity hSecondInfinity
      hTail hFirstSmul hSecondSmul hAdd
  rw [hProduct, hAdd]
  simp only [Pi.add_apply]
  rw [hFirstSmul, hSecondSmul]
  change smoothFirstJet period hPeriod Real
      (physicalFrame period hPeriod)
      (smoothScalarFieldMul period hPeriod first second) point =
    continuousScalarToLInfinity period hPeriod
        (smoothToCanonicalPhysicalContinuousScalar period hPeriod first)
        point •
      smoothFirstJetToL2 period hPeriod Real
        (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
        second point +
    continuousScalarToLInfinity period hPeriod
        (smoothToCanonicalPhysicalContinuousScalar period hPeriod second)
        point •
      graphJetTailL2 period hPeriod
        (smoothFirstJetToL2 period hPeriod Real
          (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
          first) point
  simp only [continuousScalarToLInfinity, graphJetTailL2]
  rw [hFirstInfinity, hSecondInfinity, hTail, hFirst, hSecond]
  rw [congrFun (smoothFirstJet_mul period hPeriod
    (physicalFrame period hPeriod) first second) point]
  apply Prod.ext
  · simp [scalarFirstJetMul, graphJetTail,
      smoothToCanonicalPhysicalContinuousScalar, smoothFirstJet]
  · funext index
    simp [scalarFirstJetMul, graphJetTail,
      smoothToCanonicalPhysicalContinuousScalar, smoothFirstJet]

theorem smoothFirstJetToL2_mul_norm_le
    (first second : SmoothQuotientField period hPeriod Real) :
    ‖smoothFirstJetToL2 period hPeriod Real
        (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
        (smoothScalarFieldMul period hPeriod first second)‖ ≤
      ‖continuousScalarToLInfinity period hPeriod
          (smoothToCanonicalPhysicalContinuousScalar period hPeriod first)‖ *
        ‖smoothFirstJetToL2 period hPeriod Real
          (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
          second‖ +
      ‖continuousScalarToLInfinity period hPeriod
          (smoothToCanonicalPhysicalContinuousScalar period hPeriod second)‖ *
        (‖graphJetTailL2 period hPeriod‖ *
          ‖smoothFirstJetToL2 period hPeriod Real
            (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
            first‖) := by
  rw [smoothFirstJetToL2_mul_decomposition period hPeriod first second]
  calc
    _ ≤ ‖continuousScalarToLInfinity period hPeriod
            (smoothToCanonicalPhysicalContinuousScalar period hPeriod first) •
          smoothFirstJetToL2 period hPeriod Real
            (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
            second‖ +
        ‖continuousScalarToLInfinity period hPeriod
            (smoothToCanonicalPhysicalContinuousScalar period hPeriod second) •
          graphJetTailL2 period hPeriod
            (smoothFirstJetToL2 period hPeriod Real
              (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
              first)‖ := norm_add_le _ _
    _ ≤ ‖continuousScalarToLInfinity period hPeriod
            (smoothToCanonicalPhysicalContinuousScalar period hPeriod first)‖ *
          ‖smoothFirstJetToL2 period hPeriod Real
            (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
            second‖ +
        ‖continuousScalarToLInfinity period hPeriod
            (smoothToCanonicalPhysicalContinuousScalar period hPeriod second)‖ *
          ‖graphJetTailL2 period hPeriod
            (smoothFirstJetToL2 period hPeriod Real
              (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
              first)‖ :=
      add_le_add (Lp.norm_smul_le _ _) (Lp.norm_smul_le _ _)
    _ ≤ _ := by
      gcongr
      exact (graphJetTailL2 period hPeriod).le_opNorm _

theorem smoothGraphJet_norm_le_hilbertH1
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothFirstJetToL2 period hPeriod Real
        (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
        field‖ ≤
      ‖(canonicalPhysicalScalarHilbertH1EquivGraph
          period hPeriod).toContinuousLinearMap‖ *
        ‖smoothToCanonicalPhysicalScalarHilbertH1
          period hPeriod field‖ := by
  have hAgreement :
      canonicalPhysicalScalarHilbertH1EquivGraph period hPeriod
          (smoothToCanonicalPhysicalScalarHilbertH1
            period hPeriod field) =
        smoothToCanonicalPhysicalScalarH1 period hPeriod field :=
    canonicalPhysicalScalarHilbertH1EquivGraph_agrees_on_smooth
      period hPeriod field
  calc
    _ = ‖canonicalPhysicalScalarHilbertH1EquivGraph period hPeriod
          (smoothToCanonicalPhysicalScalarHilbertH1
            period hPeriod field)‖ := by rw [hAgreement]; rfl
    _ ≤ _ := (canonicalPhysicalScalarHilbertH1EquivGraph
      period hPeriod).toContinuousLinearMap.le_opNorm _

theorem smoothHilbertH1_norm_le_graphJet
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field‖ ≤
      ‖(canonicalPhysicalScalarHilbertH1EquivGraph
          period hPeriod).symm.toContinuousLinearMap‖ *
        ‖smoothFirstJetToL2 period hPeriod Real
          (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
          field‖ := by
  let hilbertField :=
    smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field
  have hAgreement :
      canonicalPhysicalScalarHilbertH1EquivGraph period hPeriod
          hilbertField =
        smoothToCanonicalPhysicalScalarH1 period hPeriod field :=
    canonicalPhysicalScalarHilbertH1EquivGraph_agrees_on_smooth
      period hPeriod field
  calc
    ‖smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field‖ =
        ‖(canonicalPhysicalScalarHilbertH1EquivGraph
          period hPeriod).symm
            (canonicalPhysicalScalarHilbertH1EquivGraph
              period hPeriod hilbertField)‖ := by
      rw [(canonicalPhysicalScalarHilbertH1EquivGraph
        period hPeriod).symm_apply_apply]
    _ ≤ ‖(canonicalPhysicalScalarHilbertH1EquivGraph
            period hPeriod).symm.toContinuousLinearMap‖ *
          ‖canonicalPhysicalScalarHilbertH1EquivGraph
            period hPeriod hilbertField‖ :=
      (canonicalPhysicalScalarHilbertH1EquivGraph
        period hPeriod).symm.toContinuousLinearMap.le_opNorm _
    _ = _ := by rw [hAgreement]; rfl

theorem smoothContinuous_norm_le_strongCore
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothToCanonicalPhysicalContinuousScalar period hPeriod field‖ ≤
      ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
        period hPeriod field‖ := by
  change
    ‖(smoothToCanonicalPhysicalScalarStrongH1C0Core
        period hPeriod field).1.1.1‖ ≤
      ‖(smoothToCanonicalPhysicalScalarStrongH1C0Core
        period hPeriod field).1.1‖
  exact norm_fst_le _

theorem smoothHilbertH1_norm_le_strongCore
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field‖ ≤
      ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
        period hPeriod field‖ := by
  change
    ‖(smoothToCanonicalPhysicalScalarStrongH1C0Core
        period hPeriod field).1.1.2‖ ≤
      ‖(smoothToCanonicalPhysicalScalarStrongH1C0Core
        period hPeriod field).1.1‖
  exact norm_snd_le _

theorem smoothStrongCore_norm_eq_max
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
        period hPeriod field‖ =
      max
        ‖smoothToCanonicalPhysicalContinuousScalar period hPeriod field‖
        ‖smoothToCanonicalPhysicalScalarHilbertH1
          period hPeriod field‖ :=
  rfl

/-- Explicit uniform coefficient for the smooth `H¹` Leibniz estimate. -/
def smoothHilbertH1ProductBoundConstant : Real :=
  ‖(canonicalPhysicalScalarHilbertH1EquivGraph
      period hPeriod).symm.toContinuousLinearMap‖ *
    ‖continuousScalarToLInfinity period hPeriod‖ *
    ‖(canonicalPhysicalScalarHilbertH1EquivGraph
      period hPeriod).toContinuousLinearMap‖ *
    (1 + ‖graphJetTailL2 period hPeriod‖)

theorem smoothHilbertH1ProductBoundConstant_nonnegative :
    0 ≤ smoothHilbertH1ProductBoundConstant period hPeriod := by
  unfold smoothHilbertH1ProductBoundConstant
  positivity

theorem smoothHilbertH1_mul_norm_le
    (first second : SmoothQuotientField period hPeriod Real) :
    ‖smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod
        (smoothScalarFieldMul period hPeriod first second)‖ ≤
      smoothHilbertH1ProductBoundConstant period hPeriod *
        ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod first‖ *
        ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod second‖ := by
  let firstC :=
    smoothToCanonicalPhysicalContinuousScalar period hPeriod first
  let secondC :=
    smoothToCanonicalPhysicalContinuousScalar period hPeriod second
  let firstH :=
    smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod first
  let secondH :=
    smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod second
  let firstS :=
    smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod first
  let secondS :=
    smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod second
  let firstJet :=
    smoothFirstJetToL2 period hPeriod Real
      (physicalFrame period hPeriod) (physicalMeasure period hPeriod) first
  let secondJet :=
    smoothFirstJetToL2 period hPeriod Real
      (physicalFrame period hPeriod) (physicalMeasure period hPeriod) second
  let productJet :=
    smoothFirstJetToL2 period hPeriod Real
      (physicalFrame period hPeriod) (physicalMeasure period hPeriod)
      (smoothScalarFieldMul period hPeriod first second)
  let A := ‖continuousScalarToLInfinity period hPeriod‖
  let B := ‖(canonicalPhysicalScalarHilbertH1EquivGraph
    period hPeriod).toContinuousLinearMap‖
  let D := ‖(canonicalPhysicalScalarHilbertH1EquivGraph
    period hPeriod).symm.toContinuousLinearMap‖
  let T := ‖graphJetTailL2 period hPeriod‖
  have hFirstInfinity :
      ‖continuousScalarToLInfinity period hPeriod firstC‖ ≤
        A * ‖firstC‖ :=
    (continuousScalarToLInfinity period hPeriod).le_opNorm firstC
  have hSecondInfinity :
      ‖continuousScalarToLInfinity period hPeriod secondC‖ ≤
        A * ‖secondC‖ :=
    (continuousScalarToLInfinity period hPeriod).le_opNorm secondC
  have hFirstJet : ‖firstJet‖ ≤ B * ‖firstH‖ :=
    smoothGraphJet_norm_le_hilbertH1 period hPeriod first
  have hSecondJet : ‖secondJet‖ ≤ B * ‖secondH‖ :=
    smoothGraphJet_norm_le_hilbertH1 period hPeriod second
  have hFirstC : ‖firstC‖ ≤ ‖firstS‖ :=
    smoothContinuous_norm_le_strongCore period hPeriod first
  have hSecondC : ‖secondC‖ ≤ ‖secondS‖ :=
    smoothContinuous_norm_le_strongCore period hPeriod second
  have hFirstH : ‖firstH‖ ≤ ‖firstS‖ :=
    smoothHilbertH1_norm_le_strongCore period hPeriod first
  have hSecondH : ‖secondH‖ ≤ ‖secondS‖ :=
    smoothHilbertH1_norm_le_strongCore period hPeriod second
  calc
    _ ≤ D * ‖productJet‖ :=
      smoothHilbertH1_norm_le_graphJet period hPeriod
        (smoothScalarFieldMul period hPeriod first second)
    _ ≤ D *
        (‖continuousScalarToLInfinity period hPeriod firstC‖ *
            ‖secondJet‖ +
          ‖continuousScalarToLInfinity period hPeriod secondC‖ *
            (T * ‖firstJet‖)) := by
      gcongr
      exact smoothFirstJetToL2_mul_norm_le period hPeriod first second
    _ ≤ D *
        ((A * ‖firstC‖) * (B * ‖secondH‖) +
          (A * ‖secondC‖) * (T * (B * ‖firstH‖))) := by
      gcongr
    _ ≤ D *
        ((A * ‖firstS‖) * (B * ‖secondS‖) +
          (A * ‖secondS‖) * (T * (B * ‖firstS‖))) := by
      gcongr
    _ = smoothHilbertH1ProductBoundConstant period hPeriod *
          ‖firstS‖ * ‖secondS‖ := by
      simp only [smoothHilbertH1ProductBoundConstant]
      dsimp only [A, B, D, T]
      ring

/-- One coefficient controls both the pointwise and first-jet components. -/
def smoothStrongH1C0ProductBoundConstant : Real :=
  1 + smoothHilbertH1ProductBoundConstant period hPeriod

theorem smoothStrongH1C0ProductBoundConstant_nonnegative :
    0 ≤ smoothStrongH1C0ProductBoundConstant period hPeriod := by
  unfold smoothStrongH1C0ProductBoundConstant
  linarith [smoothHilbertH1ProductBoundConstant_nonnegative
    period hPeriod]

theorem smoothStrongH1C0CoreProduct_norm_le
    (first second : SmoothQuotientField period hPeriod Real) :
    ‖smoothStrongH1C0CoreProduct period hPeriod first second‖ ≤
      smoothStrongH1C0ProductBoundConstant period hPeriod *
        ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod first‖ *
        ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod second‖ := by
  let firstC :=
    smoothToCanonicalPhysicalContinuousScalar period hPeriod first
  let secondC :=
    smoothToCanonicalPhysicalContinuousScalar period hPeriod second
  let firstS :=
    smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod first
  let secondS :=
    smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod second
  let H := smoothHilbertH1ProductBoundConstant period hPeriod
  have hH : 0 ≤ H :=
    smoothHilbertH1ProductBoundConstant_nonnegative period hPeriod
  have hFirstC : ‖firstC‖ ≤ ‖firstS‖ :=
    smoothContinuous_norm_le_strongCore period hPeriod first
  have hSecondC : ‖secondC‖ ≤ ‖secondS‖ :=
    smoothContinuous_norm_le_strongCore period hPeriod second
  have hContinuous :
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
          (smoothScalarFieldMul period hPeriod first second) =
        firstC * secondC := by
    apply ContinuousMap.ext
    intro point
    rfl
  have hContinuousBound :
      ‖smoothToCanonicalPhysicalContinuousScalar period hPeriod
          (smoothScalarFieldMul period hPeriod first second)‖ ≤
        smoothStrongH1C0ProductBoundConstant period hPeriod *
          ‖firstS‖ * ‖secondS‖ := by
    rw [hContinuous]
    calc
      ‖firstC * secondC‖ ≤ ‖firstC‖ * ‖secondC‖ := norm_mul_le _ _
      _ ≤ ‖firstS‖ * ‖secondS‖ := by gcongr
      _ ≤ smoothStrongH1C0ProductBoundConstant period hPeriod *
          ‖firstS‖ * ‖secondS‖ := by
        unfold smoothStrongH1C0ProductBoundConstant
        dsimp only [H] at hH
        have hOne : 1 ≤ 1 +
            smoothHilbertH1ProductBoundConstant period hPeriod := by
          linarith
        calc
          ‖firstS‖ * ‖secondS‖ =
              1 * (‖firstS‖ * ‖secondS‖) := by ring
          _ ≤ (1 + smoothHilbertH1ProductBoundConstant period hPeriod) *
              (‖firstS‖ * ‖secondS‖) :=
            mul_le_mul_of_nonneg_right hOne (by positivity)
          _ = _ := by ring
  have hHilbertBound :
      ‖smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod
          (smoothScalarFieldMul period hPeriod first second)‖ ≤
        smoothStrongH1C0ProductBoundConstant period hPeriod *
          ‖firstS‖ * ‖secondS‖ := by
    calc
      _ ≤ H * ‖firstS‖ * ‖secondS‖ :=
        smoothHilbertH1_mul_norm_le period hPeriod first second
      _ ≤ smoothStrongH1C0ProductBoundConstant period hPeriod *
          ‖firstS‖ * ‖secondS‖ := by
        unfold smoothStrongH1C0ProductBoundConstant
        dsimp only [H] at hH ⊢
        have hStep :
            smoothHilbertH1ProductBoundConstant period hPeriod ≤
              1 + smoothHilbertH1ProductBoundConstant period hPeriod := by
          linarith
        calc
          smoothHilbertH1ProductBoundConstant period hPeriod *
                ‖firstS‖ * ‖secondS‖ =
              smoothHilbertH1ProductBoundConstant period hPeriod *
                (‖firstS‖ * ‖secondS‖) := by ring
          _ ≤ (1 + smoothHilbertH1ProductBoundConstant period hPeriod) *
              (‖firstS‖ * ‖secondS‖) :=
            mul_le_mul_of_nonneg_right hStep (by positivity)
          _ = _ := by ring
  rw [smoothStrongCore_norm_eq_max]
  exact max_le hContinuousBound hHilbertBound

theorem smoothStrongH1C0CoreProduct_fixed_norm_bound
    (first : SmoothQuotientField period hPeriod Real) :
    ∃ C : Real, ∀ second : SmoothQuotientField period hPeriod Real,
      ‖smoothStrongH1C0CoreProductBilinear
          period hPeriod first second‖ ≤
        C * ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod second‖ := by
  refine ⟨smoothStrongH1C0ProductBoundConstant period hPeriod *
      ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
        period hPeriod first‖, ?_⟩
  intro second
  simpa only [smoothStrongH1C0CoreProductBilinear_apply,
    smoothStrongH1C0CoreProduct, mul_assoc] using
    smoothStrongH1C0CoreProduct_norm_le period hPeriod first second

/-- Continuous extension in the second argument for one smooth first factor. -/
def smoothStrongH1C0CoreProductRightExtension
    (first : SmoothQuotientField period hPeriod Real) :
    CanonicalPhysicalScalarStrongH1C0Core period hPeriod →L[Real]
      CanonicalPhysicalScalarStrongH1C0Core period hPeriod :=
  LinearMap.extendOfNorm
    (𝕜 := Real) (𝕜₂ := Real) (σ₁₂ := RingHom.id Real)
    (E := SmoothQuotientField period hPeriod Real)
    (Eₗ := CanonicalPhysicalScalarStrongH1C0Core period hPeriod)
    (F := CanonicalPhysicalScalarStrongH1C0Core period hPeriod)
    (smoothStrongH1C0CoreProductBilinear period hPeriod first)
    (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod)

@[simp]
theorem smoothStrongH1C0CoreProductRightExtension_smooth
    (first second : SmoothQuotientField period hPeriod Real) :
    smoothStrongH1C0CoreProductRightExtension period hPeriod first
        (smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod second) =
      smoothStrongH1C0CoreProduct period hPeriod first second := by
  unfold smoothStrongH1C0CoreProductRightExtension
  rw [LinearMap.extendOfNorm_eq
    (smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange
      period hPeriod)
    (smoothStrongH1C0CoreProduct_fixed_norm_bound
      period hPeriod first) second]
  rfl

theorem smoothStrongH1C0CoreProductRightExtension_opNorm_le
    (first : SmoothQuotientField period hPeriod Real) :
    ‖smoothStrongH1C0CoreProductRightExtension
        period hPeriod first‖ ≤
      smoothStrongH1C0ProductBoundConstant period hPeriod *
        ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod first‖ := by
  let C := smoothStrongH1C0ProductBoundConstant period hPeriod *
    ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
      period hPeriod first‖
  have hC : 0 ≤ C :=
    mul_nonneg
      (smoothStrongH1C0ProductBoundConstant_nonnegative
        period hPeriod)
      (norm_nonneg _)
  have hNorm : ∀ second : SmoothQuotientField period hPeriod Real,
      ‖smoothStrongH1C0CoreProductBilinear
          period hPeriod first second‖ ≤
        C * ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod second‖ := by
    intro second
    simpa only [C, smoothStrongH1C0CoreProductBilinear_apply,
      smoothStrongH1C0CoreProduct, mul_assoc] using
      smoothStrongH1C0CoreProduct_norm_le period hPeriod first second
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro field
  change ‖LinearMap.extendOfNorm
      (𝕜 := Real) (𝕜₂ := Real) (σ₁₂ := RingHom.id Real)
      (E := SmoothQuotientField period hPeriod Real)
      (Eₗ := CanonicalPhysicalScalarStrongH1C0Core period hPeriod)
      (F := CanonicalPhysicalScalarStrongH1C0Core period hPeriod)
      (smoothStrongH1C0CoreProductBilinear period hPeriod first)
      (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod)
      field‖ ≤ C * ‖field‖
  exact LinearMap.norm_extendOfNorm_apply_le
    (smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange
      period hPeriod) C hNorm field

/-- The one-sided extensions depend linearly on their smooth first factor. -/
def smoothStrongH1C0CoreProductLeftLinear :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      (CanonicalPhysicalScalarStrongH1C0Core period hPeriod →L[Real]
        CanonicalPhysicalScalarStrongH1C0Core period hPeriod) where
  toFun := smoothStrongH1C0CoreProductRightExtension period hPeriod
  map_add' first second := by
    apply ContinuousLinearMap.ext
    intro field
    refine DenseRange.induction_on
      (smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange
        period hPeriod) field
      (isClosed_eq
        (smoothStrongH1C0CoreProductRightExtension
          period hPeriod (first + second)).continuous
        ((smoothStrongH1C0CoreProductRightExtension period hPeriod first +
          smoothStrongH1C0CoreProductRightExtension
            period hPeriod second).continuous)) ?_
    intro smooth
    simp only [add_apply,
      smoothStrongH1C0CoreProductRightExtension_smooth]
    have hAdd := congrArg
      (fun linear => linear smooth)
      ((smoothStrongH1C0CoreProductBilinear
        period hPeriod).map_add first second)
    simpa only [LinearMap.add_apply,
      smoothStrongH1C0CoreProductBilinear_apply,
      smoothStrongH1C0CoreProduct] using hAdd
  map_smul' scalar first := by
    apply ContinuousLinearMap.ext
    intro field
    refine DenseRange.induction_on
      (smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange
        period hPeriod) field
      (isClosed_eq
        (smoothStrongH1C0CoreProductRightExtension
          period hPeriod (scalar • first)).continuous
        ((scalar • smoothStrongH1C0CoreProductRightExtension
          period hPeriod first).continuous)) ?_
    intro smooth
    simp only [smul_apply,
      smoothStrongH1C0CoreProductRightExtension_smooth]
    have hSmul := congrArg
      (fun linear => linear smooth)
      ((smoothStrongH1C0CoreProductBilinear
        period hPeriod).map_smul scalar first)
    simpa only [LinearMap.smul_apply,
      smoothStrongH1C0CoreProductBilinear_apply,
      smoothStrongH1C0CoreProduct, RingHom.id_apply] using hSmul

theorem smoothStrongH1C0CoreProductLeftLinear_norm_bound :
    ∃ C : Real, ∀ first : SmoothQuotientField period hPeriod Real,
      ‖smoothStrongH1C0CoreProductLeftLinear period hPeriod first‖ ≤
        C * ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod first‖ := by
  refine ⟨smoothStrongH1C0ProductBoundConstant period hPeriod, ?_⟩
  intro first
  exact smoothStrongH1C0CoreProductRightExtension_opNorm_le
    period hPeriod first

/-- Canonical continuous bilinear multiplication on the complete strong core. -/
def canonicalPhysicalScalarStrongH1C0CoreProduct :
    CanonicalPhysicalScalarStrongH1C0Core period hPeriod →L[Real]
      (CanonicalPhysicalScalarStrongH1C0Core period hPeriod →L[Real]
        CanonicalPhysicalScalarStrongH1C0Core period hPeriod) :=
  LinearMap.extendOfNorm
    (𝕜 := Real) (𝕜₂ := Real) (σ₁₂ := RingHom.id Real)
    (E := SmoothQuotientField period hPeriod Real)
    (Eₗ := CanonicalPhysicalScalarStrongH1C0Core period hPeriod)
    (F := CanonicalPhysicalScalarStrongH1C0Core period hPeriod →L[Real]
      CanonicalPhysicalScalarStrongH1C0Core period hPeriod)
    (smoothStrongH1C0CoreProductLeftLinear period hPeriod)
    (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod)

@[simp]
theorem canonicalPhysicalScalarStrongH1C0CoreProduct_smooth_left
    (first : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarStrongH1C0CoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod first) =
      smoothStrongH1C0CoreProductRightExtension
        period hPeriod first := by
  unfold canonicalPhysicalScalarStrongH1C0CoreProduct
  rw [LinearMap.extendOfNorm_eq
    (smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange
      period hPeriod)
    (smoothStrongH1C0CoreProductLeftLinear_norm_bound
      period hPeriod) first]
  rfl

@[simp]
theorem canonicalPhysicalScalarStrongH1C0CoreProduct_smooth
    (first second : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarStrongH1C0CoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod first)
        (smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod second) =
      smoothStrongH1C0CoreProduct period hPeriod first second := by
  rw [canonicalPhysicalScalarStrongH1C0CoreProduct_smooth_left,
    smoothStrongH1C0CoreProductRightExtension_smooth]

theorem canonicalPhysicalScalarStrongH1C0CoreProduct_opNorm_le :
    ‖canonicalPhysicalScalarStrongH1C0CoreProduct period hPeriod‖ ≤
      smoothStrongH1C0ProductBoundConstant period hPeriod := by
  let K := smoothStrongH1C0ProductBoundConstant period hPeriod
  have hK : 0 ≤ K :=
    smoothStrongH1C0ProductBoundConstant_nonnegative period hPeriod
  have hNorm : ∀ first : SmoothQuotientField period hPeriod Real,
      ‖smoothStrongH1C0CoreProductLeftLinear period hPeriod first‖ ≤
        K * ‖smoothToCanonicalPhysicalScalarStrongH1C0Core
          period hPeriod first‖ := by
    intro first
    exact smoothStrongH1C0CoreProductRightExtension_opNorm_le
      period hPeriod first
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro field
  change ‖LinearMap.extendOfNorm
      (𝕜 := Real) (𝕜₂ := Real) (σ₁₂ := RingHom.id Real)
      (E := SmoothQuotientField period hPeriod Real)
      (Eₗ := CanonicalPhysicalScalarStrongH1C0Core period hPeriod)
      (F := StrongCoreEnd period hPeriod)
      (smoothStrongH1C0CoreProductLeftLinear period hPeriod)
      (smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod)
      field‖ ≤ K * ‖field‖
  exact LinearMap.norm_extendOfNorm_apply_le
    (smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange
      period hPeriod) K hNorm field

theorem canonicalPhysicalScalarStrongH1C0CoreProduct_norm_le
    (first second : CanonicalPhysicalScalarStrongH1C0Core
      period hPeriod) :
    ‖canonicalPhysicalScalarStrongH1C0CoreProduct
        period hPeriod first second‖ ≤
      smoothStrongH1C0ProductBoundConstant period hPeriod *
        ‖first‖ * ‖second‖ := by
  calc
    _ ≤ ‖canonicalPhysicalScalarStrongH1C0CoreProduct
          period hPeriod first‖ * ‖second‖ :=
      (canonicalPhysicalScalarStrongH1C0CoreProduct
        period hPeriod first).le_opNorm second
    _ ≤ (‖canonicalPhysicalScalarStrongH1C0CoreProduct
            period hPeriod‖ * ‖first‖) * ‖second‖ := by
      gcongr
      exact (canonicalPhysicalScalarStrongH1C0CoreProduct
        period hPeriod).le_opNorm first
    _ ≤ (smoothStrongH1C0ProductBoundConstant period hPeriod *
            ‖first‖) * ‖second‖ := by
      gcongr
      exact canonicalPhysicalScalarStrongH1C0CoreProduct_opNorm_le
        period hPeriod
    _ = _ := by ring

/-- Summary gate: smooth multiplication has a uniform strong estimate and a
canonical continuous bilinear extension to the complete dense core. -/
theorem canonical_physical_strong_h1_c0_product_extension_gate :
    0 ≤ smoothStrongH1C0ProductBoundConstant period hPeriod ∧
      ‖canonicalPhysicalScalarStrongH1C0CoreProduct period hPeriod‖ ≤
        smoothStrongH1C0ProductBoundConstant period hPeriod ∧
      (∀ first second : SmoothQuotientField period hPeriod Real,
        canonicalPhysicalScalarStrongH1C0CoreProduct period hPeriod
            (smoothToCanonicalPhysicalScalarStrongH1C0Core
              period hPeriod first)
            (smoothToCanonicalPhysicalScalarStrongH1C0Core
              period hPeriod second) =
          smoothStrongH1C0CoreProduct period hPeriod first second) := by
  exact ⟨smoothStrongH1C0ProductBoundConstant_nonnegative
      period hPeriod,
    canonicalPhysicalScalarStrongH1C0CoreProduct_opNorm_le
      period hPeriod,
    canonicalPhysicalScalarStrongH1C0CoreProduct_smooth
      period hPeriod⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0ProductExtension4D
end JanusFormal
