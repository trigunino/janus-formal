import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D

/-!
# Global paired Abelian Lorenz graph Hessian

The genuine supplied-metric Lorenz operator is completed with its physical
`L²` potential coordinates.  Projection onto the Lorenz graph feature gives a
bounded Riesz operator.  On the injective dense smooth core its pairing is
exactly the reduced, on-shell polarization of the unchanged global BRST
gauge-fixing action.

No Green identity, adjoint formula for `δ_g`, Fredholm claim, or new analytic
hypothesis is used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-! ## Faithful paired graph core -/

abbrev GlobalPairedAbelianPotentialSmooth :=
  Sector → SmoothAbelianGaugePotential period hPeriod

abbrev GlobalPairedAbelianPotentialCoordinateIndex :=
  Sector × Fin 2 ×
    Fin (finiteSmoothTangentFrame period hPeriod).count

abbrev GlobalPairedAbelianLorenzCoordinateIndex :=
  Sector × Fin 2

abbrev GlobalPairedAbelianPotentialL2 :=
  PiLp 2
    (fun _ : GlobalPairedAbelianPotentialCoordinateIndex period hPeriod =>
      CanonicalPhysicalBulkL2 period hPeriod)

abbrev GlobalPairedAbelianLorenzL2 :=
  PiLp 2
    (fun _ : GlobalPairedAbelianLorenzCoordinateIndex =>
      CanonicalPhysicalBulkL2 period hPeriod)

abbrev GlobalPairedAbelianLorenzGraphAmbient :=
  WithLp 2
    (GlobalPairedAbelianPotentialL2 period hPeriod ×
      GlobalPairedAbelianLorenzL2 period hPeriod)

local instance globalPairedAbelianPotentialL2NormedSpace :
    NormedSpace Real (GlobalPairedAbelianPotentialL2 period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianPotentialL2 period hPeriod)).toNormedSpace

local instance globalPairedAbelianPotentialL2Module :
    Module Real (GlobalPairedAbelianPotentialL2 period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianPotentialL2 period hPeriod)).toNormedSpace.toModule

local instance globalPairedAbelianLorenzL2NormedSpace :
    NormedSpace Real (GlobalPairedAbelianLorenzL2 period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianLorenzL2 period hPeriod)).toNormedSpace

local instance globalPairedAbelianLorenzL2Module :
    Module Real (GlobalPairedAbelianLorenzL2 period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianLorenzL2 period hPeriod)).toNormedSpace.toModule

local instance globalPairedAbelianLorenzGraphAmbientNormedSpace :
    NormedSpace Real
      (GlobalPairedAbelianLorenzGraphAmbient period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)).toNormedSpace

local instance globalPairedAbelianLorenzGraphAmbientModule :
    Module Real (GlobalPairedAbelianLorenzGraphAmbient period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)
    ).toNormedSpace.toModule

theorem ghostComponent_smul
    (scalar : Real)
    (field : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) :
    ghostComponent period hPeriod (scalar • field) component =
      scalar • ghostComponent period hPeriod field component := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

/-- Componentwise physical `L²` coordinates of a smooth gauge-Lie field. -/
def globalGaugeLieFieldL2Coordinates :
    SmoothQuotientField period hPeriod GaugeLieAlgebra →ₗ[Real]
      (Fin 2 → CanonicalPhysicalBulkL2 period hPeriod) where
  toFun := fun field component =>
    smoothToCanonicalPhysicalBulkL2 period hPeriod
      (ghostComponent period hPeriod field component)
  map_add' first second := by
    funext component
    rw [ghostComponent_add]
    exact (smoothToCanonicalPhysicalBulkL2 period hPeriod).map_add _ _
  map_smul' scalar field := by
    funext component
    rw [ghostComponent_smul]
    exact (smoothToCanonicalPhysicalBulkL2 period hPeriod).map_smul _ _

/-- Paired physical potential coordinates. -/
def globalPairedAbelianPotentialL2LinearMap :
    GlobalPairedAbelianPotentialSmooth period hPeriod →ₗ[Real]
      GlobalPairedAbelianPotentialL2 period hPeriod where
  toFun := fun potential =>
    WithLp.toLp 2 fun index =>
      gaugePotentialL2Coordinates period hPeriod (potential index.1)
        index.2.1 index.2.2
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact congrArg
      (fun value => value index.2.1 index.2.2)
      ((gaugePotentialL2Coordinates period hPeriod).map_add
        (first index.1) (second index.1))
  map_smul' scalar potential := by
    apply PiLp.ext
    intro index
    exact congrArg
      (fun value => value index.2.1 index.2.2)
      ((gaugePotentialL2Coordinates period hPeriod).map_smul
        scalar (potential index.1))

/-- Paired supplied-metric Lorenz features in physical `L²`. -/
def globalPairedAbelianLorenzL2LinearMap
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianPotentialSmooth period hPeriod →ₗ[Real]
      GlobalPairedAbelianLorenzL2 period hPeriod where
  toFun := fun potential =>
    WithLp.toLp 2 fun index =>
      globalGaugeLieFieldL2Coordinates period hPeriod
        (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
          (metric index.1) (potential index.1)) index.2
  map_add' first second := by
    apply PiLp.ext
    intro index
    change
      globalGaugeLieFieldL2Coordinates period hPeriod
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric index.1) (first index.1 + second index.1)) index.2 =
        globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
              (metric index.1) (first index.1)) index.2 +
          globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
              (metric index.1) (second index.1)) index.2
    rw [globalGeneralMetricAbelianLorenzCodifferential_add]
    exact congrArg (fun value => value index.2)
      ((globalGaugeLieFieldL2Coordinates period hPeriod).map_add _ _)
  map_smul' scalar potential := by
    apply PiLp.ext
    intro index
    change
      globalGaugeLieFieldL2Coordinates period hPeriod
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric index.1) (scalar • potential index.1)) index.2 =
        scalar •
          globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
              (metric index.1) (potential index.1)) index.2
    rw [globalGeneralMetricAbelianLorenzCodifferential_smul]
    exact congrArg (fun value => value index.2)
      ((globalGaugeLieFieldL2Coordinates period hPeriod).map_smul _ _)

/-- Raw potential values together with the true Lorenz feature. -/
def globalPairedAbelianLorenzGraphAmbientLinearMap
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianPotentialSmooth period hPeriod →ₗ[Real]
      GlobalPairedAbelianLorenzGraphAmbient period hPeriod where
  toFun := fun potential =>
    WithLp.toLp 2
      (globalPairedAbelianPotentialL2LinearMap period hPeriod potential,
        globalPairedAbelianLorenzL2LinearMap period hPeriod metric potential)
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    change
      ((globalPairedAbelianPotentialL2LinearMap period hPeriod)
          (first + second),
        (globalPairedAbelianLorenzL2LinearMap period hPeriod metric)
          (first + second)) = _
    rw [(globalPairedAbelianPotentialL2LinearMap period hPeriod).map_add,
      (globalPairedAbelianLorenzL2LinearMap period hPeriod metric).map_add]
    rfl
  map_smul' scalar potential := by
    apply WithLp.ofLp_injective 2
    change
      ((globalPairedAbelianPotentialL2LinearMap period hPeriod)
          (scalar • potential),
        (globalPairedAbelianLorenzL2LinearMap period hPeriod metric)
          (scalar • potential)) = _
    rw [(globalPairedAbelianPotentialL2LinearMap period hPeriod).map_smul,
      (globalPairedAbelianLorenzL2LinearMap period hPeriod metric).map_smul]
    rfl

/-- Closed Hilbert graph generated by genuine smooth paired potentials. -/
def globalPairedAbelianLorenzGraphSubmodule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real
      (GlobalPairedAbelianLorenzGraphAmbient period hPeriod) :=
  (LinearMap.range
    (globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric)
    ).topologicalClosure

abbrev GlobalPairedAbelianLorenzGraphHilbert
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :=
  globalPairedAbelianLorenzGraphSubmodule period hPeriod metric

local instance globalPairedAbelianLorenzGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric)
    ).toNormedSpace

local instance globalPairedAbelianLorenzGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric)
    ).toNormedSpace.toModule

/-- Canonical smooth-core inclusion into the Lorenz graph completion. -/
def globalPairedAbelianLorenzSmoothEmbedding
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianPotentialSmooth period hPeriod →ₗ[Real]
      GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric where
  toFun potential :=
    ⟨globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric
        potential,
      (LinearMap.range
        (globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric)
        ).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric)
          potential)⟩
  map_add' first second := Subtype.ext
    ((globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric).map_add
      first second)
  map_smul' scalar potential := Subtype.ext
    ((globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric).map_smul
      scalar potential)

theorem globalPairedAbelianLorenzSmoothEmbedding_denseRange
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (globalPairedAbelianLorenzSmoothEmbedding period hPeriod metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  unfold GlobalPairedAbelianLorenzGraphHilbert
    globalPairedAbelianLorenzGraphSubmodule
  let graph :=
    globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric
  have hRange :
      Subtype.val '' Set.range
          (globalPairedAbelianLorenzSmoothEmbedding period hPeriod metric) =
        (LinearMap.range graph :
          Set (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨potential, rfl⟩, rfl⟩
      exact ⟨potential, rfl⟩
    · rintro ⟨potential, rfl⟩
      exact
        ⟨globalPairedAbelianLorenzSmoothEmbedding period hPeriod metric
            potential,
          ⟨potential, rfl⟩, rfl⟩
  change closure
      (LinearMap.range graph :
        Set (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)) ⊆
    closure (Subtype.val '' Set.range
      (globalPairedAbelianLorenzSmoothEmbedding period hPeriod metric))
  rw [hRange]

theorem globalPairedAbelianLorenzSmoothEmbedding_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalPairedAbelianLorenzSmoothEmbedding period hPeriod metric) := by
  intro first second hEqual
  have hAmbient := congrArg Subtype.val hEqual
  have hPotential :
      globalPairedAbelianPotentialL2LinearMap period hPeriod first =
        globalPairedAbelianPotentialL2LinearMap period hPeriod second :=
    congrArg WithLp.fst hAmbient
  funext sector
  apply gaugePotentialL2Coordinates_injective period hPeriod
  funext component index
  exact congrArg
    (fun value => value (sector, component, index)) hPotential

@[implicit_reducible]
def globalPairedAbelianLorenzGraphCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) := by
  unfold GlobalPairedAbelianLorenzGraphHilbert
    globalPairedAbelianLorenzGraphSubmodule
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric))

/-! ## Bounded graph representative and same-action identification -/

/-- Continuous projection onto the genuine Lorenz feature. -/
def globalPairedAbelianLorenzFeatureProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianLorenzL2 period hPeriod :=
  (WithLp.sndL 2 Real
      (GlobalPairedAbelianPotentialL2 period hPeriod)
      (GlobalPairedAbelianLorenzL2 period hPeriod)).comp
    (globalPairedAbelianLorenzGraphSubmodule period hPeriod metric).subtypeL

@[simp]
theorem globalPairedAbelianLorenzFeatureProjection_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (potential : GlobalPairedAbelianPotentialSmooth period hPeriod) :
    globalPairedAbelianLorenzFeatureProjection period hPeriod metric
        (globalPairedAbelianLorenzSmoothEmbedding period hPeriod metric
          potential) =
      globalPairedAbelianLorenzL2LinearMap period hPeriod metric potential :=
  rfl

/-- Bounded nonnegative Riesz representative `P†P` of the Lorenz graph form. -/
def globalPairedAbelianLorenzGraphRieszOperator
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric := by
  letI : CompleteSpace
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :=
    globalPairedAbelianLorenzGraphCompleteSpace period hPeriod metric
  exact
    (globalPairedAbelianLorenzFeatureProjection period hPeriod metric).adjoint.comp
      (globalPairedAbelianLorenzFeatureProjection period hPeriod metric)

theorem globalPairedAbelianLorenzGraphRieszOperator_pairing
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :
    inner Real
        (globalPairedAbelianLorenzGraphRieszOperator period hPeriod metric first)
        second =
      inner Real
        (globalPairedAbelianLorenzFeatureProjection period hPeriod metric first)
        (globalPairedAbelianLorenzFeatureProjection period hPeriod metric
          second) := by
  letI : CompleteSpace
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :=
    globalPairedAbelianLorenzGraphCompleteSpace period hPeriod metric
  change inner Real
      ((globalPairedAbelianLorenzFeatureProjection period hPeriod metric).adjoint
        (globalPairedAbelianLorenzFeatureProjection period hPeriod metric first))
      second = _
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

theorem globalPairedAbelianLorenzGraphRieszOperator_ker_eq
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    LinearMap.ker
        (globalPairedAbelianLorenzGraphRieszOperator period hPeriod
          metric).toLinearMap =
      LinearMap.ker
        (globalPairedAbelianLorenzFeatureProjection period hPeriod
          metric).toLinearMap := by
  ext direction
  simp only [LinearMap.mem_ker]
  constructor
  · intro hRiesz
    letI : CompleteSpace
        (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :=
      globalPairedAbelianLorenzGraphCompleteSpace period hPeriod metric
    change
      (globalPairedAbelianLorenzFeatureProjection period hPeriod metric).adjoint
        (globalPairedAbelianLorenzFeatureProjection period hPeriod metric
          direction) = 0 at hRiesz
    have hPairing :=
      ContinuousLinearMap.adjoint_inner_left
        (globalPairedAbelianLorenzFeatureProjection period hPeriod metric)
        direction
        (globalPairedAbelianLorenzFeatureProjection period hPeriod metric
          direction)
    rw [hRiesz, inner_zero_left] at hPairing
    exact inner_self_eq_zero.mp hPairing.symm
  · intro hProjection
    letI : CompleteSpace
        (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :=
      globalPairedAbelianLorenzGraphCompleteSpace period hPeriod metric
    change
      (globalPairedAbelianLorenzFeatureProjection period hPeriod metric).adjoint
        (globalPairedAbelianLorenzFeatureProjection period hPeriod metric
          direction) = 0
    have hZero :
        globalPairedAbelianLorenzFeatureProjection period hPeriod metric
            direction =
          (0 : GlobalPairedAbelianLorenzL2 period hPeriod) :=
      hProjection
    rw [hZero]
    exact map_zero _

theorem globalPairedAbelianLorenzGraphRieszOperator_symmetric
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric) :
    inner Real
        (globalPairedAbelianLorenzGraphRieszOperator period hPeriod metric first)
        second =
      inner Real first
        (globalPairedAbelianLorenzGraphRieszOperator period hPeriod metric
          second) := by
  calc
    _ = inner Real
          (globalPairedAbelianLorenzFeatureProjection period hPeriod metric
            first)
          (globalPairedAbelianLorenzFeatureProjection period hPeriod metric
            second) :=
      globalPairedAbelianLorenzGraphRieszOperator_pairing
        period hPeriod metric first second
    _ = inner Real
          (globalPairedAbelianLorenzFeatureProjection period hPeriod metric
            second)
          (globalPairedAbelianLorenzFeatureProjection period hPeriod metric
            first) :=
      real_inner_comm _ _
    _ = inner Real
          (globalPairedAbelianLorenzGraphRieszOperator period hPeriod metric
            second)
          first :=
      (globalPairedAbelianLorenzGraphRieszOperator_pairing
        period hPeriod metric second first).symm
    _ = _ := real_inner_comm _ _

/-- Put the auxiliary field on its exact algebraic shell `B = δ_g A`. -/
def globalPairedAbelianLorenzOnShellState
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (potential : GlobalPairedAbelianPotentialSmooth period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod where
  potential := potential
  nonminimal := fun sector =>
    { ghost := zeroGlobalAbelianGhostField period hPeriod
      antighost := zeroGlobalAbelianAntighostField period hPeriod
      nakanishiLautrup :=
        ⟨globalGeneralMetricAbelianLorenzCodifferential period hPeriod
          (metric sector) (potential sector)⟩ }

theorem globalPairedAbelianLorenzOnShellPolarizationDensity
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianPotentialSmooth period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTPolarizationDensity period hPeriod metric
        (globalPairedAbelianLorenzOnShellState period hPeriod metric first)
        (globalPairedAbelianLorenzOnShellState period hPeriod metric second)
        point =
      ∑ sector : Sector,
        globalGaugeLiePairingAt period hPeriod
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (first sector))
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (second sector)) point := by
  unfold globalPairedAbelianGaugeFermionBRSTPolarizationDensity
    globalPairedAbelianGaugeFermionBRSTMixedDensity
    globalPairedAbelianLorenzOnShellState
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sector _
  simp only [zeroGlobalAbelianGhostField, zeroGlobalAbelianAntighostField]
  unfold globalGaugeLiePairingAt
  have hZeroComponent (component : Fin 2) :
      (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra)
          point component = 0 :=
    rfl
  simp_rw [hZeroComponent]
  simp only [Finset.sum_const_zero, zero_mul, add_zero]
  have hPairComm :
      (∑ component : Fin 2,
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (second sector)) point component *
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (first sector)) point component) =
        ∑ component : Fin 2,
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (first sector)) point component *
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (second sector)) point component := by
    apply Finset.sum_congr rfl
    intro component _
    exact mul_comm _ _
  rw [hPairComm]
  ring

theorem globalGaugeLiePairingAt_integrable
    (first second :
      SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    Integrable
      (globalGaugeLiePairingAt period hPeriod first second)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (globalGaugeLiePairingAt_continuous period hPeriod first second
    ).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      |>.integrable one_le_two

theorem globalGaugeLieComponentProduct_integrable
    (first second :
      SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) :
    Integrable
      (fun point : EffectiveQuotient period hPeriod =>
        first point component * second point component)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (((ghostComponent period hPeriod first component).contMDiff_toFun.continuous
    ).mul
      ((ghostComponent period hPeriod second component
        ).contMDiff_toFun.continuous)
    ).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      |>.integrable one_le_two

/-- The Lorenz feature inner product is the exact reduced BRST polarization. -/
theorem globalPairedAbelianLorenzFeature_inner_eq_BRST
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianPotentialSmooth period hPeriod) :
    inner Real
        (globalPairedAbelianLorenzL2LinearMap period hPeriod metric first)
        (globalPairedAbelianLorenzL2LinearMap period hPeriod metric second) =
        globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric
        (globalPairedAbelianLorenzOnShellState period hPeriod metric first)
        (globalPairedAbelianLorenzOnShellState period hPeriod metric second)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold globalPairedAbelianGaugeFermionBRSTPolarizationAction
  rw [show
      (∫ point,
          globalPairedAbelianGaugeFermionBRSTPolarizationDensity period hPeriod
            metric
            (globalPairedAbelianLorenzOnShellState period hPeriod metric first)
            (globalPairedAbelianLorenzOnShellState period hPeriod metric second)
            point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
        ∫ point, ∑ sector : Sector,
          globalGaugeLiePairingAt period hPeriod
            (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
              (metric sector) (first sector))
            (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
              (metric sector) (second sector)) point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun point =>
        globalPairedAbelianLorenzOnShellPolarizationDensity period hPeriod
          metric first second point]
  rw [integral_finsetSum Finset.univ (fun sector _ =>
    globalGaugeLiePairingAt_integrable period hPeriod
      (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
        (metric sector) (first sector))
      (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
        (metric sector) (second sector)))]
  simp only [PiLp.inner_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro sector _
  unfold globalGaugeLiePairingAt
  rw [integral_finsetSum Finset.univ (fun component _ =>
    globalGaugeLieComponentProduct_integrable period hPeriod
      (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
        (metric sector) (first sector))
      (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
        (metric sector) (second sector))
      component)]
  apply Finset.sum_congr rfl
  intro component _
  change
    inner Real
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (ghostComponent period hPeriod
            (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
              (metric sector) (first sector)) component))
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (ghostComponent period hPeriod
            (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
              (metric sector) (second sector)) component)) =
      ∫ point,
        (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (first sector)) point component *
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (second sector)) point component
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [
      smoothFieldToL2_ae period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (first sector)) component),
      smoothFieldToL2_ae period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (second sector)) component)]
    with point hFirst hSecond
  change inner Real
      ((smoothFieldToL2 period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (first sector)) component) :
          EffectiveQuotient period hPeriod → Real) point)
      ((smoothFieldToL2 period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (second sector)) component) :
          EffectiveQuotient period hPeriod → Real) point) = _
  rw [hFirst, hSecond]
  exact Real.inner_apply _ _

/-- On the dense smooth core, `P†P` is the unchanged reduced BRST Hessian. -/
theorem globalPairedAbelianLorenzGraphRieszOperator_smooth_pairing
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianPotentialSmooth period hPeriod) :
    inner Real
        (globalPairedAbelianLorenzGraphRieszOperator period hPeriod metric
          (globalPairedAbelianLorenzSmoothEmbedding period hPeriod metric first))
        (globalPairedAbelianLorenzSmoothEmbedding period hPeriod metric
          second) =
      globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric
        (globalPairedAbelianLorenzOnShellState period hPeriod metric first)
        (globalPairedAbelianLorenzOnShellState period hPeriod metric second)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [globalPairedAbelianLorenzGraphRieszOperator_pairing
    period hPeriod metric]
  simp only [globalPairedAbelianLorenzFeatureProjection_smooth]
  exact globalPairedAbelianLorenzFeature_inner_eq_BRST
    period hPeriod metric first second

end
end P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
end JanusFormal
