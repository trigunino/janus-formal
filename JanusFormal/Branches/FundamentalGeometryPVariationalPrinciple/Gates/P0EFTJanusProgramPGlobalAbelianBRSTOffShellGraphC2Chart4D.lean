import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianLorenzGraphC2Chart4D

/-!
# Global paired Abelian BRST off-shell graph chart

The existing paired Lorenz graph is enlarged by the independently typed
Nakanishi--Lautrup, antighost, ghost and genuine Faddeev--Popov `δ_g d`
features. The smooth off-shell BRST state has injective dense graph range.
The resulting bounded symmetric form and its Riesz representative agree
exactly on that core with the polarization of the unchanged global `sΨ`
action specialized to the canonical Lorentz volume.

Here “graph” means the closed feature-range completion. No injectivity of its
raw-field projection, differential-operator closability, Green identity,
ellipticity, closed-range or Fredholm claim is used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D

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

abbrev GlobalPairedGaugeLieSmooth :=
  Sector → SmoothQuotientField period hPeriod GaugeLieAlgebra

abbrev GlobalPairedGaugeLieL2 :=
  GlobalPairedAbelianLorenzL2 period hPeriod

local instance globalPairedGaugeLieL2NormedSpace :
    NormedSpace Real (GlobalPairedGaugeLieL2 period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real (GlobalPairedGaugeLieL2 period hPeriod)
    ).toNormedSpace

local instance globalPairedGaugeLieL2Module :
    Module Real (GlobalPairedGaugeLieL2 period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real (GlobalPairedGaugeLieL2 period hPeriod)
    ).toNormedSpace.toModule

local instance globalPairedAbelianLorenzGraphAmbientNormedSpace :
    NormedSpace Real
      (GlobalPairedAbelianLorenzGraphAmbient period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)).toNormedSpace

local instance globalPairedAbelianLorenzGraphAmbientModule :
    Module Real
      (GlobalPairedAbelianLorenzGraphAmbient period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)
    ).toNormedSpace.toModule

def globalPairedGaugeLieL2LinearMap :
    GlobalPairedGaugeLieSmooth period hPeriod →ₗ[Real]
      GlobalPairedGaugeLieL2 period hPeriod where
  toFun := fun field =>
    WithLp.toLp 2 fun index =>
      globalGaugeLieFieldL2Coordinates period hPeriod
        (field index.1) index.2
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact congrArg (fun value => value index.2)
      ((globalGaugeLieFieldL2Coordinates period hPeriod).map_add
        (first index.1) (second index.1))
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact congrArg (fun value => value index.2)
      ((globalGaugeLieFieldL2Coordinates period hPeriod).map_smul
        scalar (field index.1))

theorem globalPairedGaugeLieL2LinearMap_injective :
    Function.Injective
      (globalPairedGaugeLieL2LinearMap period hPeriod) := by
  intro first second hEqual
  funext sector
  apply SmoothQuotientField.ext period hPeriod GaugeLieAlgebra
  intro point
  apply (EuclideanSpace.equiv (Fin 2) Real).injective
  funext component
  have hCoordinate := congrArg
    (fun value : GlobalPairedGaugeLieL2 period hPeriod =>
      value (sector, component)) hEqual
  have hComponent :
      ghostComponent period hPeriod (first sector) component =
        ghostComponent period hPeriod (second sector) component := by
    letI :
        (intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).IsOpenPosMeasure :=
      JanusFormal.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D.intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure
        period hPeriod
    exact smoothFieldToL2_injective period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) hCoordinate
  exact congrArg (fun field => field point) hComponent

def globalPairedAbelianFPL2LinearMap
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGaugeLieSmooth period hPeriod →ₗ[Real]
      GlobalPairedGaugeLieL2 period hPeriod where
  toFun := fun ghost =>
    globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
      globalGeneralMetricAbelianFaddeevPopov period hPeriod
        (metric sector) (ghost sector))
  map_add' first second := by
    apply PiLp.ext
    intro index
    change
      globalGaugeLieFieldL2Coordinates period hPeriod
          (globalGeneralMetricAbelianFaddeevPopov period hPeriod
            (metric index.1) (first index.1 + second index.1)) index.2 = _
    rw [globalGeneralMetricAbelianFaddeevPopov_add]
    exact congrArg (fun value => value index.2)
      ((globalGaugeLieFieldL2Coordinates period hPeriod).map_add _ _)
  map_smul' scalar ghost := by
    apply PiLp.ext
    intro index
    change
      globalGaugeLieFieldL2Coordinates period hPeriod
          (globalGeneralMetricAbelianFaddeevPopov period hPeriod
            (metric index.1) (scalar • ghost index.1)) index.2 = _
    rw [globalGeneralMetricAbelianFaddeevPopov_smul]
    exact congrArg (fun value => value index.2)
      ((globalGaugeLieFieldL2Coordinates period hPeriod).map_smul _ _)

abbrev GlobalPairedAbelianOffShellTail3 :=
  WithLp 2
    (GlobalPairedGaugeLieL2 period hPeriod ×
      GlobalPairedGaugeLieL2 period hPeriod)

abbrev GlobalPairedAbelianOffShellTail2 :=
  WithLp 2
    (GlobalPairedGaugeLieL2 period hPeriod ×
      GlobalPairedAbelianOffShellTail3 period hPeriod)

abbrev GlobalPairedAbelianOffShellTail1 :=
  WithLp 2
    (GlobalPairedGaugeLieL2 period hPeriod ×
      GlobalPairedAbelianOffShellTail2 period hPeriod)

abbrev GlobalPairedAbelianOffShellAmbient :=
  WithLp 2
    (GlobalPairedAbelianLorenzGraphAmbient period hPeriod ×
      GlobalPairedAbelianOffShellTail1 period hPeriod)

local instance globalPairedAbelianOffShellAmbientNormedSpace :
    NormedSpace Real
      (GlobalPairedAbelianOffShellAmbient period hPeriod) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianOffShellAmbient period hPeriod)).toNormedSpace

local instance globalPairedAbelianOffShellAmbientModule :
    Module Real
      (GlobalPairedAbelianOffShellAmbient period hPeriod) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianOffShellAmbient period hPeriod)
    ).toNormedSpace.toModule

def globalPairedAbelianOffShellAmbientLinearMap
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real]
      GlobalPairedAbelianOffShellAmbient period hPeriod where
  toFun := fun state => WithLp.toLp 2
    (globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric
        state.potential,
      WithLp.toLp 2
        (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
            (state.nonminimal sector).nakanishiLautrup.field),
          WithLp.toLp 2
            (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
                (state.nonminimal sector).antighost.field),
              WithLp.toLp 2
                (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
                    (state.nonminimal sector).ghost.field),
                  globalPairedAbelianFPL2LinearMap period hPeriod metric
                    (fun sector =>
                      (state.nonminimal sector).ghost.field)))))
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact
        (globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric
          ).map_add first.potential second.potential
    · apply WithLp.ofLp_injective 2
      apply Prod.ext
      · exact (globalPairedGaugeLieL2LinearMap period hPeriod).map_add _ _
      · apply WithLp.ofLp_injective 2
        apply Prod.ext
        · exact (globalPairedGaugeLieL2LinearMap period hPeriod).map_add _ _
        · apply WithLp.ofLp_injective 2
          apply Prod.ext
          · exact (globalPairedGaugeLieL2LinearMap period hPeriod).map_add _ _
          · exact
              (globalPairedAbelianFPL2LinearMap period hPeriod metric).map_add _ _
  map_smul' scalar state := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact
        (globalPairedAbelianLorenzGraphAmbientLinearMap period hPeriod metric
          ).map_smul scalar state.potential
    · apply WithLp.ofLp_injective 2
      apply Prod.ext
      · exact (globalPairedGaugeLieL2LinearMap period hPeriod).map_smul _ _
      · apply WithLp.ofLp_injective 2
        apply Prod.ext
        · exact (globalPairedGaugeLieL2LinearMap period hPeriod).map_smul _ _
        · apply WithLp.ofLp_injective 2
          apply Prod.ext
          · exact (globalPairedGaugeLieL2LinearMap period hPeriod).map_smul _ _
          · exact
              (globalPairedAbelianFPL2LinearMap period hPeriod metric).map_smul _ _

def globalPairedAbelianOffShellGraphSubmodule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real (GlobalPairedAbelianOffShellAmbient period hPeriod) :=
  (LinearMap.range
    (globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric)
    ).topologicalClosure

abbrev GlobalPairedAbelianOffShellGraphHilbert
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :=
  globalPairedAbelianOffShellGraphSubmodule period hPeriod metric

local instance globalPairedAbelianOffShellGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric)
    ).toNormedSpace

local instance globalPairedAbelianOffShellGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric)
    ).toNormedSpace.toModule

def globalPairedAbelianOffShellSmoothEmbedding
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric where
  toFun state :=
    ⟨globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric state,
      (LinearMap.range
        (globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric)
        ).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric)
          state)⟩
  map_add' first second := Subtype.ext
    ((globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric).map_add
      first second)
  map_smul' scalar state := Subtype.ext
    ((globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric).map_smul
      scalar state)

theorem globalPairedAbelianOffShellSmoothEmbedding_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalPairedAbelianOffShellSmoothEmbedding
        period hPeriod metric) := by
  intro first second hEqual
  have hAmbient := congrArg Subtype.val hEqual
  have hPotentialCoordinates :
      globalPairedAbelianPotentialL2LinearMap period hPeriod
          first.potential =
        globalPairedAbelianPotentialL2LinearMap period hPeriod
          second.potential :=
    congrArg
      (fun value : GlobalPairedAbelianOffShellAmbient period hPeriod =>
        WithLp.fst (WithLp.fst value)) hAmbient
  have hPotential : first.potential = second.potential := by
    funext sector
    apply gaugePotentialL2Coordinates_injective period hPeriod
    funext component index
    exact congrArg
      (fun value : GlobalPairedAbelianPotentialL2 period hPeriod =>
        value (sector, component, index)) hPotentialCoordinates
  have hAuxiliaryCoordinates :
      globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
          (first.nonminimal sector).nakanishiLautrup.field) =
        globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
          (second.nonminimal sector).nakanishiLautrup.field) :=
    congrArg
      (fun value : GlobalPairedAbelianOffShellAmbient period hPeriod =>
        WithLp.fst (WithLp.snd value)) hAmbient
  have hAntighostCoordinates :
      globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
          (first.nonminimal sector).antighost.field) =
        globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
          (second.nonminimal sector).antighost.field) :=
    congrArg
      (fun value : GlobalPairedAbelianOffShellAmbient period hPeriod =>
        WithLp.fst (WithLp.snd (WithLp.snd value))) hAmbient
  have hGhostCoordinates :
      globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
          (first.nonminimal sector).ghost.field) =
        globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
          (second.nonminimal sector).ghost.field) :=
    congrArg
      (fun value : GlobalPairedAbelianOffShellAmbient period hPeriod =>
        WithLp.fst (WithLp.snd (WithLp.snd (WithLp.snd value)))) hAmbient
  have hAuxiliary :=
    globalPairedGaugeLieL2LinearMap_injective
      period hPeriod hAuxiliaryCoordinates
  have hAntighost :=
    globalPairedGaugeLieL2LinearMap_injective
      period hPeriod hAntighostCoordinates
  have hGhost :=
    globalPairedGaugeLieL2LinearMap_injective
      period hPeriod hGhostCoordinates
  apply GlobalPairedAbelianBRSTState.ext
  · exact hPotential
  · funext sector
    apply GlobalAbelianNonminimalFields.ext
    · exact GlobalAbelianGhostField.ext (congrFun hGhost sector)
    · exact GlobalAbelianAntighostField.ext (congrFun hAntighost sector)
    · exact GlobalAbelianNakanishiLautrupField.ext
        (congrFun hAuxiliary sector)

theorem globalPairedAbelianOffShellSmoothEmbedding_denseRange
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  unfold GlobalPairedAbelianOffShellGraphHilbert
    globalPairedAbelianOffShellGraphSubmodule
  let graph :=
    globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric
  have hRange :
      Subtype.val '' Set.range
          (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric) =
        (LinearMap.range graph :
          Set (GlobalPairedAbelianOffShellAmbient period hPeriod)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨state, rfl⟩, rfl⟩
      exact ⟨state, rfl⟩
    · rintro ⟨state, rfl⟩
      exact
        ⟨globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
            state,
          ⟨state, rfl⟩, rfl⟩
  change closure
      (LinearMap.range graph :
        Set (GlobalPairedAbelianOffShellAmbient period hPeriod)) ⊆
    closure (Subtype.val '' Set.range
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric))
  rw [hRange]

@[implicit_reducible]
def globalPairedAbelianOffShellGraphCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) := by
  unfold GlobalPairedAbelianOffShellGraphHilbert
    globalPairedAbelianOffShellGraphSubmodule
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalPairedAbelianOffShellAmbientLinearMap period hPeriod metric))

def globalPairedAbelianOffShellAmbientProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianOffShellAmbient period hPeriod :=
  (globalPairedAbelianOffShellGraphSubmodule period hPeriod metric).subtypeL

def globalPairedAbelianOffShellPotentialAmbientProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianLorenzGraphAmbient period hPeriod :=
  (WithLp.fstL 2 Real
      (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)
      (GlobalPairedAbelianOffShellTail1 period hPeriod)).comp
    (globalPairedAbelianOffShellAmbientProjection period hPeriod metric)

def globalPairedAbelianOffShellLorenzProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedGaugeLieL2 period hPeriod :=
  (WithLp.sndL 2 Real
      (GlobalPairedAbelianPotentialL2 period hPeriod)
      (GlobalPairedAbelianLorenzL2 period hPeriod)).comp
    (globalPairedAbelianOffShellPotentialAmbientProjection
      period hPeriod metric)

def globalPairedAbelianOffShellTail1Projection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianOffShellTail1 period hPeriod :=
  (WithLp.sndL 2 Real
      (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)
      (GlobalPairedAbelianOffShellTail1 period hPeriod)).comp
    (globalPairedAbelianOffShellAmbientProjection period hPeriod metric)

def globalPairedAbelianOffShellBProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedGaugeLieL2 period hPeriod :=
  (WithLp.fstL 2 Real
      (GlobalPairedGaugeLieL2 period hPeriod)
      (GlobalPairedAbelianOffShellTail2 period hPeriod)).comp
    (globalPairedAbelianOffShellTail1Projection period hPeriod metric)

def globalPairedAbelianOffShellTail2Projection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianOffShellTail2 period hPeriod :=
  (WithLp.sndL 2 Real
      (GlobalPairedGaugeLieL2 period hPeriod)
      (GlobalPairedAbelianOffShellTail2 period hPeriod)).comp
    (globalPairedAbelianOffShellTail1Projection period hPeriod metric)

def globalPairedAbelianOffShellAntighostProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedGaugeLieL2 period hPeriod :=
  (WithLp.fstL 2 Real
      (GlobalPairedGaugeLieL2 period hPeriod)
      (GlobalPairedAbelianOffShellTail3 period hPeriod)).comp
    (globalPairedAbelianOffShellTail2Projection period hPeriod metric)

def globalPairedAbelianOffShellTail3Projection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianOffShellTail3 period hPeriod :=
  (WithLp.sndL 2 Real
      (GlobalPairedGaugeLieL2 period hPeriod)
      (GlobalPairedAbelianOffShellTail3 period hPeriod)).comp
    (globalPairedAbelianOffShellTail2Projection period hPeriod metric)

def globalPairedAbelianOffShellFPProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedGaugeLieL2 period hPeriod :=
  (WithLp.sndL 2 Real
      (GlobalPairedGaugeLieL2 period hPeriod)
      (GlobalPairedGaugeLieL2 period hPeriod)).comp
    (globalPairedAbelianOffShellTail3Projection period hPeriod metric)

def globalPairedAbelianOffShellHessian
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
        Real :=
  (innerSL Real).bilinearComp
      (globalPairedAbelianOffShellBProjection period hPeriod metric)
      (globalPairedAbelianOffShellLorenzProjection period hPeriod metric) +
    (innerSL Real).bilinearComp
      (globalPairedAbelianOffShellLorenzProjection period hPeriod metric)
      (globalPairedAbelianOffShellBProjection period hPeriod metric) -
    (innerSL Real).bilinearComp
      (globalPairedAbelianOffShellBProjection period hPeriod metric)
      (globalPairedAbelianOffShellBProjection period hPeriod metric) +
    (innerSL Real).bilinearComp
      (globalPairedAbelianOffShellAntighostProjection period hPeriod metric)
      (globalPairedAbelianOffShellFPProjection period hPeriod metric) +
    (innerSL Real).bilinearComp
      (globalPairedAbelianOffShellFPProjection period hPeriod metric)
      (globalPairedAbelianOffShellAntighostProjection period hPeriod metric)

@[simp]
theorem globalPairedAbelianOffShellHessian_apply
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    globalPairedAbelianOffShellHessian period hPeriod metric first second =
      inner Real
          (globalPairedAbelianOffShellBProjection period hPeriod metric first)
          (globalPairedAbelianOffShellLorenzProjection period hPeriod metric
            second) +
        inner Real
          (globalPairedAbelianOffShellLorenzProjection period hPeriod metric
            first)
          (globalPairedAbelianOffShellBProjection period hPeriod metric second) -
        inner Real
          (globalPairedAbelianOffShellBProjection period hPeriod metric first)
          (globalPairedAbelianOffShellBProjection period hPeriod metric second) +
        inner Real
          (globalPairedAbelianOffShellAntighostProjection period hPeriod metric
            first)
          (globalPairedAbelianOffShellFPProjection period hPeriod metric second) +
        inner Real
          (globalPairedAbelianOffShellFPProjection period hPeriod metric first)
          (globalPairedAbelianOffShellAntighostProjection period hPeriod metric
            second) :=
  rfl

theorem globalPairedAbelianOffShellHessian_comm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    globalPairedAbelianOffShellHessian period hPeriod metric first second =
      globalPairedAbelianOffShellHessian period hPeriod metric second first := by
  simp only [globalPairedAbelianOffShellHessian_apply]
  rw [real_inner_comm
      (globalPairedAbelianOffShellBProjection period hPeriod metric first)
      (globalPairedAbelianOffShellLorenzProjection period hPeriod metric second),
    real_inner_comm
      (globalPairedAbelianOffShellBProjection period hPeriod metric second)
      (globalPairedAbelianOffShellLorenzProjection period hPeriod metric first),
    real_inner_comm
      (globalPairedAbelianOffShellBProjection period hPeriod metric first)
      (globalPairedAbelianOffShellBProjection period hPeriod metric second),
    real_inner_comm
      (globalPairedAbelianOffShellAntighostProjection period hPeriod metric first)
      (globalPairedAbelianOffShellFPProjection period hPeriod metric second),
    real_inner_comm
      (globalPairedAbelianOffShellFPProjection period hPeriod metric first)
      (globalPairedAbelianOffShellAntighostProjection period hPeriod metric
        second)]
  ring

/-- Bounded self-adjoint representative of the off-shell Hessian form. -/
def globalPairedAbelianOffShellRieszOperator
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric := by
  letI : CompleteSpace
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
    globalPairedAbelianOffShellGraphCompleteSpace period hPeriod metric
  exact
    (globalPairedAbelianOffShellLorenzProjection
        period hPeriod metric).adjoint.comp
      (globalPairedAbelianOffShellBProjection period hPeriod metric) +
    (globalPairedAbelianOffShellBProjection
        period hPeriod metric).adjoint.comp
      (globalPairedAbelianOffShellLorenzProjection period hPeriod metric) -
    (globalPairedAbelianOffShellBProjection
        period hPeriod metric).adjoint.comp
      (globalPairedAbelianOffShellBProjection period hPeriod metric) +
    (globalPairedAbelianOffShellFPProjection
        period hPeriod metric).adjoint.comp
      (globalPairedAbelianOffShellAntighostProjection period hPeriod metric) +
    (globalPairedAbelianOffShellAntighostProjection
        period hPeriod metric).adjoint.comp
      (globalPairedAbelianOffShellFPProjection period hPeriod metric)

theorem globalPairedAbelianOffShellRieszOperator_pairing
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    inner Real
        (globalPairedAbelianOffShellRieszOperator period hPeriod metric first)
        second =
      globalPairedAbelianOffShellHessian period hPeriod metric first second := by
  letI : CompleteSpace
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
    globalPairedAbelianOffShellGraphCompleteSpace period hPeriod metric
  unfold globalPairedAbelianOffShellRieszOperator
  simp only [add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, inner_add_left, inner_sub_left]
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem globalPairedAbelianOffShellRieszOperator_symmetric
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    inner Real
        (globalPairedAbelianOffShellRieszOperator period hPeriod metric first)
        second =
      inner Real first
        (globalPairedAbelianOffShellRieszOperator period hPeriod metric
          second) := by
  rw [globalPairedAbelianOffShellRieszOperator_pairing,
    globalPairedAbelianOffShellHessian_comm,
    ← globalPairedAbelianOffShellRieszOperator_pairing]
  exact real_inner_comm _ _

@[simp]
theorem globalPairedAbelianOffShellLorenzProjection_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianOffShellLorenzProjection period hPeriod metric
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
          state) =
      globalPairedAbelianLorenzL2LinearMap period hPeriod metric
        state.potential :=
  rfl

@[simp]
theorem globalPairedAbelianOffShellBProjection_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianOffShellBProjection period hPeriod metric
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
          state) =
      globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
        (state.nonminimal sector).nakanishiLautrup.field) :=
  rfl

@[simp]
theorem globalPairedAbelianOffShellAntighostProjection_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianOffShellAntighostProjection period hPeriod metric
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
          state) =
      globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
        (state.nonminimal sector).antighost.field) :=
  rfl

@[simp]
theorem globalPairedAbelianOffShellFPProjection_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianOffShellFPProjection period hPeriod metric
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
          state) =
      globalPairedAbelianFPL2LinearMap period hPeriod metric (fun sector =>
        (state.nonminimal sector).ghost.field) :=
  rfl

theorem globalPairedGaugeLieL2_inner_eq_sum_integral
    (first second : GlobalPairedGaugeLieSmooth period hPeriod) :
    inner Real
        (globalPairedGaugeLieL2LinearMap period hPeriod first)
        (globalPairedGaugeLieL2LinearMap period hPeriod second) =
      ∑ sector : Sector,
        ∫ point,
          globalGaugeLiePairingAt period hPeriod
            (first sector) (second sector) point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  simp only [PiLp.inner_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro sector _
  unfold globalGaugeLiePairingAt
  rw [integral_finsetSum Finset.univ (fun component _ =>
    globalGaugeLieComponentProduct_integrable period hPeriod
      (first sector) (second sector) component)]
  apply Finset.sum_congr rfl
  intro component _
  change
    inner Real
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (ghostComponent period hPeriod (first sector) component))
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (ghostComponent period hPeriod (second sector) component)) =
      ∫ point,
        first sector point component * second sector point component
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [smoothFieldToL2_ae period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (ghostComponent period hPeriod (first sector) component),
    smoothFieldToL2_ae period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (ghostComponent period hPeriod (second sector) component)]
    with point hFirst hSecond
  change inner Real
      ((smoothFieldToL2 period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        (ghostComponent period hPeriod (first sector) component) :
          EffectiveQuotient period hPeriod → Real) point)
      ((smoothFieldToL2 period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        (ghostComponent period hPeriod (second sector) component) :
          EffectiveQuotient period hPeriod → Real) point) = _
  rw [hFirst, hSecond]
  exact Real.inner_apply _ _

theorem globalPairedAbelianGaugeFermionBRSTMixedAction_eq_offShell_inner
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
        first second
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      inner Real
          (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
            (first.nonminimal sector).nakanishiLautrup.field))
          (globalPairedAbelianLorenzL2LinearMap period hPeriod metric
            second.potential) -
        (1 / 2 : Real) *
          inner Real
            (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
              (first.nonminimal sector).nakanishiLautrup.field))
            (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
              (second.nonminimal sector).nakanishiLautrup.field)) +
        inner Real
          (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
            (first.nonminimal sector).antighost.field))
          (globalPairedAbelianFPL2LinearMap period hPeriod metric
            (fun sector => (second.nonminimal sector).ghost.field)) := by
  let BFirst : GlobalPairedGaugeLieSmooth period hPeriod := fun sector =>
    (first.nonminimal sector).nakanishiLautrup.field
  let BSecond : GlobalPairedGaugeLieSmooth period hPeriod := fun sector =>
    (second.nonminimal sector).nakanishiLautrup.field
  let lorenzSecond : GlobalPairedGaugeLieSmooth period hPeriod := fun sector =>
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod
      (metric sector) (second.potential sector)
  let antighostFirst : GlobalPairedGaugeLieSmooth period hPeriod := fun sector =>
    (first.nonminimal sector).antighost.field
  let fpSecond : GlobalPairedGaugeLieSmooth period hPeriod := fun sector =>
    globalGeneralMetricAbelianFaddeevPopov period hPeriod
      (metric sector) (second.nonminimal sector).ghost.field
  change
    (∫ point, ∑ sector : Sector,
      (globalGaugeLiePairingAt period hPeriod
          (BFirst sector) (lorenzSecond sector) point -
        (1 / 2 : Real) *
          globalGaugeLiePairingAt period hPeriod
            (BFirst sector) (BSecond sector) point +
        globalGaugeLiePairingAt period hPeriod
          (antighostFirst sector) (fpSecond sector) point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      inner Real
          (globalPairedGaugeLieL2LinearMap period hPeriod BFirst)
          (globalPairedGaugeLieL2LinearMap period hPeriod lorenzSecond) -
        (1 / 2 : Real) *
          inner Real
            (globalPairedGaugeLieL2LinearMap period hPeriod BFirst)
            (globalPairedGaugeLieL2LinearMap period hPeriod BSecond) +
        inner Real
          (globalPairedGaugeLieL2LinearMap period hPeriod antighostFirst)
          (globalPairedGaugeLieL2LinearMap period hPeriod fpSecond)
  rw [integral_finsetSum Finset.univ]
  · rw [globalPairedGaugeLieL2_inner_eq_sum_integral,
      globalPairedGaugeLieL2_inner_eq_sum_integral,
      globalPairedGaugeLieL2_inner_eq_sum_integral]
    have hSector (sector : Sector) :
        (∫ point,
          (globalGaugeLiePairingAt period hPeriod
              (BFirst sector) (lorenzSecond sector) point -
            (1 / 2 : Real) *
              globalGaugeLiePairingAt period hPeriod
                (BFirst sector) (BSecond sector) point +
            globalGaugeLiePairingAt period hPeriod
              (antighostFirst sector) (fpSecond sector) point)
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
        (∫ point,
          globalGaugeLiePairingAt period hPeriod
            (BFirst sector) (lorenzSecond sector) point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) -
          (1 / 2 : Real) *
            (∫ point,
              globalGaugeLiePairingAt period hPeriod
                (BFirst sector) (BSecond sector) point
              ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) +
          (∫ point,
            globalGaugeLiePairingAt period hPeriod
              (antighostFirst sector) (fpSecond sector) point
            ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) := by
      have hBL := globalGaugeLiePairingAt_integrable period hPeriod
        (BFirst sector) (lorenzSecond sector)
      have hBB := globalGaugeLiePairingAt_integrable period hPeriod
        (BFirst sector) (BSecond sector)
      have hCFP := globalGaugeLiePairingAt_integrable period hPeriod
        (antighostFirst sector) (fpSecond sector)
      calc
        _ =
            (∫ point,
              (globalGaugeLiePairingAt period hPeriod
                  (BFirst sector) (lorenzSecond sector) point -
                (1 / 2 : Real) *
                  globalGaugeLiePairingAt period hPeriod
                    (BFirst sector) (BSecond sector) point)
              ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) +
              ∫ point,
                globalGaugeLiePairingAt period hPeriod
                  (antighostFirst sector) (fpSecond sector) point
                ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
          integral_add (hBL.sub (hBB.const_mul (1 / 2 : Real))) hCFP
        _ =
            ((∫ point,
                globalGaugeLiePairingAt period hPeriod
                  (BFirst sector) (lorenzSecond sector) point
                ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) -
              ∫ point,
                (1 / 2 : Real) *
                  globalGaugeLiePairingAt period hPeriod
                    (BFirst sector) (BSecond sector) point
                ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) +
              ∫ point,
                globalGaugeLiePairingAt period hPeriod
                  (antighostFirst sector) (fpSecond sector) point
                ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
          rw [integral_sub hBL (hBB.const_mul (1 / 2 : Real))]
        _ = _ := by rw [integral_const_mul]
    simp_rw [hSector]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
  · intro sector _
    exact
      ((globalGaugeLiePairingAt_integrable period hPeriod
          (BFirst sector) (lorenzSecond sector)).sub
        ((globalGaugeLiePairingAt_integrable period hPeriod
          (BFirst sector) (BSecond sector)).const_mul (1 / 2 : Real))).add
        (globalGaugeLiePairingAt_integrable period hPeriod
          (antighostFirst sector) (fpSecond sector))

theorem globalPairedAbelianOffShellHessian_smooth_eq_BRST
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianOffShellHessian period hPeriod metric
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric first)
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
          second) =
      globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric first second
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [globalPairedAbelianOffShellHessian_apply]
  simp only [globalPairedAbelianOffShellBProjection_smooth,
    globalPairedAbelianOffShellLorenzProjection_smooth,
    globalPairedAbelianOffShellAntighostProjection_smooth,
    globalPairedAbelianOffShellFPProjection_smooth]
  rw [globalPairedAbelianGaugeFermionBRSTPolarizationAction_eq_mixed,
    globalPairedAbelianGaugeFermionBRSTMixedAction_eq_offShell_inner,
    globalPairedAbelianGaugeFermionBRSTMixedAction_eq_offShell_inner]
  rw [real_inner_comm
      (globalPairedAbelianLorenzL2LinearMap period hPeriod metric
        first.potential)
      (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
        (second.nonminimal sector).nakanishiLautrup.field)),
    real_inner_comm
      (globalPairedAbelianFPL2LinearMap period hPeriod metric (fun sector =>
        (first.nonminimal sector).ghost.field))
      (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
        (second.nonminimal sector).antighost.field)),
    real_inner_comm
      (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
        (second.nonminimal sector).nakanishiLautrup.field))
      (globalPairedGaugeLieL2LinearMap period hPeriod (fun sector =>
        (first.nonminimal sector).nakanishiLautrup.field))]
  ring

/-- Quadratic graph action extending the canonical-volume specialization of
the unchanged off-shell Abelian `sΨ`. -/
def globalPairedAbelianOffShellGraphAction
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state :
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) : Real :=
  (1 / 2 : Real) *
    globalPairedAbelianOffShellHessian period hPeriod metric state state

theorem globalPairedAbelianOffShellGraphAction_smooth_eq_BRST
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianOffShellGraphAction period hPeriod metric
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
          state) =
      globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric state
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold globalPairedAbelianOffShellGraphAction
  rw [globalPairedAbelianOffShellHessian_smooth_eq_BRST,
    globalPairedAbelianGaugeFermionBRSTPolarizationAction_self]
  ring

private theorem symmetricQuadratic_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second,
      bilinear first second = bilinear second first)
    (point : E) :
    HasFDerivAt (fun state => (1 / 2 : Real) * bilinear state state)
      (bilinear point) point := by
  have hDiagonal :=
    (bilinear.hasFDerivAt (x := point)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) point)
  have hHalf := hDiagonal.const_mul (1 / 2 : Real)
  apply hHalf.congr_fderiv
  ext direction
  change (1 / 2 : Real) *
      (bilinear point direction + bilinear direction point) =
    bilinear point direction
  rw [hSymmetric direction point]
  ring

private theorem symmetricQuadratic_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real) :
    ContDiff Real ⊤ (fun state => (1 / 2 : Real) * bilinear state state) :=
  contDiff_const.mul (bilinear.contDiff.clm_apply contDiff_id)

theorem globalPairedAbelianOffShellGraphAction_hasFDerivAt
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state :
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    HasFDerivAt
      (globalPairedAbelianOffShellGraphAction period hPeriod metric)
      (globalPairedAbelianOffShellHessian period hPeriod metric state)
      state := by
  exact @symmetricQuadratic_hasFDerivAt
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric)
    inferInstance
    (globalPairedAbelianOffShellGraphNormedSpace period hPeriod metric)
    (globalPairedAbelianOffShellHessian period hPeriod metric)
    (globalPairedAbelianOffShellHessian_comm period hPeriod metric)
    state

theorem globalPairedAbelianOffShellGraphAction_fderiv
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state :
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    fderiv Real
        (globalPairedAbelianOffShellGraphAction period hPeriod metric)
        state =
      globalPairedAbelianOffShellHessian period hPeriod metric state :=
  (globalPairedAbelianOffShellGraphAction_hasFDerivAt
    period hPeriod metric state).fderiv

theorem globalPairedAbelianOffShellGraphAction_second_fderiv
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (base :
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :
    fderiv Real
        (fun state => fderiv Real
          (globalPairedAbelianOffShellGraphAction period hPeriod metric)
          state)
        base =
      globalPairedAbelianOffShellHessian period hPeriod metric := by
  have hLinear :
      HasFDerivAt
        (globalPairedAbelianOffShellHessian period hPeriod metric)
        (globalPairedAbelianOffShellHessian period hPeriod metric)
        base :=
    (globalPairedAbelianOffShellHessian period hPeriod metric).hasFDerivAt
  have hEventually :
      (fun state => fderiv Real
        (globalPairedAbelianOffShellGraphAction
          period hPeriod metric) state) =ᶠ[𝓝 base]
      globalPairedAbelianOffShellHessian period hPeriod metric :=
    Filter.Eventually.of_forall fun state =>
      globalPairedAbelianOffShellGraphAction_fderiv
        period hPeriod metric state
  exact (hLinear.congr_of_eventuallyEq hEventually).fderiv

theorem globalPairedAbelianOffShellGraphAction_contDiff
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real ⊤
      (globalPairedAbelianOffShellGraphAction period hPeriod metric) := by
  unfold globalPairedAbelianOffShellGraphAction
  exact @symmetricQuadratic_contDiff
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric)
    inferInstance
    (globalPairedAbelianOffShellGraphNormedSpace period hPeriod metric)
    (globalPairedAbelianOffShellHessian period hPeriod metric)

theorem globalPairedAbelianOffShellGraphAction_contDiff_two
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (globalPairedAbelianOffShellGraphAction period hPeriod metric) :=
  (globalPairedAbelianOffShellGraphAction_contDiff
    period hPeriod metric).of_le (by simp)

/-! ## Corrected typed gauge-fixed tangent -/

def globalPairedAbelianBRSTPotentialProjectionLinearMap :
    GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real]
      (Sector → SmoothAbelianGaugePotential period hPeriod) where
  toFun := GlobalPairedAbelianBRSTState.potential
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def globalPairedAbelianBRSTNonminimalProjectionLinearMap :
    GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real]
      (Sector → GlobalAbelianNonminimalFields period hPeriod) where
  toFun := GlobalPairedAbelianBRSTState.nonminimal
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The two Abelian triples in the nine-field typed packet, with the
diffeomorphism triple fixed at zero. -/
def globalPairedAbelianNonminimalTypedInclusionLinearMap :
    (Sector → GlobalAbelianNonminimalFields period hPeriod) →ₗ[Real]
      GlobalTypedNonminimalFields period hPeriod where
  toFun nonminimal :=
    { abelian := nonminimal
      diffeomorphism := 0 }
  map_add' first second := by
    apply GlobalTypedNonminimalFields.ext
    · rfl
    · change (0 : GlobalDiffeomorphismNonminimalFields
        period hPeriod) = 0 + 0
      exact (zero_add 0).symm
  map_smul' scalar nonminimal := by
    apply GlobalTypedNonminimalFields.ext
    · rfl
    · change (0 : GlobalDiffeomorphismNonminimalFields
        period hPeriod) = scalar • 0
      exact (smul_zero scalar).symm

@[simp]
theorem globalPairedAbelianNonminimalTypedInclusion_abelian
    (nonminimal :
      Sector → GlobalAbelianNonminimalFields period hPeriod) :
    (globalPairedAbelianNonminimalTypedInclusionLinearMap
      period hPeriod nonminimal).abelian = nonminimal := by
  simp [globalPairedAbelianNonminimalTypedInclusionLinearMap]

@[simp]
theorem globalPairedAbelianNonminimalTypedInclusion_diffeomorphism
    (nonminimal :
      Sector → GlobalAbelianNonminimalFields period hPeriod) :
    (globalPairedAbelianNonminimalTypedInclusionLinearMap
      period hPeriod nonminimal).diffeomorphism = 0 := by
  simp [globalPairedAbelianNonminimalTypedInclusionLinearMap]

theorem globalPairedAbelianNonminimalTypedInclusion_injective :
    Function.Injective
      (globalPairedAbelianNonminimalTypedInclusionLinearMap
        period hPeriod) := by
  intro first second hEqual
  have hAbelian :=
    congrArg GlobalTypedNonminimalFields.abelian hEqual
  simpa [globalPairedAbelianNonminimalTypedInclusionLinearMap] using hAbelian

/-- The off-shell potential and its two nonminimal triples in the corrected
gauge-fixed tangent, without legacy ghost duplication. -/
def globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace) :
    GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent
        period hPeriod configuration where
  toFun state :=
    (globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
        period hPeriod data state.potential,
      globalPairedAbelianNonminimalTypedInclusionLinearMap
        period hPeriod state.nonminimal)
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
          period hPeriod data).map_add first.potential second.potential
    · exact
        (globalPairedAbelianNonminimalTypedInclusionLinearMap
          period hPeriod).map_add first.nonminimal second.nonminimal
  map_smul' scalar state := by
    apply Prod.ext
    · exact
        (globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
          period hPeriod data).map_smul scalar state.potential
    · exact
        (globalPairedAbelianNonminimalTypedInclusionLinearMap
          period hPeriod).map_smul scalar state.nonminimal

@[simp]
theorem globalPairedAbelianBRSTStateGaugeFixedTangent_abelian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    (globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap
      period hPeriod configuration data state).2.abelian =
      state.nonminimal := by
  simp [globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap,
    globalPairedAbelianNonminimalTypedInclusionLinearMap]

@[simp]
theorem globalPairedAbelianBRSTStateGaugeFixedTangent_diffeomorphism
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    (globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap
      period hPeriod configuration data state).2.diffeomorphism = 0 := by
  simp [globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap,
    globalPairedAbelianNonminimalTypedInclusionLinearMap]

theorem globalPairedAbelianBRSTStateGaugeFixedTangent_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace) :
    Function.Injective
      (globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap
        period hPeriod configuration data) := by
  intro first second hEqual
  apply GlobalPairedAbelianBRSTState.ext
  · apply
      globalCandidateAPairedGaugePotentialMinimalTangentLinearMap_injective
        period hPeriod data
    exact congrArg Prod.fst hEqual
  · apply globalPairedAbelianNonminimalTypedInclusion_injective
      period hPeriod
    exact congrArg Prod.snd hEqual

/-- Physical Candidate-A specialization recording the analytic graph point
and the exact typed gauge-fixed tangent direction. -/
def globalPairedAbelianOffShellGraphTypedCoreLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace) :
    GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real]
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) ×
        GlobalGaugeFixedPhysicalFieldTangent
          period hPeriod configuration) where
  toFun state :=
    (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) state,
      globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap
        period hPeriod configuration data state)
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector
            period hPeriod data)).map_add first second
    · exact
        (globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap
          period hPeriod configuration data).map_add first second
  map_smul' scalar state := by
    apply Prod.ext
    · exact
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector
            period hPeriod data)).map_smul scalar state
    · exact
        (globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap
          period hPeriod configuration data).map_smul scalar state

theorem globalPairedAbelianOffShellGraphTypedCoreLinearMap_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace) :
    Function.Injective
      (globalPairedAbelianOffShellGraphTypedCoreLinearMap
        period hPeriod configuration data) := by
  intro first second hEqual
  apply globalPairedAbelianOffShellSmoothEmbedding_injective
    period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
  exact congrArg Prod.fst hEqual

end
end P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
end JanusFormal
