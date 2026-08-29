import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianFaddeevPopovScalarBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalScalarGreenBoundaryDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffL2Convergence4D

/-!
# Abelian Faddeev--Popov Green--Stokes bridge

The intrinsic Abelian FP pairing defect is the exact oriented scalar Green
boundary current whenever the existing unrestricted scalar Green--Stokes data
is available.  Hence every existing Green-isotropic scalar boundary condition
makes each real FP component formally symmetric on its smooth boundary domain.

This is a composition of existing FP, Green--Stokes, boundary-domain and
minimal-cutoff bricks.  It transfers the existing single-valued graph closure
to each real FP component, proves density of the actual four-component smooth
ghost core in their finite product, and realizes that completed graph as a
single-valued paired FP operator on its ambient range.  It does not construct
the unrestricted scalar Green--Stokes data or claim self-adjointness of that
realization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D
open P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
open P0EFTJanusMappingTorusCutBulkGlobalScalarBoundaryForm4D
open P0EFTJanusMappingTorusCutBulkGlobalScalarGreenBoundaryDomain4D
open P0EFTJanusMappingTorusScalarSeparatedBoundaryCondition4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffL2Convergence4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianFaddeevPopovScalarBridge4D

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

/-- The smooth intrinsic FP adjunction defect is the genuine oriented boundary
current from the scalar Green--Stokes package. -/
theorem intrinsicAbelianFaddeevPopov_component_pairingDefect_eq_orientedBoundary
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (first second : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) :
    inner Real
          (globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianFaddeevPopov period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) first)
            component)
          (globalGaugeLieFieldL2Coordinates period hPeriod second component) -
        inner Real
          (globalGaugeLieFieldL2Coordinates period hPeriod first component)
          (globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianFaddeevPopov period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) second)
            component) =
      cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod
        (ghostComponent period hPeriod first component)
        (ghostComponent period hPeriod second component) := by
  rw [intrinsicAbelianFaddeevPopov_component_pairingDefect_eq_integral]
  exact green.eulerSkew_integral_eq_orientedBoundary
    (ghostComponent period hPeriod first component)
    (ghostComponent period hPeriod second component)

/-- Every existing Green-isotropic scalar boundary domain makes one real
intrinsic FP component formally symmetric on its admitted smooth ghosts. -/
theorem intrinsicAbelianFaddeevPopov_component_symmetric_of_greenBoundaryCondition
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (condition : CanonicalCutBulkScalarGreenBoundaryCondition period hPeriod)
    (first second : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2)
    (hFirst : condition.admits (ghostComponent period hPeriod first component))
    (hSecond : condition.admits (ghostComponent period hPeriod second component)) :
    inner Real
          (globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianFaddeevPopov period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) first)
            component)
          (globalGaugeLieFieldL2Coordinates period hPeriod second component) =
        inner Real
          (globalGaugeLieFieldL2Coordinates period hPeriod first component)
          (globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianFaddeevPopov period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) second)
            component) := by
  apply sub_eq_zero.mp
  rw [intrinsicAbelianFaddeevPopov_component_pairingDefect_eq_orientedBoundary
    period hPeriod green first second component]
  exact condition.green_isotropic
    (ghostComponent period hPeriod first component)
    (ghostComponent period hPeriod second component) hFirst hSecond

/-- Formal symmetry of the full two-component intrinsic FP pairing when both
ghosts satisfy the same scalar Green boundary condition componentwise. -/
theorem intrinsicAbelianFaddeevPopov_symmetric_of_greenBoundaryCondition
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (condition : CanonicalCutBulkScalarGreenBoundaryCondition period hPeriod)
    (first second : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (hFirst : ∀ component,
      condition.admits (ghostComponent period hPeriod first component))
    (hSecond : ∀ component,
      condition.admits (ghostComponent period hPeriod second component)) :
    (∑ component : Fin 2,
      inner Real
        (globalGaugeLieFieldL2Coordinates period hPeriod
          (globalGeneralMetricAbelianFaddeevPopov period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) first)
          component)
        (globalGaugeLieFieldL2Coordinates period hPeriod second component)) =
      ∑ component : Fin 2,
        inner Real
          (globalGaugeLieFieldL2Coordinates period hPeriod first component)
          (globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianFaddeevPopov period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) second)
            component) := by
  apply Finset.sum_congr rfl
  intro component _
  exact intrinsicAbelianFaddeevPopov_component_symmetric_of_greenBoundaryCondition
    period hPeriod green condition first second component
      (hFirst component) (hSecond component)

/-- Componentwise formal symmetry on the canonical smooth Dirichlet ghost
domain. -/
theorem intrinsicAbelianFaddeevPopov_component_symmetric_of_dirichlet
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (first second : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2)
    (hFirst : CanonicalLatitudeScalarDirichletBoundaryCondition period hPeriod
      (ghostComponent period hPeriod first component))
    (hSecond : CanonicalLatitudeScalarDirichletBoundaryCondition period hPeriod
      (ghostComponent period hPeriod second component)) :
    inner Real
          (globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianFaddeevPopov period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) first)
            component)
          (globalGaugeLieFieldL2Coordinates period hPeriod second component) =
        inner Real
          (globalGaugeLieFieldL2Coordinates period hPeriod first component)
          (globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianFaddeevPopov period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) second)
            component) :=
  intrinsicAbelianFaddeevPopov_component_symmetric_of_greenBoundaryCondition
    period hPeriod green (dirichletScalarGreenBoundaryCondition period hPeriod)
      first second component hFirst hSecond

/-- Existing physical scalar Green core specialized to the intrinsic
mass-zero FP operator. -/
def intrinsicAbelianFaddeevPopovScalarGreenCore
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    CanonicalPhysicalScalarFirstSheetGreenCoreData period hPeriod 0 :=
  (green.toWeightedTransportedGlobalGreenData period hPeriod).greenCore
    period hPeriod

/-- On smooth ghosts, the scalar Green-core operator is exactly one physical
`L²` coordinate of the intrinsic Abelian FP operator. -/
theorem intrinsicAbelianFaddeevPopovScalarGreenCore_operator_eq_component
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) :
    (intrinsicAbelianFaddeevPopovScalarGreenCore period hPeriod green).core.operator
        (ghostComponent period hPeriod ghost component) =
      globalGaugeLieFieldL2Coordinates period hPeriod
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost)
        component := by
  rw [intrinsicAbelianFaddeevPopov_component_l2_eq_scalarOperator]
  rfl

/-- The zero-Cauchy smooth FP component core is dense in physical `L²`; this is
the existing cutoff-density theorem, not an additional premise. -/
theorem intrinsicAbelianFaddeevPopovScalarGreenCore_minimalDense
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    (intrinsicAbelianFaddeevPopovScalarGreenCore period hPeriod green
      ).MinimalCoreDense period hPeriod :=
  canonicalPhysicalScalarMinimalCoreDense period hPeriod
    (intrinsicAbelianFaddeevPopovScalarGreenCore period hPeriod green)

/-- Concrete componentwise FP closability certificate: the completed scalar
graph inclusion is injective and every vertical graph vector has zero operator
coordinate. -/
theorem intrinsicAbelianFaddeevPopovScalarGreenCore_closable_certificate
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          (intrinsicAbelianFaddeevPopovScalarGreenCore
            period hPeriod green).core) ∧
      (∀ graphField : CanonicalScalarGreenCoreGraphSpace
          (intrinsicAbelianFaddeevPopovScalarGreenCore
            period hPeriod green).core,
        canonicalScalarGreenCoreGraphInclusion
              (intrinsicAbelianFaddeevPopovScalarGreenCore
                period hPeriod green).core graphField = 0 →
          canonicalScalarGreenCoreGraphOperator
              (intrinsicAbelianFaddeevPopovScalarGreenCore
                period hPeriod green).core graphField = 0) :=
  CanonicalScalarHilbertGreenCore.minimalCoreClosable_certificate
    (intrinsicAbelianFaddeevPopovScalarGreenCore period hPeriod green).core
    (intrinsicAbelianFaddeevPopovScalarGreenCore_minimalDense
      period hPeriod green)

private abbrev IntrinsicAbelianFPScalarGraphSpace
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :=
  CanonicalScalarGreenCoreGraphSpace
    (intrinsicAbelianFaddeevPopovScalarGreenCore period hPeriod green).core

/-- Completed differential graph for both `U(1)²` ghost components in both
Candidate-A sectors. -/
abbrev GlobalPairedIntrinsicAbelianFPGraphSpace
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :=
  PiLp 2 (fun _ : GlobalPairedAbelianLorenzCoordinateIndex =>
    IntrinsicAbelianFPScalarGraphSpace period hPeriod green)

local instance intrinsicAbelianFPScalarGraphCompleteSpace
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    CompleteSpace (IntrinsicAbelianFPScalarGraphSpace period hPeriod green) :=
  canonicalScalarGreenCoreGraphCompleteSpace
    (intrinsicAbelianFaddeevPopovScalarGreenCore period hPeriod green).core

local instance globalPairedIntrinsicAbelianFPGraphNormedSpace
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    NormedSpace Real
      (GlobalPairedIntrinsicAbelianFPGraphSpace period hPeriod green) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedIntrinsicAbelianFPGraphSpace period hPeriod green)).toNormedSpace

local instance globalPairedIntrinsicAbelianFPGraphModule
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    Module Real
      (GlobalPairedIntrinsicAbelianFPGraphSpace period hPeriod green) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedIntrinsicAbelianFPGraphSpace period hPeriod green)
    ).toNormedSpace.toModule

local instance globalPairedIntrinsicAbelianFPTargetNormedSpace :
    NormedSpace Real (GlobalPairedGaugeLieL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedGaugeLieL2 period hPeriod)).toNormedSpace

local instance globalPairedIntrinsicAbelianFPTargetModule :
    Module Real (GlobalPairedGaugeLieL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedGaugeLieL2 period hPeriod)).toNormedSpace.toModule

/-- Assemble a paired smooth `U(1)²` ghost from its four real scalar
components. -/
def globalPairedGaugeLieSmoothOfComponents
    (field : GlobalPairedAbelianLorenzCoordinateIndex →
      SmoothQuotientField period hPeriod Real) :
    GlobalPairedGaugeLieSmooth period hPeriod :=
  fun sector =>
    { toFun := fun point => WithLp.toLp 2 fun component =>
        field (sector, component) point
      contMDiff_toFun := by
        have hComponents : ContMDiff coverModelWithCorners
            (modelWithCornersSelf Real (Fin 2 → Real)) ∞
            (fun point component => field (sector, component) point) := by
          rw [contMDiff_pi_space]
          intro component
          exact (field (sector, component)).contMDiff_toFun
        exact
          (PiLp.continuousLinearEquiv 2 Real
              (fun _ : Fin 2 => Real)).symm.contDiff.contMDiff.comp
            hComponents }

@[simp] theorem ghostComponent_globalPairedGaugeLieSmoothOfComponents
    (field : GlobalPairedAbelianLorenzCoordinateIndex →
      SmoothQuotientField period hPeriod Real)
    (index : GlobalPairedAbelianLorenzCoordinateIndex) :
    ghostComponent period hPeriod
        (globalPairedGaugeLieSmoothOfComponents period hPeriod field index.1)
        index.2 =
      field index := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

/-- Field coordinate of the completed paired FP differential graph. -/
def globalPairedIntrinsicAbelianFPGraphInclusion
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    GlobalPairedIntrinsicAbelianFPGraphSpace period hPeriod green →ₗ[Real]
      GlobalPairedGaugeLieL2 period hPeriod where
  toFun graph := WithLp.toLp 2 fun index =>
    canonicalScalarGreenCoreGraphInclusion
      (intrinsicAbelianFaddeevPopovScalarGreenCore period hPeriod green).core
      (graph index)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact (canonicalScalarGreenCoreGraphInclusion
      (intrinsicAbelianFaddeevPopovScalarGreenCore
        period hPeriod green).core).map_add _ _
  map_smul' scalar graph := by
    apply PiLp.ext
    intro index
    exact (canonicalScalarGreenCoreGraphInclusion
      (intrinsicAbelianFaddeevPopovScalarGreenCore
        period hPeriod green).core).map_smul scalar (graph index)

/-- Operator coordinate of the completed paired FP differential graph. -/
def globalPairedIntrinsicAbelianFPGraphOperator
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    GlobalPairedIntrinsicAbelianFPGraphSpace period hPeriod green →ₗ[Real]
      GlobalPairedGaugeLieL2 period hPeriod where
  toFun graph := WithLp.toLp 2 fun index =>
    canonicalScalarGreenCoreGraphOperator
      (intrinsicAbelianFaddeevPopovScalarGreenCore period hPeriod green).core
      (graph index)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact (canonicalScalarGreenCoreGraphOperator
      (intrinsicAbelianFaddeevPopovScalarGreenCore
        period hPeriod green).core).map_add _ _
  map_smul' scalar graph := by
    apply PiLp.ext
    intro index
    exact (canonicalScalarGreenCoreGraphOperator
      (intrinsicAbelianFaddeevPopovScalarGreenCore
        period hPeriod green).core).map_smul scalar (graph index)

/-- The actual paired smooth ghosts embed componentwise in the completed
differential graph. -/
def globalPairedIntrinsicAbelianFPSmoothToGraph
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    GlobalPairedGaugeLieSmooth period hPeriod →ₗ[Real]
      GlobalPairedIntrinsicAbelianFPGraphSpace period hPeriod green where
  toFun ghost := WithLp.toLp 2 fun index =>
    canonicalScalarGreenCoreToGraph
      (intrinsicAbelianFaddeevPopovScalarGreenCore period hPeriod green).core
      (ghostComponent period hPeriod (ghost index.1) index.2)
  map_add' first second := by
    apply PiLp.ext
    intro index
    change canonicalScalarGreenCoreToGraph _
        (ghostComponent period hPeriod
          (first index.1 + second index.1) index.2) = _
    rw [ghostComponent_add]
    exact map_add _ _ _
  map_smul' scalar ghost := by
    apply PiLp.ext
    intro index
    change canonicalScalarGreenCoreToGraph _
        (ghostComponent period hPeriod
          (scalar • ghost index.1) index.2) = _
    rw [ghostComponent_smul]
    exact map_smul _ _ _

/-- The actual paired smooth ghosts are dense in the finite product of the
four completed scalar FP graphs. -/
theorem globalPairedIntrinsicAbelianFPSmoothToGraph_denseRange
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    DenseRange
      (globalPairedIntrinsicAbelianFPSmoothToGraph
        period hPeriod green) := by
  let scalarMap := fun field :
      GlobalPairedAbelianLorenzCoordinateIndex →
        SmoothQuotientField period hPeriod Real =>
    WithLp.toLp 2 (Pi.map (fun _ :
        GlobalPairedAbelianLorenzCoordinateIndex =>
      canonicalScalarGreenCoreToGraph
        (intrinsicAbelianFaddeevPopovScalarGreenCore
          period hPeriod green).core) field)
  let coordinateEquiv := PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalPairedAbelianLorenzCoordinateIndex =>
      IntrinsicAbelianFPScalarGraphSpace period hPeriod green)
  have hPi : DenseRange (Pi.map fun _ :
      GlobalPairedAbelianLorenzCoordinateIndex =>
        canonicalScalarGreenCoreToGraph
          (intrinsicAbelianFaddeevPopovScalarGreenCore
            period hPeriod green).core) :=
    DenseRange.piMap fun _ =>
      canonicalScalarGreenCoreToGraph_denseRange
        (intrinsicAbelianFaddeevPopovScalarGreenCore
          period hPeriod green).core
  have hCoordinates : DenseRange (coordinateEquiv ∘ scalarMap) := by
    simpa [coordinateEquiv, scalarMap, Function.comp_def, Pi.map,
      PiLp.coe_continuousLinearEquiv] using hPi
  have hScalarMap : DenseRange scalarMap := by
    have hBack :=
      (coordinateEquiv.symm.surjective.denseRange).comp
        hCoordinates coordinateEquiv.symm.continuous
    simpa [coordinateEquiv, scalarMap, Function.comp_def] using hBack
  have hRange :
      Set.range (globalPairedIntrinsicAbelianFPSmoothToGraph
          period hPeriod green) =
        Set.range scalarMap := by
    ext graph
    constructor
    · rintro ⟨ghost, rfl⟩
      refine ⟨fun index => ghostComponent period hPeriod
        (ghost index.1) index.2, ?_⟩
      apply PiLp.ext
      intro index
      rfl
    · rintro ⟨field, rfl⟩
      refine ⟨globalPairedGaugeLieSmoothOfComponents
        period hPeriod field, ?_⟩
      apply PiLp.ext
      intro index
      simp [scalarMap, globalPairedIntrinsicAbelianFPSmoothToGraph]
  rw [DenseRange, hRange]
  exact hScalarMap

/-- The paired graph field coordinate agrees on smooth ghosts with the
existing faithful physical `L²` embedding. -/
theorem globalPairedIntrinsicAbelianFPGraphInclusion_smooth
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedIntrinsicAbelianFPGraphInclusion period hPeriod green
        (globalPairedIntrinsicAbelianFPSmoothToGraph
          period hPeriod green ghost) =
      globalPairedGaugeLieL2LinearMap period hPeriod ghost := by
  apply PiLp.ext
  intro index
  exact canonicalScalarGreenCoreGraphInclusion_smooth
    (intrinsicAbelianFaddeevPopovScalarGreenCore period hPeriod green).core
    (ghostComponent period hPeriod (ghost index.1) index.2)

/-- The paired graph operator coordinate agrees on smooth ghosts with the true
intrinsic Faddeev--Popov map already used by the off-shell BRST chart. -/
theorem globalPairedIntrinsicAbelianFPGraphOperator_smooth
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedIntrinsicAbelianFPGraphOperator period hPeriod green
        (globalPairedIntrinsicAbelianFPSmoothToGraph
          period hPeriod green ghost) =
      globalPairedAbelianFPL2LinearMap period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost := by
  apply PiLp.ext
  intro index
  change canonicalScalarGreenCoreGraphOperator _
      (canonicalScalarGreenCoreToGraph _
        (ghostComponent period hPeriod (ghost index.1) index.2)) = _
  rw [canonicalScalarGreenCoreGraphOperator_smooth]
  exact intrinsicAbelianFaddeevPopovScalarGreenCore_operator_eq_component
    period hPeriod green (ghost index.1) index.2

/-- The completed paired FP differential graph is single-valued.  This is the
finite-product transfer of the already proved componentwise closability. -/
theorem globalPairedIntrinsicAbelianFPGraphInclusion_injective
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    Function.Injective
      (globalPairedIntrinsicAbelianFPGraphInclusion period hPeriod green) := by
  intro first second hEqual
  apply PiLp.ext
  intro index
  exact
    (intrinsicAbelianFaddeevPopovScalarGreenCore_closable_certificate
      period hPeriod green).1
      (congrArg
        (fun value : GlobalPairedGaugeLieL2 period hPeriod => value index)
        hEqual)

/-- Ambient field domain obtained from the first projection of the completed
paired FP graph. -/
def GlobalPairedIntrinsicAbelianFPRealizationDomain
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    Submodule Real (GlobalPairedGaugeLieL2 period hPeriod) :=
  LinearMap.range
    (globalPairedIntrinsicAbelianFPGraphInclusion period hPeriod green)

/-- The completed paired graph is linearly equivalent to its ambient field
domain because its first projection is injective. -/
noncomputable def globalPairedIntrinsicAbelianFPGraphToRealizationDomainEquiv
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    GlobalPairedIntrinsicAbelianFPGraphSpace period hPeriod green ≃ₗ[Real]
      GlobalPairedIntrinsicAbelianFPRealizationDomain
        period hPeriod green :=
  LinearEquiv.ofInjective
    (globalPairedIntrinsicAbelianFPGraphInclusion period hPeriod green)
    (globalPairedIntrinsicAbelianFPGraphInclusion_injective
      period hPeriod green)

/-- Canonical inclusion of the realized FP domain in paired physical `L²`. -/
def globalPairedIntrinsicAbelianFPRealizationInclusion
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    GlobalPairedIntrinsicAbelianFPRealizationDomain period hPeriod green →ₗ[Real]
      GlobalPairedGaugeLieL2 period hPeriod :=
  (GlobalPairedIntrinsicAbelianFPRealizationDomain
    period hPeriod green).subtype

theorem globalPairedIntrinsicAbelianFPRealizationInclusion_injective
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    Function.Injective
      (globalPairedIntrinsicAbelianFPRealizationInclusion
        period hPeriod green) := by
  intro first second hEqual
  exact Subtype.ext hEqual

/-- Genuine single-valued intrinsic paired FP operator on the ambient range of
the completed graph projection. -/
noncomputable def globalPairedIntrinsicAbelianFPRealizationOperator
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    GlobalPairedIntrinsicAbelianFPRealizationDomain period hPeriod green →ₗ[Real]
      GlobalPairedGaugeLieL2 period hPeriod :=
  (globalPairedIntrinsicAbelianFPGraphOperator
      period hPeriod green).comp
    (globalPairedIntrinsicAbelianFPGraphToRealizationDomainEquiv
      period hPeriod green).symm.toLinearMap

/-- Smooth paired ghosts embedded in the realized FP domain. -/
noncomputable def globalPairedIntrinsicAbelianFPSmoothToRealizationDomain
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    GlobalPairedGaugeLieSmooth period hPeriod →ₗ[Real]
      GlobalPairedIntrinsicAbelianFPRealizationDomain
        period hPeriod green :=
  (globalPairedIntrinsicAbelianFPGraphToRealizationDomainEquiv
      period hPeriod green).toLinearMap.comp
    (globalPairedIntrinsicAbelianFPSmoothToGraph period hPeriod green)

@[simp] theorem globalPairedIntrinsicAbelianFPGraphToRealizationDomain_coe
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (graph : GlobalPairedIntrinsicAbelianFPGraphSpace
      period hPeriod green) :
    ((globalPairedIntrinsicAbelianFPGraphToRealizationDomainEquiv
        period hPeriod green graph :
      GlobalPairedIntrinsicAbelianFPRealizationDomain
        period hPeriod green) : GlobalPairedGaugeLieL2 period hPeriod) =
      globalPairedIntrinsicAbelianFPGraphInclusion
        period hPeriod green graph :=
  rfl

@[simp] theorem globalPairedIntrinsicAbelianFPRealizationOperator_equiv
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (graph : GlobalPairedIntrinsicAbelianFPGraphSpace
      period hPeriod green) :
    globalPairedIntrinsicAbelianFPRealizationOperator period hPeriod green
        (globalPairedIntrinsicAbelianFPGraphToRealizationDomainEquiv
          period hPeriod green graph) =
      globalPairedIntrinsicAbelianFPGraphOperator
        period hPeriod green graph := by
  simp [globalPairedIntrinsicAbelianFPRealizationOperator]

/-- The realized inclusion agrees on the smooth core with the existing
faithful paired physical `L²` embedding. -/
theorem globalPairedIntrinsicAbelianFPRealizationInclusion_smooth
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedIntrinsicAbelianFPRealizationInclusion period hPeriod green
        (globalPairedIntrinsicAbelianFPSmoothToRealizationDomain
          period hPeriod green ghost) =
      globalPairedGaugeLieL2LinearMap period hPeriod ghost := by
  exact globalPairedIntrinsicAbelianFPGraphInclusion_smooth
    period hPeriod green ghost

/-- The realized operator agrees on the smooth core with the true intrinsic
paired Faddeev--Popov map. -/
theorem globalPairedIntrinsicAbelianFPRealizationOperator_smooth
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedIntrinsicAbelianFPRealizationOperator period hPeriod green
        (globalPairedIntrinsicAbelianFPSmoothToRealizationDomain
          period hPeriod green ghost) =
      globalPairedAbelianFPL2LinearMap period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost := by
  change globalPairedIntrinsicAbelianFPRealizationOperator
      period hPeriod green
        (globalPairedIntrinsicAbelianFPGraphToRealizationDomainEquiv
          period hPeriod green
          (globalPairedIntrinsicAbelianFPSmoothToGraph
            period hPeriod green ghost)) = _
  rw [globalPairedIntrinsicAbelianFPRealizationOperator_equiv]
  exact globalPairedIntrinsicAbelianFPGraphOperator_smooth
    period hPeriod green ghost

/-- Both coordinates of every completed graph vector are reconstructed by the
single-valued ambient-domain realization. -/
theorem globalPairedIntrinsicAbelianFPRealization_reconstructs_graph
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (graph : GlobalPairedIntrinsicAbelianFPGraphSpace
      period hPeriod green) :
    (globalPairedIntrinsicAbelianFPRealizationInclusion period hPeriod green
        (globalPairedIntrinsicAbelianFPGraphToRealizationDomainEquiv
          period hPeriod green graph),
      globalPairedIntrinsicAbelianFPRealizationOperator period hPeriod green
        (globalPairedIntrinsicAbelianFPGraphToRealizationDomainEquiv
          period hPeriod green graph)) =
      (globalPairedIntrinsicAbelianFPGraphInclusion period hPeriod green graph,
        globalPairedIntrinsicAbelianFPGraphOperator
          period hPeriod green graph) := by
  apply Prod.ext
  · change
      ((globalPairedIntrinsicAbelianFPGraphToRealizationDomainEquiv
          period hPeriod green graph :
        GlobalPairedIntrinsicAbelianFPRealizationDomain
          period hPeriod green) : GlobalPairedGaugeLieL2 period hPeriod) = _
    exact globalPairedIntrinsicAbelianFPGraphToRealizationDomain_coe
      period hPeriod green graph
  · exact globalPairedIntrinsicAbelianFPRealizationOperator_equiv
      period hPeriod green graph

/-- Dense-core, single-valued realization certificate for the intrinsic paired
FP differential graph. -/
theorem globalPairedIntrinsicAbelianFPRealization_certificate
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :
    DenseRange
        (globalPairedIntrinsicAbelianFPSmoothToGraph
          period hPeriod green) ∧
      Function.Injective
        (globalPairedIntrinsicAbelianFPGraphInclusion
          period hPeriod green) ∧
      Function.Injective
        (globalPairedIntrinsicAbelianFPRealizationInclusion
          period hPeriod green) ∧
      (∀ ghost : GlobalPairedGaugeLieSmooth period hPeriod,
        globalPairedIntrinsicAbelianFPRealizationInclusion period hPeriod green
            (globalPairedIntrinsicAbelianFPSmoothToRealizationDomain
              period hPeriod green ghost) =
          globalPairedGaugeLieL2LinearMap period hPeriod ghost) ∧
      ∀ ghost : GlobalPairedGaugeLieSmooth period hPeriod,
        globalPairedIntrinsicAbelianFPRealizationOperator period hPeriod green
            (globalPairedIntrinsicAbelianFPSmoothToRealizationDomain
              period hPeriod green ghost) =
          globalPairedAbelianFPL2LinearMap period hPeriod
            (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost :=
  ⟨globalPairedIntrinsicAbelianFPSmoothToGraph_denseRange
      period hPeriod green,
    globalPairedIntrinsicAbelianFPGraphInclusion_injective
      period hPeriod green,
    globalPairedIntrinsicAbelianFPRealizationInclusion_injective
      period hPeriod green,
    globalPairedIntrinsicAbelianFPRealizationInclusion_smooth
      period hPeriod green,
    globalPairedIntrinsicAbelianFPRealizationOperator_smooth
      period hPeriod green⟩

end
end P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D
end JanusFormal
