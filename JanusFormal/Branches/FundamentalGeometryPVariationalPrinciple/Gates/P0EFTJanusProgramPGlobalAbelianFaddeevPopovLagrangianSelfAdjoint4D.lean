import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetDirectAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphMinimalProgramPClosure4D

/-!
# Conditional Lagrangian self-adjoint realization of the intrinsic Abelian FP operator

The existing completed scalar boundary triple is applied directly to the
mass-zero scalar Green core already identified with every intrinsic Abelian
Faddeev--Popov component.  Given the existing completed-boundary inputs and
analytic-closure package, each of the four real FP components has dense domain
and equality of its actual Hilbert-adjoint domain with its realization domain.

The finite paired domain and its inclusion/operator are assembled without a
second ghost space.  On the admitted smooth boundary core they agree exactly
with the existing faithful ghost `L²` inclusion and the true intrinsic FP map.

The pre-existing graph/direct-coercive Program P endpoint gives a sharper
route: its local-divergence datum reconstructs the global Green datum with the
same scalar core; its bounded real resolvent gives actual adjoint-domain
equality; and its admitted smooth realization is exactly the FP component.
No inhabitant of either remaining analytic data package is constructed here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalAbelianFaddeevPopovLagrangianSelfAdjoint4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetDirectAnalyticClosure4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphMinimalProgramPClosure4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianFaddeevPopovScalarBridge4D
open P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev FPScalarData
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :=
  intrinsicAbelianFaddeevPopovScalarGreenCore period hPeriod green

/-- The already defined completed graph bound, specialized to the intrinsic
mass-zero FP scalar core. -/
def intrinsicAbelianFPScalarTraceBound
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod) :=
  inputs.traceBound period hPeriod (FPScalarData period hPeriod green)

/-- The existing completed scalar boundary triple, now based on the exact
intrinsic FP scalar core. -/
def intrinsicAbelianFPScalarCompletedTriple
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod) :=
  inputs.triple period hPeriod (FPScalarData period hPeriod green)

/-- One component domain for a supplied closed Lagrangian boundary condition. -/
abbrev IntrinsicAbelianFPScalarLagrangianDomain
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period)) :=
  (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
    ).lagrangianDomainSubmodule condition

/-- The supplied analytic package makes the FP scalar realization dense in the
physical bulk `L²` space. -/
theorem intrinsicAbelianFPScalarLagrangianInclusion_denseRange
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period))
    (analytic : (intrinsicAbelianFPScalarCompletedTriple
      period hPeriod green inputs).LagrangianAnalyticClosureData condition) :
    DenseRange
      ((intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
        ).lagrangianInclusion condition) :=
  analytic.denseDomain
    (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs)
    condition

/-- Conditional actual Hilbert self-adjointness of one intrinsic FP scalar
component, expressed by equality of adjoint and realization domains. -/
theorem intrinsicAbelianFPScalar_actualAdjointDomain_eq
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period))
    (analytic : (intrinsicAbelianFPScalarCompletedTriple
      period hPeriod green inputs).LagrangianAnalyticClosureData condition) :
    (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
        ).actualAdjointDomain condition =
      (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
        ).realizationDomain condition :=
  analytic.actualAdjointDomain_eq
    (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs)
    condition

/-- Finite domain of all four real `Sector × Fin 2` FP components. -/
abbrev GlobalPairedIntrinsicAbelianFPLagrangianDomain
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period)) :=
  GlobalPairedAbelianLorenzCoordinateIndex →
    IntrinsicAbelianFPScalarLagrangianDomain period hPeriod green inputs
      condition

/-- Coordinatewise ambient inclusion of the paired Lagrangian domain. -/
def globalPairedIntrinsicAbelianFPLagrangianInclusion
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period)) :
    GlobalPairedIntrinsicAbelianFPLagrangianDomain period hPeriod green inputs
        condition →ₗ[Real]
      GlobalPairedGaugeLieL2 period hPeriod where
  toFun field := WithLp.toLp 2 fun index =>
    (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
      ).lagrangianInclusion condition (field index)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact ((intrinsicAbelianFPScalarCompletedTriple
      period hPeriod green inputs).lagrangianInclusion condition).map_add
        (first index) (second index)
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact ((intrinsicAbelianFPScalarCompletedTriple
      period hPeriod green inputs).lagrangianInclusion condition).map_smul
        scalar (field index)

/-- Coordinatewise intrinsic FP operator on the paired Lagrangian domain. -/
def globalPairedIntrinsicAbelianFPLagrangianOperator
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period)) :
    GlobalPairedIntrinsicAbelianFPLagrangianDomain period hPeriod green inputs
        condition →ₗ[Real]
      GlobalPairedGaugeLieL2 period hPeriod where
  toFun field := WithLp.toLp 2 fun index =>
    (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
      ).lagrangianOperator condition (field index)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact ((intrinsicAbelianFPScalarCompletedTriple
      period hPeriod green inputs).lagrangianOperator condition).map_add
        (first index) (second index)
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact ((intrinsicAbelianFPScalarCompletedTriple
      period hPeriod green inputs).lagrangianOperator condition).map_smul
        scalar (field index)

theorem globalPairedIntrinsicAbelianFPLagrangianInclusion_injective
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period)) :
    Function.Injective
      (globalPairedIntrinsicAbelianFPLagrangianInclusion period hPeriod green
        inputs condition) := by
  intro first second hEqual
  funext index
  apply (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
    ).lagrangianInclusion_injective condition
  exact congrArg (fun value : GlobalPairedGaugeLieL2 period hPeriod =>
    value index) hEqual

/-- The finite paired domain is dense because every scalar Lagrangian
realization is dense. -/
theorem globalPairedIntrinsicAbelianFPLagrangianInclusion_denseRange
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period))
    (analytic : (intrinsicAbelianFPScalarCompletedTriple
      period hPeriod green inputs).LagrangianAnalyticClosureData condition) :
    DenseRange
      (globalPairedIntrinsicAbelianFPLagrangianInclusion period hPeriod green
        inputs condition) := by
  let coordinateEquiv := PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalPairedAbelianLorenzCoordinateIndex =>
      CanonicalPhysicalBulkL2 period hPeriod)
  have hPi : DenseRange (Pi.map fun _ :
      GlobalPairedAbelianLorenzCoordinateIndex =>
        (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
          ).lagrangianInclusion condition) :=
    DenseRange.piMap fun _ =>
      intrinsicAbelianFPScalarLagrangianInclusion_denseRange
        period hPeriod green inputs condition analytic
  have hCoordinates : DenseRange (coordinateEquiv ∘
      globalPairedIntrinsicAbelianFPLagrangianInclusion
        period hPeriod green inputs condition) := by
    change DenseRange (Pi.map fun _ :
      GlobalPairedAbelianLorenzCoordinateIndex =>
        (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
          ).lagrangianInclusion condition)
    exact hPi
  have hBack :=
    (coordinateEquiv.symm.surjective.denseRange).comp
      hCoordinates coordinateEquiv.symm.continuous
  simpa [coordinateEquiv, Function.comp_def] using hBack

/-- Smooth paired ghosts whose completed scalar graph traces lie in the
selected Lagrangian condition componentwise. -/
def GlobalPairedIntrinsicAbelianFPSmoothLagrangianCore
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period)) :=
  { ghost : GlobalPairedGaugeLieSmooth period hPeriod //
    ∀ index : GlobalPairedAbelianLorenzCoordinateIndex,
      canonicalScalarGreenCoreToGraph
          (FPScalarData period hPeriod green).core
          (ghostComponent period hPeriod (ghost index.1) index.2) ∈
        (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
          ).lagrangianDomainSubmodule condition }

/-- Admitted smooth ghosts inserted into the paired Lagrangian domain. -/
def globalPairedIntrinsicAbelianFPSmoothToLagrangianDomain
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period))
    (ghost : GlobalPairedIntrinsicAbelianFPSmoothLagrangianCore
      period hPeriod green inputs condition) :
    GlobalPairedIntrinsicAbelianFPLagrangianDomain period hPeriod green inputs
      condition :=
  fun index => ⟨
    canonicalScalarGreenCoreToGraph
      (FPScalarData period hPeriod green).core
      (ghostComponent period hPeriod (ghost.1 index.1) index.2),
    ghost.2 index⟩

/-- On its admitted smooth core the paired Lagrangian inclusion is the existing
faithful physical ghost `L²` inclusion. -/
theorem globalPairedIntrinsicAbelianFPLagrangianInclusion_smooth
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period))
    (ghost : GlobalPairedIntrinsicAbelianFPSmoothLagrangianCore
      period hPeriod green inputs condition) :
    globalPairedIntrinsicAbelianFPLagrangianInclusion period hPeriod green
        inputs condition
        (globalPairedIntrinsicAbelianFPSmoothToLagrangianDomain
          period hPeriod green inputs condition ghost) =
      globalPairedGaugeLieL2LinearMap period hPeriod ghost.1 := by
  apply PiLp.ext
  intro index
  exact canonicalScalarGreenCoreGraphInclusion_smooth
    (FPScalarData period hPeriod green).core
    (ghostComponent period hPeriod (ghost.1 index.1) index.2)

/-- On its admitted smooth core the paired Lagrangian operator is exactly the
true intrinsic FP operator already present in the off-shell BRST chart. -/
theorem globalPairedIntrinsicAbelianFPLagrangianOperator_smooth
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period))
    (ghost : GlobalPairedIntrinsicAbelianFPSmoothLagrangianCore
      period hPeriod green inputs condition) :
    globalPairedIntrinsicAbelianFPLagrangianOperator period hPeriod green
        inputs condition
        (globalPairedIntrinsicAbelianFPSmoothToLagrangianDomain
          period hPeriod green inputs condition ghost) =
      globalPairedAbelianFPL2LinearMap period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost.1 := by
  apply PiLp.ext
  intro index
  change (FPScalarData period hPeriod green).core.operator
      (ghostComponent period hPeriod (ghost.1 index.1) index.2) = _
  exact intrinsicAbelianFaddeevPopovScalarGreenCore_operator_eq_component
    period hPeriod green (ghost.1 index.1) index.2

/-- All four real FP components inherit the same conditional actual-adjoint
domain equality. -/
theorem globalPairedIntrinsicAbelianFP_componentwise_actualAdjointDomain_eq
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period))
    (analytic : (intrinsicAbelianFPScalarCompletedTriple
      period hPeriod green inputs).LagrangianAnalyticClosureData condition) :
    ∀ _ : GlobalPairedAbelianLorenzCoordinateIndex,
      (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
          ).actualAdjointDomain condition =
        (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
          ).realizationDomain condition :=
  fun _ => intrinsicAbelianFPScalar_actualAdjointDomain_eq
    period hPeriod green inputs condition analytic

/-- Conditional paired FP Lagrangian-realization certificate. -/
theorem globalPairedIntrinsicAbelianFPLagrangian_certificate
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (CanonicalPhysicalScalarFirstSheetL2 period))
    (analytic : (intrinsicAbelianFPScalarCompletedTriple
      period hPeriod green inputs).LagrangianAnalyticClosureData condition) :
    DenseRange
        (globalPairedIntrinsicAbelianFPLagrangianInclusion period hPeriod green
          inputs condition) ∧
      Function.Injective
        (globalPairedIntrinsicAbelianFPLagrangianInclusion period hPeriod green
          inputs condition) ∧
      (∀ _ : GlobalPairedAbelianLorenzCoordinateIndex,
        (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
            ).actualAdjointDomain condition =
          (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
            ).realizationDomain condition) :=
  ⟨globalPairedIntrinsicAbelianFPLagrangianInclusion_denseRange
      period hPeriod green inputs condition analytic,
    globalPairedIntrinsicAbelianFPLagrangianInclusion_injective
      period hPeriod green inputs condition,
    globalPairedIntrinsicAbelianFP_componentwise_actualAdjointDomain_eq
      period hPeriod green inputs condition analytic⟩

/-- The existing direct physical analytic package supplies the generic closure
data required by the paired FP certificate. -/
theorem globalPairedIntrinsicAbelianFPLagrangian_certificate_of_directAnalytic
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0)
    (inputs : (FPScalarData period hPeriod green).CompletedBoundaryTripleInputs
      period hPeriod)
    (analytic : CanonicalPhysicalScalarFirstSheetDirectAnalyticData
      period hPeriod (FPScalarData period hPeriod green) inputs) :
    DenseRange
        (globalPairedIntrinsicAbelianFPLagrangianInclusion period hPeriod green
          inputs analytic.condition) ∧
      Function.Injective
        (globalPairedIntrinsicAbelianFPLagrangianInclusion period hPeriod green
          inputs analytic.condition) ∧
      (∀ _ : GlobalPairedAbelianLorenzCoordinateIndex,
        (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
            ).actualAdjointDomain analytic.condition =
          (intrinsicAbelianFPScalarCompletedTriple period hPeriod green inputs
            ).realizationDomain analytic.condition) :=
  globalPairedIntrinsicAbelianFPLagrangian_certificate period hPeriod green
    inputs analytic.condition (analytic.toGeneric period hPeriod)

/-- The minimal Program P PDE endpoint already reconstructs the global
Green--Stokes datum required by the earlier FP adapter. -/
def intrinsicAbelianFPGraphMinimalGreen
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod 0) :
    CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0 :=
  CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData.ofCanonicalLocalDivergenceData
    period hPeriod
      ((analytic.boundary.geometric.toCanonicalNormalSplitData period hPeriod
        ).toCanonicalLocalDivergenceData period hPeriod)

/-- The reconstructed datum uses exactly the Green core already carried by the
minimal Program P endpoint. -/
theorem intrinsicAbelianFPGraphMinimalGreen_scalarCore_eq
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod 0) :
    intrinsicAbelianFaddeevPopovScalarGreenCore period hPeriod
        (intrinsicAbelianFPGraphMinimalGreen period hPeriod analytic) =
      analytic.boundary.geometric.greenCore period hPeriod := by
  rfl

/-- The mass-zero operator in the existing graph/direct-coercive Program P
endpoint is exactly one intrinsic Abelian FP component on smooth ghosts. -/
theorem intrinsicAbelianFPGraphMinimal_coreOperator_eq_component
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod 0)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) :
    (analytic.boundary.geometric.greenCore period hPeriod).core.operator
        (ghostComponent period hPeriod ghost component) =
      globalGaugeLieFieldL2Coordinates period hPeriod
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost)
        component := by
  rw [intrinsicAbelianFaddeevPopov_component_l2_eq_scalarOperator]
  rfl

/-- On every admitted smooth Lagrangian vector, the existing minimal Program P
realization is the true intrinsic FP component. -/
theorem intrinsicAbelianFPGraphMinimal_lagrangianOperator_smooth
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod 0)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2)
    (hBoundary : canonicalScalarGreenCoreToGraph
        (analytic.boundary.geometric.greenCore period hPeriod).core
        (ghostComponent period hPeriod ghost component) ∈
      analytic.boundary.triple.lagrangianDomainSubmodule analytic.condition) :
    analytic.boundary.triple.lagrangianOperator analytic.condition
        ⟨canonicalScalarGreenCoreToGraph
            (analytic.boundary.geometric.greenCore period hPeriod).core
            (ghostComponent period hPeriod ghost component),
          hBoundary⟩ =
      globalGaugeLieFieldL2Coordinates period hPeriod
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost)
        component := by
  change (analytic.boundary.geometric.greenCore period hPeriod).core.operator
      (ghostComponent period hPeriod ghost component) = _
  exact intrinsicAbelianFPGraphMinimal_coreOperator_eq_component
    period hPeriod analytic ghost component

/-- The already implemented graph/direct-coercive endpoint therefore supplies
actual scalar FP self-adjointness plus exact smooth-core identification. -/
theorem intrinsicAbelianFPGraphMinimal_selfAdjoint_certificate
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod 0) :
    DenseRange
        (analytic.boundary.triple.lagrangianInclusion analytic.condition) ∧
      analytic.boundary.triple.actualAdjointDomain analytic.condition =
          analytic.boundary.triple.realizationDomain analytic.condition ∧
      ∀ (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
        (component : Fin 2)
        (hBoundary : canonicalScalarGreenCoreToGraph
            (analytic.boundary.geometric.greenCore period hPeriod).core
            (ghostComponent period hPeriod ghost component) ∈
          analytic.boundary.triple.lagrangianDomainSubmodule analytic.condition),
        analytic.boundary.triple.lagrangianOperator analytic.condition
            ⟨canonicalScalarGreenCoreToGraph
                (analytic.boundary.geometric.greenCore period hPeriod).core
                (ghostComponent period hPeriod ghost component),
              hBoundary⟩ =
          globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianFaddeevPopov period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost)
            component :=
  ⟨analytic.denseDomain period hPeriod,
    analytic.actualAdjointDomain_eq period hPeriod,
    fun ghost component hBoundary =>
      intrinsicAbelianFPGraphMinimal_lagrangianOperator_smooth
        period hPeriod analytic ghost component hBoundary⟩

end
end P0EFTJanusProgramPGlobalAbelianFaddeevPopovLagrangianSelfAdjoint4D
end JanusFormal
