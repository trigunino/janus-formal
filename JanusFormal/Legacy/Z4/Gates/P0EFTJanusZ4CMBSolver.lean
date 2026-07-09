import JanusFormal.Legacy.CMB.Gates.P0EFTBiSectorBoltzmannPrototype
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4LinearizedEquation
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4TensorOperatorContract
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4ActionVariationGate
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4LinearizedActionVariation
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4DeterminantMeasureVariation
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4BoundaryVariationClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4FullActionAssemblyTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4NonlinearResidualFactorization
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4ObstructionWardIdentity
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4AnomalyCancellationTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4FullActionWardClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4NonProxyCMBObligations
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4ScalarPerturbationSystem
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4BackgroundClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4BackgroundBianchiIdentity
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4BackgroundActionDerivation
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4ScalarClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4ScalarConservationIdentity
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4ScalarActionDerivation
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PhotonBaryonHierarchyTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PhotonBaryonSourceClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PhotonBaryonIntegratorTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PhotonBaryonNonProxyClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4RecombinationVisibilityTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4VisibilityNormalizationClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4VisibilityNonProxyClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4HierarchyCoefficientClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4IonizationHistoryClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4IonizationEquilibriumSolution
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4IonizationODESolverTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4RecombinationCoefficientClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4NeutrinoHierarchyTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4NeutrinoFreeStreamingClosure
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4LineOfSightSourceTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4LineOfSightIntegratorTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4WeylLensingSourceTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4WeylLensingIntegratorTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4CMBSpectrumAssemblyTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PlanckAdapterContract
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PlanckSpectrumExportGate
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PlanckLikelihoodDryRunTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4PlanckAdapterReadyClosure

namespace JanusFormal
namespace P0EFTJanusZ4CMBSolver

set_option autoImplicit false

abbrev Prototype := P0EFTBiSectorBoltzmannPrototype.BiSectorBoltzmannPrototype
abbrev Z4Equation := P0EFTJanusZ4LinearizedEquation.UnifiedZ4LinearizedEquation
abbrev TensorOperator := P0EFTJanusZ4TensorOperatorContract.DeterminantCoupledTensorOperator
abbrev ActionGate := P0EFTJanusZ4ActionVariationGate.Z4ActionVariationGate
abbrev LinearizedAction :=
  P0EFTJanusZ4LinearizedActionVariation.LinearizedActionVariation
abbrev MeasureVariation :=
  P0EFTJanusZ4DeterminantMeasureVariation.DeterminantMeasureVariation
abbrev BoundaryVariation :=
  P0EFTJanusZ4BoundaryVariationClosure.BoundaryVariationClosure
abbrev FullActionAssembly :=
  P0EFTJanusZ4FullActionAssemblyTarget.FullActionAssemblyTarget
abbrev NonlinearResidual :=
  P0EFTJanusZ4NonlinearResidualFactorization.NonlinearResidualFactorization
abbrev ObstructionWard :=
  P0EFTJanusZ4ObstructionWardIdentity.ObstructionWardIdentity
abbrev AnomalyCancellation :=
  P0EFTJanusZ4AnomalyCancellationTarget.Z4AnomalyCancellationTarget
abbrev FullActionWard :=
  P0EFTJanusZ4FullActionWardClosure.FullActionWardClosure
abbrev CMBObligations := P0EFTJanusZ4NonProxyCMBObligations.NonProxyCMBObligations
abbrev ScalarSystem := P0EFTJanusZ4ScalarPerturbationSystem.ScalarPerturbationSystem
abbrev BackgroundClosure := P0EFTJanusZ4BackgroundClosure.Z4BackgroundClosure
abbrev BackgroundBianchi :=
  P0EFTJanusZ4BackgroundBianchiIdentity.BackgroundBianchiIdentity
abbrev BackgroundAction :=
  P0EFTJanusZ4BackgroundActionDerivation.BackgroundActionDerivation
abbrev ScalarClosure := P0EFTJanusZ4ScalarClosure.Z4ScalarClosure
abbrev ScalarConservation :=
  P0EFTJanusZ4ScalarConservationIdentity.ScalarConservationIdentity
abbrev ScalarAction :=
  P0EFTJanusZ4ScalarActionDerivation.ScalarActionDerivation
abbrev PhotonBaryonTarget :=
  P0EFTJanusZ4PhotonBaryonHierarchyTarget.PhotonBaryonHierarchyTarget
abbrev PhotonBaryonSource :=
  P0EFTJanusZ4PhotonBaryonSourceClosure.PhotonBaryonSourceClosure
abbrev PhotonBaryonIntegrator :=
  P0EFTJanusZ4PhotonBaryonIntegratorTarget.PhotonBaryonIntegratorTarget
abbrev PhotonBaryonNonProxy :=
  P0EFTJanusZ4PhotonBaryonNonProxyClosure.PhotonBaryonNonProxyClosure
abbrev VisibilityTarget :=
  P0EFTJanusZ4RecombinationVisibilityTarget.RecombinationVisibilityTarget
abbrev VisibilityNormalization :=
  P0EFTJanusZ4VisibilityNormalizationClosure.VisibilityNormalizationClosure
abbrev VisibilityNonProxy :=
  P0EFTJanusZ4VisibilityNonProxyClosure.VisibilityNonProxyClosure
abbrev HierarchyCoefficients :=
  P0EFTJanusZ4HierarchyCoefficientClosure.HierarchyCoefficientClosure
abbrev IonizationClosure :=
  P0EFTJanusZ4IonizationHistoryClosure.IonizationHistoryClosure
abbrev IonizationEquilibrium :=
  P0EFTJanusZ4IonizationEquilibriumSolution.IonizationEquilibriumSolution
abbrev IonizationODESolver :=
  P0EFTJanusZ4IonizationODESolverTarget.IonizationODESolverTarget
abbrev RecombinationCoefficients :=
  P0EFTJanusZ4RecombinationCoefficientClosure.RecombinationCoefficientClosure
abbrev NeutrinoTarget := P0EFTJanusZ4NeutrinoHierarchyTarget.NeutrinoHierarchyTarget
abbrev NeutrinoFreeStreaming :=
  P0EFTJanusZ4NeutrinoFreeStreamingClosure.NeutrinoFreeStreamingClosure
abbrev LOSTarget := P0EFTJanusZ4LineOfSightSourceTarget.LineOfSightSourceTarget
abbrev LOSIntegrator :=
  P0EFTJanusZ4LineOfSightIntegratorTarget.LineOfSightIntegratorTarget
abbrev LensingTarget := P0EFTJanusZ4WeylLensingSourceTarget.WeylLensingSourceTarget
abbrev LensingIntegrator :=
  P0EFTJanusZ4WeylLensingIntegratorTarget.WeylLensingIntegratorTarget
abbrev SpectrumAssembly :=
  P0EFTJanusZ4CMBSpectrumAssemblyTarget.CMBSpectrumAssemblyTarget
abbrev PlanckAdapter := P0EFTJanusZ4PlanckAdapterContract.PlanckAdapterContract
abbrev PlanckSpectrumGate :=
  P0EFTJanusZ4PlanckSpectrumExportGate.PlanckSpectrumExportGate
abbrev PlanckDryRun :=
  P0EFTJanusZ4PlanckLikelihoodDryRunTarget.PlanckLikelihoodDryRunTarget
abbrev PlanckAdapterReady :=
  P0EFTJanusZ4PlanckAdapterReadyClosure.PlanckAdapterReadyClosure

def z4ArchitectureReady (p : Prototype) : Prop :=
  P0EFTBiSectorBoltzmannPrototype.prototypeReady p /\
  p.z4UnifiedGeometricOriginEncoded /\
  p.metricSectorsAreZ4Projections /\
  p.independentMetricDynamicsForbidden /\
  p.cmbSolverScaffold95PercentReached

def z4PhysicalPlanckReady (p : Prototype) : Prop :=
  z4ArchitectureReady p /\
  p.fullPhotonBaryonNeutrinoHierarchyValidated /\
  p.planckLikelihoodIntegrated

def z4ArchitectureWithEquationReady (p : Prototype) (e : Z4Equation) : Prop :=
  z4ArchitectureReady p /\
  P0EFTJanusZ4LinearizedEquation.z4ProjectionScaffoldReady e

def z4ArchitectureWithTensorContractReady
    (p : Prototype) (e : Z4Equation) (op : TensorOperator) : Prop :=
  z4ArchitectureWithEquationReady p e /\
  P0EFTJanusZ4TensorOperatorContract.tensorOperatorFromCoupledEquationsReady op

def z4ArchitectureFullScaffoldReady
    (p : Prototype) (e : Z4Equation) (op : TensorOperator)
    (g : ActionGate) (la : LinearizedAction) (m : MeasureVariation)
    (bv : BoundaryVariation) (fa : FullActionAssembly) (nr : NonlinearResidual)
    (ow : ObstructionWard) (ac : AnomalyCancellation) (fw : FullActionWard)
    (s : ScalarSystem) (b : BackgroundClosure) (bb : BackgroundBianchi)
    (ba : BackgroundAction)
    (c : ScalarClosure) (sc : ScalarConservation) (sa2 : ScalarAction)
    (h : PhotonBaryonTarget)
    (pbs : PhotonBaryonSource) (pbi : PhotonBaryonIntegrator)
    (pbn : PhotonBaryonNonProxy)
    (r : VisibilityTarget) (vn : VisibilityNormalization) (vnp : VisibilityNonProxy)
    (hc : HierarchyCoefficients)
    (i : IonizationClosure) (ie : IonizationEquilibrium) (io : IonizationODESolver)
    (rc : RecombinationCoefficients)
    (n : NeutrinoTarget) (nf : NeutrinoFreeStreaming)
    (los : LOSTarget) (losi : LOSIntegrator) (w : LensingTarget)
    (wi : LensingIntegrator)
    (sa : SpectrumAssembly) (pa : PlanckAdapter) (pg : PlanckSpectrumGate)
    (pd : PlanckDryRun) (par : PlanckAdapterReady)
    (o : CMBObligations) : Prop :=
  z4ArchitectureWithTensorContractReady p e op /\
  P0EFTJanusZ4ActionVariationGate.actionVariationScaffoldReady g /\
  P0EFTJanusZ4LinearizedActionVariation.linearizedActionVariationReady la /\
  P0EFTJanusZ4DeterminantMeasureVariation.measureVariationScaffoldReady m /\
  P0EFTJanusZ4BoundaryVariationClosure.boundaryVariationScaffoldReady bv /\
  P0EFTJanusZ4FullActionAssemblyTarget.fullActionAssemblyScaffoldReady fa /\
  P0EFTJanusZ4NonlinearResidualFactorization.residualFactorizationReady nr /\
  P0EFTJanusZ4ObstructionWardIdentity.obstructionWardIdentityReady ow /\
  P0EFTJanusZ4AnomalyCancellationTarget.anomalyCancellationTargetReady ac /\
  P0EFTJanusZ4FullActionWardClosure.fullActionWardClosureReady fw /\
  P0EFTJanusZ4ScalarPerturbationSystem.scalarSystemScaffoldReady s /\
  P0EFTJanusZ4BackgroundClosure.backgroundScaffoldReady b /\
  P0EFTJanusZ4BackgroundBianchiIdentity.backgroundBianchiIdentityReady bb /\
  P0EFTJanusZ4BackgroundActionDerivation.backgroundActionDerivedReady ba /\
  P0EFTJanusZ4ScalarClosure.scalarClosureScaffoldReady c /\
  P0EFTJanusZ4ScalarConservationIdentity.scalarConservationIdentityReady sc /\
  P0EFTJanusZ4ScalarActionDerivation.scalarActionDerivedReady sa2 /\
  P0EFTJanusZ4PhotonBaryonHierarchyTarget.hierarchyTargetReady h /\
  P0EFTJanusZ4PhotonBaryonSourceClosure.photonBaryonSourceClosureReady pbs /\
  P0EFTJanusZ4PhotonBaryonIntegratorTarget.photonBaryonIntegratorReady pbi /\
  P0EFTJanusZ4PhotonBaryonNonProxyClosure.photonBaryonNonProxyClosureReady pbn /\
  P0EFTJanusZ4RecombinationVisibilityTarget.visibilityTargetReady r /\
  P0EFTJanusZ4VisibilityNormalizationClosure.visibilityNormalizationReady vn /\
  P0EFTJanusZ4VisibilityNonProxyClosure.visibilityNonProxyClosureReady vnp /\
  P0EFTJanusZ4HierarchyCoefficientClosure.coefficientScaffoldReady hc /\
  P0EFTJanusZ4IonizationHistoryClosure.ionizationScaffoldReady i /\
  P0EFTJanusZ4IonizationEquilibriumSolution.ionizationEquilibriumReady ie /\
  P0EFTJanusZ4IonizationODESolverTarget.ionizationODESolverReady io /\
  P0EFTJanusZ4RecombinationCoefficientClosure.recombinationCoefficientClosureReady rc /\
  P0EFTJanusZ4NeutrinoHierarchyTarget.neutrinoTargetReady n /\
  P0EFTJanusZ4NeutrinoFreeStreamingClosure.neutrinoFreeStreamingClosureReady nf /\
  P0EFTJanusZ4LineOfSightSourceTarget.losTargetReady los /\
  P0EFTJanusZ4LineOfSightIntegratorTarget.losIntegratorReady losi /\
  P0EFTJanusZ4WeylLensingSourceTarget.weylLensingTargetReady w /\
  P0EFTJanusZ4WeylLensingIntegratorTarget.weylLensingIntegratorReady wi /\
  P0EFTJanusZ4CMBSpectrumAssemblyTarget.spectrumAssemblyReady sa /\
  P0EFTJanusZ4PlanckAdapterContract.adapterContractReady pa /\
  P0EFTJanusZ4PlanckSpectrumExportGate.spectrumExportGateReady pg /\
  P0EFTJanusZ4PlanckLikelihoodDryRunTarget.planckLikelihoodDryRunReady pd /\
  P0EFTJanusZ4PlanckAdapterReadyClosure.planckAdapterReadyClosureReady par /\
  P0EFTJanusZ4NonProxyCMBObligations.nonProxyCMBReady o

theorem architecture_does_not_imply_planck_ready
    (p : Prototype)
    (_hArch : z4ArchitectureReady p)
    (hMissing : Not p.planckLikelihoodIntegrated) :
    Not (z4PhysicalPlanckReady p) := by
  intro h
  exact hMissing h.right.right

theorem equation_scaffold_does_not_imply_planck_ready
    (p : Prototype)
    (e : Z4Equation)
    (_hArch : z4ArchitectureWithEquationReady p e)
    (hMissing : Not p.planckLikelihoodIntegrated) :
    Not (z4PhysicalPlanckReady p) := by
  intro h
  exact hMissing h.right.right

end P0EFTJanusZ4CMBSolver
end JanusFormal
