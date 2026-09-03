import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D

/-!
# C² Candidate-A interaction on the paired minimal-physical chart

The exact paired relative matrix is rooted in the completed C² algebra,
inserted into the lifted spectral potential, multiplied by the fixed plus
volume, and integrated.  Exact root rigidity identifies this auxiliary C²
construction with the genuine Candidate-A interaction block.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootJetRigidity4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixC2Exact4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotential4D
open P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

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

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Selected completed root of the exact paired relative matrix. -/
def regularGeneralMetricC2PairedRelativeRoot
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase) : C2Matrix period hPeriod :=
  c2IdentityRootBranch period hPeriod
    (regularGeneralMetricC2PairedRelativeMatrix period hPeriod
      plusBase minusBase core)

theorem regularGeneralMetricC2PairedRelativeRoot_contDiffOn
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC2PairedRelativeRoot period hPeriod
        plusBase minusBase)
      (regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod
        plusBase minusBase) := by
  exact (c2IdentityRootBranch_contDiffOn period hPeriod).comp
    ((regularGeneralMetricC2PairedRelativeMatrix_contDiffOn period hPeriod
      plusBase minusBase).mono (fun _ hCore => hCore.2.1))
    (fun _ hCore => hCore.2.2.2.1)

/-- Completed C² interaction density on the paired relative core. -/
def regularGeneralMetricC2PairedInteractionC2Density
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (core : RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase) : C2Scalar period hPeriod :=
  (-interactionScale) •
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod plusBase.volume)
      (c2MatrixSpectralPotential period hPeriod coefficients
        (regularGeneralMetricC2PairedRelativeRoot period hPeriod
          plusBase minusBase core))

theorem regularGeneralMetricC2PairedInteractionC2Density_contDiffOn
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (regularGeneralMetricC2PairedInteractionC2Density period hPeriod
        plusBase minusBase interactionScale coefficients)
      (regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod
        plusBase minusBase) := by
  have hPotential : ContDiffOn Real 2
      (fun core => c2MatrixSpectralPotential period hPeriod coefficients
        (regularGeneralMetricC2PairedRelativeRoot period hPeriod
          plusBase minusBase core))
      (regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod
        plusBase minusBase) := by
    have hSpectral : ContDiff Real 2
        (c2MatrixSpectralPotential period hPeriod coefficients) :=
      (c2MatrixSpectralPotential_contDiff period hPeriod coefficients).of_le
        (by exact WithTop.coe_le_coe.mpr le_top)
    exact hSpectral.contDiffOn.comp
      (regularGeneralMetricC2PairedRelativeRoot_contDiffOn period hPeriod
        plusBase minusBase) (fun _ _ => Set.mem_univ _)
  exact ((canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        plusBase.volume)).contDiff.contDiffOn.comp hPotential
        (fun _ _ => Set.mem_univ _)).const_smul (-interactionScale)

/-- Finite-measure interaction action on the completed paired core. -/
def regularGeneralMetricC2PairedInteractionC2Action
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (core : RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase) : Real :=
  canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure
    (regularGeneralMetricC2PairedInteractionC2Density period hPeriod
      plusBase minusBase interactionScale coefficients core)

theorem regularGeneralMetricC2PairedInteractionC2Action_contDiffOn
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (regularGeneralMetricC2PairedInteractionC2Action period hPeriod
        plusBase minusBase measure interactionScale coefficients)
      (regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod
        plusBase minusBase) :=
  (canonicalPhysicalC2ScalarIntegralCLM
    period hPeriod measure).contDiff.contDiffOn.comp
      (regularGeneralMetricC2PairedInteractionC2Density_contDiffOn period
        hPeriod plusBase minusBase interactionScale coefficients)
      (fun _ _ => Set.mem_univ _)

/-- On an honest paired direction the completed density is exactly the smooth
interaction density already stored in the Candidate-A datum. -/
theorem regularGeneralMetricC2PairedInteractionC2Density_projected_valueAt
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)
    (hAdmissible : GlobalMetricPerturbationPairLorentzChartAdmissible
      period hPeriod plusBase minusBase
        direction.1.completeVariation.fullMetricPerturbation)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (regularGeneralMetricC2PairedInteractionC2Density period hPeriod
          plusBase minusBase interactionScale coefficients
          (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period
            hPeriod configuration plusBase minusBase direction)) point =
      regularGeneralMetricC2PairedInteractionDensity period hPeriod plusBase
        minusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus)
        (direction.1.completeVariation.fullMetricPerturbation .minus)
        hAdmissible interactionScale coefficients point := by
  unfold regularGeneralMetricC2PairedInteractionC2Density
  rw [c2ScalarSmul_valueAt, c2ScalarProduct_valueAt,
    canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
    c2MatrixSpectralPotential_valueAt]
  unfold regularGeneralMetricC2PairedRelativeRoot
  rw [regularGeneralMetricC2PairedRelativeMatrix_projected_admissible_exact
    period hPeriod configuration plusBase minusBase direction hAdmissible]
  let variedPlus := regularGeneralMetricC2PairedPlusMetric period hPeriod
    plusBase minusBase
      (direction.1.completeVariation.fullMetricPerturbation .plus)
      (direction.1.completeVariation.fullMetricPerturbation .minus)
      hAdmissible
  let relativeTensor := regularGeneralMetricC2PairedRelativeTensor period
    hPeriod plusBase minusBase
      (direction.1.completeVariation.fullMetricPerturbation .plus)
      (direction.1.completeVariation.fullMetricPerturbation .minus)
  have hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod
      variedPlus relativeTensor :=
    (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root period hPeriod
      variedPlus hAdmissible.relative_mem).1
  rw [regularGeneralMetricC2IdentityRoot_eq_smoothMatrixFieldToC2 period
      hPeriod variedPlus relativeTensor hRoot,
    c2FiniteMatrixValueAt_smoothMatrixFieldToC2]
  unfold regularGeneralMetricC2PairedInteractionDensity
  change -interactionScale * (plusBase.volume point * _) =
    -interactionScale * plusBase.volume point * _
  simp only [P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D.regularGeneralMetricC2IdentityRootMatrixField]
  ring

/-- On the exact paired domain the genuine Candidate-A interaction block is
the pullback of the completed C² interaction action. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_eq
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration couplings data plusBase minusBase hBase
        measure).candidateA direction =
      regularGeneralMetricC2PairedInteractionC2Action period hPeriod plusBase
        minusBase measure couplings.interactionScale
          couplings.interactionCoefficients
          (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
            configuration plusBase minusBase direction) := by
  let family :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration couplings data plusBase minusBase
  have hZero : (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) ∈ family.domain :=
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase hBase
  have hDirection' : direction ∈ family.domain := hDirection
  change globalCandidateAInteractionAction period hPeriod
      (family.datumAtTotal period hPeriod 0 hZero direction).2 measure = _
  rw [family.datumAtTotal_of_mem period hPeriod 0 hZero direction hDirection']
  unfold globalCandidateAInteractionAction
    regularGeneralMetricC2PairedInteractionC2Action
  rw [canonicalPhysicalC2ScalarIntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards with point
  exact (regularGeneralMetricC2PairedInteractionC2Density_projected_valueAt
    period hPeriod configuration plusBase minusBase direction hDirection
      couplings.interactionScale couplings.interactionCoefficients point).symm

/-- The completed interaction action remains C² after pullback to the minimal
physical tangent and restriction to the exact paired domain. -/
theorem regularGeneralMetricC2PairedInteractionC2Action_projected_contDiffOn
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    ContDiffOn Real 2
      (fun direction =>
        regularGeneralMetricC2PairedInteractionC2Action period hPeriod
          plusBase minusBase measure couplings.interactionScale
            couplings.interactionCoefficients
            (globalMinimalPhysicalPairedRelativeMetricCoreCLM period hPeriod
              configuration data analysis realization plusBase minusBase
                direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period
        hPeriod configuration.physical plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  exact (regularGeneralMetricC2PairedInteractionC2Action_contDiffOn period
      hPeriod plusBase minusBase measure couplings.interactionScale
        couplings.interactionCoefficients).comp
    (globalMinimalPhysicalPairedRelativeMetricCoreCLM period hPeriod
      configuration data analysis realization plusBase minusBase).contDiff.contDiffOn
    (fun direction hDirection =>
      (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
        period hPeriod configuration.physical plusBase minusBase direction).1
          hDirection)

/-- The genuine Candidate-A interaction block is C² within the exact paired
minimal-physical domain. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_contDiffWithinAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).candidateA
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  have hAux : ContDiffWithinAt Real 2
      (fun direction =>
        regularGeneralMetricC2PairedInteractionC2Action period hPeriod
          plusBase minusBase measure couplings.interactionScale
            couplings.interactionCoefficients
            (globalMinimalPhysicalPairedRelativeMetricCoreCLM period hPeriod
              configuration data analysis realization plusBase minusBase
                direction))
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point :=
    (regularGeneralMetricC2PairedInteractionC2Action_projected_contDiffOn
      period hPeriod configuration data analysis realization plusBase minusBase
        measure).contDiffWithinAt hPoint
  exact hAux.congr_of_mem
    (fun direction hDirection =>
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure direction hDirection)
    hPoint

/-- Gate marker: the interaction member of the five variable physical blocks
is now discharged exactly. -/
theorem regular_general_metric_c2_paired_minimal_physical_interaction_c2_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).candidateA
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  exact regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_contDiffWithinAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
end JanusFormal
