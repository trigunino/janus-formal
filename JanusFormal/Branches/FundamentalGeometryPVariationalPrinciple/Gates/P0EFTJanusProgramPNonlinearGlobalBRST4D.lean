import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCoadjointAntifieldBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGaugePotentialDiffeomorphismGenerator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMeasuredDensityBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusThroatScalarCoadjointBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPTensorialCoadjointAntifieldBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricGeometricAntifieldDual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricGeometricAntifieldDual4D

/-!
# Unified nonlinear BRST/BV packet

This gate puts the existing exterior-coefficient field complex, the general
metric BV doublet, and its genuine throat trace in one graded packet.  Its
single differential contains the nonlinear `so(3)` ghost rule, is square-zero,
and commutes with restriction to the boundary.

Invariance of an arbitrary assembled action is deliberately exposed as a
contract: the nine Candidate-A blocks still need their common nonlinear
diffeomorphism-naturality theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNonlinearGlobalBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusD8NonabelianGhostKoszul4D
open P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
open P0EFTJanusProgramPCoadjointAntifieldBRST4D
open P0EFTJanusMappingTorusGaugePotentialDiffeomorphismGenerator4D
open P0EFTJanusMappingTorusMeasuredDensityBRST4D
open P0EFTJanusMappingTorusThroatScalarCoadjointBRST4D
open P0EFTJanusProgramPTensorialCoadjointAntifieldBRST4D
open P0EFTJanusProgramPGeneralMetricGeometricAntifieldDual4D
open P0EFTJanusProgramPThroatMetricGeometricAntifieldDual4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- One carrier for all exterior-valued field coordinates, the metric
antifields, and independent boundary variables. -/
structure ProgramPNonlinearBRSTPacket where
  fieldsAndGhosts : LinearFullFieldBRST period hPeriod
  metricFieldsAndAntifields : SmoothGeneralMetricBVField period hPeriod
  boundaryVariables : SmoothThroatGeneralMetricBVField period hPeriod

/-- The grading on the BV slots.  The exterior grading of every ordinary
field/ghost coordinate is the existing coefficient parity. -/
def programPNonlinearBRSTParity
    (packet : ProgramPNonlinearBRSTPacket period hPeriod) :
    ProgramPNonlinearBRSTPacket period hPeriod where
  fieldsAndGhosts := packet.fieldsAndGhosts
  metricFieldsAndAntifields :=
    smoothGeneralMetricBVParity period hPeriod
      packet.metricFieldsAndAntifields
  boundaryVariables := packet.boundaryVariables

/-- The single nonlinear BRST/BV differential on the assembled packet. -/
def programPNonlinearBRST
    (packet : ProgramPNonlinearBRSTPacket period hPeriod) :
    ProgramPNonlinearBRSTPacket period hPeriod where
  fieldsAndGhosts :=
    correctedLinearFullFieldBRST period hPeriod
      (unconditionalLLThroatRotationBRSTCompletion period hPeriod)
      packet.fieldsAndGhosts
  metricFieldsAndAntifields :=
    smoothGeneralMetricBVBRST period hPeriod
      packet.metricFieldsAndAntifields
  boundaryVariables :=
    smoothThroatGeneralMetricBVBRST period hPeriod
      packet.boundaryVariables

/-- Zero packet, stated explicitly because the tensor BV carriers use their
geometric zero constructors. -/
def programPNonlinearBRSTZero :
    ProgramPNonlinearBRSTPacket period hPeriod where
  fieldsAndGhosts := 0
  metricFieldsAndAntifields := smoothGeneralMetricBVZero period hPeriod
  boundaryVariables := smoothThroatGeneralMetricBVZero period hPeriod

/-- The field/ghost component uses the corrected Koszul differential, whose
coefficient part realizes `s c = -1/2 [c,c]`. -/
theorem programPNonlinearBRST_has_nonlinear_ghost_rule :
    (unconditionalSpatialRotationKoszulCoefficientData period hPeriod).differential =
      spatialRotationKoszulDifferential ∧
    ∀ coefficient,
      spatialRotationKoszulDifferential
          (spatialRotationKoszulDifferential coefficient) = 0 := by
  constructor
  · rfl
  · exact spatialRotationKoszulDifferential_square_zero

/-- The unified differential is nilpotent on fields, ghosts, antifields, and
boundary variables simultaneously. -/
theorem programPNonlinearBRST_square_zero
    (packet : ProgramPNonlinearBRSTPacket period hPeriod) :
    programPNonlinearBRST period hPeriod
        (programPNonlinearBRST period hPeriod packet) =
      programPNonlinearBRSTZero period hPeriod := by
  rcases packet with ⟨fields, metricBV, boundaryBV⟩
  change
    { fieldsAndGhosts :=
        correctedLinearFullFieldBRST period hPeriod
          (unconditionalLLThroatRotationBRSTCompletion period hPeriod)
          (correctedLinearFullFieldBRST period hPeriod
            (unconditionalLLThroatRotationBRSTCompletion period hPeriod)
            fields)
      metricFieldsAndAntifields :=
        smoothGeneralMetricBVBRST period hPeriod
          (smoothGeneralMetricBVBRST period hPeriod metricBV)
      boundaryVariables :=
        smoothThroatGeneralMetricBVBRST period hPeriod
          (smoothThroatGeneralMetricBVBRST period hPeriod boundaryBV) } =
      programPNonlinearBRSTZero period hPeriod
  rw [correctedLinearFullFieldBRST_square_zero,
    smoothGeneralMetricBVBRST_square_zero,
    smoothThroatGeneralMetricBVBRST_square_zero]
  rfl

/-- The independent boundary variables agree with the actual metric/BV
throat restriction. -/
def BoundaryCompatible
    (packet : ProgramPNonlinearBRSTPacket period hPeriod) : Prop :=
  packet.boundaryVariables =
    smoothGeneralMetricBVThroatTrace period hPeriod
      packet.metricFieldsAndAntifields

/-- Boundary compatibility is stable under the nonlinear BRST differential. -/
theorem programPNonlinearBRST_boundary_stable
    (packet : ProgramPNonlinearBRSTPacket period hPeriod)
    (hBoundary : BoundaryCompatible period hPeriod packet) :
    BoundaryCompatible period hPeriod
      (programPNonlinearBRST period hPeriod packet) := by
  change smoothThroatGeneralMetricBVBRST period hPeriod
      packet.boundaryVariables =
    smoothGeneralMetricBVThroatTrace period hPeriod
      (smoothGeneralMetricBVBRST period hPeriod
        packet.metricFieldsAndAntifields)
  rw [hBoundary]
  exact smoothGeneralMetricBVThroatTrace_commutes_BRST period hPeriod
    packet.metricFieldsAndAntifields

/-- Precise remaining input for a real assembled action. -/
structure AssembledActionBRSTInvarianceContract
    (action : ProgramPNonlinearBRSTPacket period hPeriod → Real) : Prop where
  invariant :
    ∀ packet,
      action (programPNonlinearBRST period hPeriod packet) = 0

theorem assembled_action_brst_invariant
    (action : ProgramPNonlinearBRSTPacket period hPeriod → Real)
    (contract :
      AssembledActionBRSTInvarianceContract period hPeriod action)
    (packet : ProgramPNonlinearBRSTPacket period hPeriod) :
    action (programPNonlinearBRST period hPeriod packet) = 0 :=
  contract.invariant packet

/-- Closed algebraic and boundary part of the nonlinear BRST frontier. -/
structure ProgramPNonlinearBRSTCertificate4D : Prop where
  squareZero :
    ∀ packet,
      programPNonlinearBRST period hPeriod
          (programPNonlinearBRST period hPeriod packet) =
        programPNonlinearBRSTZero period hPeriod
  boundaryStable :
    ∀ packet,
      BoundaryCompatible period hPeriod packet →
        BoundaryCompatible period hPeriod
          (programPNonlinearBRST period hPeriod packet)
  nonlinearGhostRule :
    (unconditionalSpatialRotationKoszulCoefficientData
      period hPeriod).differential =
        spatialRotationKoszulDifferential
  tensorialFiniteRepresentation :
    TensorialDiffeomorphismRepresentationCertificate4D period hPeriod
  scalarInfinitesimalRepresentation :
    ∀ first second scalar,
      lieRepresentationBRSTPairObstruction period hPeriod
        (smoothScalarGhostLieRepresentation period hPeriod)
        first second scalar = 0
  scalarCoadjointAntifieldRepresentation :
    ∀ first second antifield,
      lieRepresentationBRSTPairObstruction period hPeriod
        (smoothScalarFieldAntifieldLieRepresentation
          period hPeriod).antifield first second antifield = 0
  scalarFieldAntifieldPairingInvariant :
    ∀ ghost antifield scalar,
      fieldAntifieldPairing
          (coadjointGhostAction period hPeriod
            (smoothScalarGhostLieRepresentation period hPeriod)
            ghost antifield) scalar +
        fieldAntifieldPairing antifield
          ((smoothScalarGhostLieRepresentation period hPeriod).action
            ghost scalar) = 0
  measuredDensityClosure :
    MeasuredDensityBRSTCertificate4D period hPeriod
  throatScalarCoadjointClosure :
    ThroatScalarCoadjointBRSTCertificate4D period hPeriod
  metricGeometricAntifieldDual :
    GeneralMetricGeometricAntifieldDualCertificate4D period hPeriod
  throatMetricGeometricAntifieldDual :
    ThroatMetricGeometricAntifieldDualCertificate4D period hPeriod

def programPNonlinearBRSTCertificate4D :
    ProgramPNonlinearBRSTCertificate4D period hPeriod where
  squareZero := programPNonlinearBRST_square_zero period hPeriod
  boundaryStable := programPNonlinearBRST_boundary_stable period hPeriod
  nonlinearGhostRule :=
    (programPNonlinearBRST_has_nonlinear_ghost_rule period hPeriod).1
  tensorialFiniteRepresentation :=
    tensorialDiffeomorphismRepresentationCertificate4D period hPeriod
  scalarInfinitesimalRepresentation :=
    scalar_geometric_nonlinear_brst_pair_square_zero period hPeriod
  scalarCoadjointAntifieldRepresentation :=
    scalar_algebraic_antifield_brst_pair_square_zero period hPeriod
  scalarFieldAntifieldPairingInvariant :=
    scalar_field_antifield_pairing_brst_invariant period hPeriod
  measuredDensityClosure :=
    measuredDensityBRSTCertificate4D period hPeriod
  throatScalarCoadjointClosure :=
    throatScalarCoadjointBRSTCertificate4D period hPeriod
  metricGeometricAntifieldDual :=
    generalMetricGeometricAntifieldDualCertificate4D period hPeriod
  throatMetricGeometricAntifieldDual :=
    throatMetricGeometricAntifieldDualCertificate4D period hPeriod

/-- Any genuine Maxwell/metric Lie-action datum canonically closes both
tensorial algebraic antifield sectors. -/
theorem programP_tensorial_coadjoint_antifield_gate
    (actions : TensorialInfinitesimalLieActionData period hPeriod) :
    TensorialCoadjointAntifieldBRSTCertificate4D
      period hPeriod actions :=
  tensorialCoadjointAntifieldBRSTCertificate4D
    period hPeriod actions

end
end P0EFTJanusProgramPNonlinearGlobalBRST4D
end JanusFormal
