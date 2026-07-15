import JanusFormal.Branches.JanusCompactObjects.Gates.P0EFTJanusCO01PlugstarSourceAudit
import JanusFormal.Branches.JanusCompactObjects.Gates.P0EFTJanusCOGRBaseline
import JanusFormal.Branches.JanusCompactObjects.Gates.P0EFTJanusCOFutureBimetricInterface
import JanusFormal.Branches.JanusCompactObjects.Gates.P0EFTJanusCORayTracingBinaryGR

namespace JanusFormal
namespace JanusCompactObjects

structure ProgramStatus where
  co01SourceFormulaCore : Prop
  co01PhysicalPlugstarClosure : Prop
  co02GRReference : Prop
  co02StaticBimetricSolution : Prop
  co03GRRadialStabilityDiagnostic : Prop
  co03BimetricRadialStability : Prop
  co04SchwarzschildExteriorObservables : Prop
  co04PhysicalPlugstarObservables : Prop
  co05GRBinaryReference : Prop
  co05JanusBinaryDynamics : Prop
  co06DataComparison : Prop

def programClosed (s : ProgramStatus) : Prop :=
  s.co01SourceFormulaCore ∧
  s.co01PhysicalPlugstarClosure ∧
  s.co02GRReference ∧
  s.co02StaticBimetricSolution ∧
  s.co03GRRadialStabilityDiagnostic ∧
  s.co03BimetricRadialStability ∧
  s.co04SchwarzschildExteriorObservables ∧
  s.co04PhysicalPlugstarObservables ∧
  s.co05GRBinaryReference ∧
  s.co05JanusBinaryDynamics ∧
  s.co06DataComparison

end JanusCompactObjects
end JanusFormal
