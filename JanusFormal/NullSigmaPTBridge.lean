/- Active alternative facade for the Janus Z2 null-Sigma/PT-bridge branch.

Build explicitly:
  lake build JanusFormal.NullSigmaPTBridge

This branch follows the chapter-6 PT bridge reading of the Janus reference:
cross-term retained, one-way membrane, null/degenerate throat accepted.
It is intentionally separate from `JanusFormal.ActiveZ2Sigma`, whose regular
Sigma pipeline assumes invertible h_ab and standard K_ab/GHY data.
-/

import JanusFormal.P0EFTJanusZ2SO3EddingtonCrossTermCollarDiagnosticGate
import JanusFormal.P0EFTJanusZ2NullSigmaPTBridgeSourceAlignmentGate
import JanusFormal.P0EFTJanusZ2NullSigmaBoundaryVariablesGate
import JanusFormal.P0EFTJanusZ2NullSigmaActionVariationGate
import JanusFormal.P0EFTJanusZ2NullSigmaVariationReductionGate
import JanusFormal.P0EFTJanusZ2NullSigmaPTJointGate
import JanusFormal.P0EFTJanusZ2NullSigmaBarrabesIsraelGate
import JanusFormal.P0EFTJanusZ2NullSigmaBranchVerdictGate
