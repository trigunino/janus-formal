import JanusFormal.P0EFTJanusZ2SigmaMatterFluxRadialBlockGate
import JanusFormal.P0EFTJanusZ2SigmaCountertermRadialBlockGate
import JanusFormal.P0EFTJanusZ2SigmaRadiusToEmbeddingConditionalClosureGate
import JanusFormal.P0EFTJanusZ2SigmaThroatRadiusBlockDependencyAuditGate
import JanusFormal.P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaThroatRadiusSolutionFrontierGate

set_option autoImplicit false

structure ThroatRadiusSolutionFrontierGate where
  variationalEquationGateImported : Prop
  blockDependencyAuditImported : Prop
  matterFluxRadialBlockImported : Prop
  countertermRadialBlockImported : Prop
  radiusToEmbeddingConditionalClosureImported : Prop
  thinShellRadiusBibliographyChecked : Prop
  noFitSolutionCertificateDeclared : Prop
  variationalEquationReady : Prop
  conditionalEmbeddingMapReady : Prop
  matterFluxBlockReduced : Prop
  countertermBlockReduced : Prop
  allRadialBlocksReduced : Prop
  rSigmaEquationSolved : Prop
  rSigmaOfAReady : Prop
  xPlusMinusUnconditionalReady : Prop

def throatRadiusSolutionFrontierLedgerDeclared
    (g : ThroatRadiusSolutionFrontierGate) : Prop :=
  g.variationalEquationGateImported /\
  g.blockDependencyAuditImported /\
  g.matterFluxRadialBlockImported /\
  g.countertermRadialBlockImported /\
  g.radiusToEmbeddingConditionalClosureImported /\
  g.thinShellRadiusBibliographyChecked /\
  g.noFitSolutionCertificateDeclared

def throatRadiusSolutionCertificateReady
    (g : ThroatRadiusSolutionFrontierGate) : Prop :=
  throatRadiusSolutionFrontierLedgerDeclared g /\
  g.variationalEquationReady /\
  g.matterFluxBlockReduced /\
  g.countertermBlockReduced /\
  g.allRadialBlocksReduced /\
  g.rSigmaEquationSolved /\
  g.rSigmaOfAReady

def embeddingUnblockedByRadiusSolution
    (g : ThroatRadiusSolutionFrontierGate) : Prop :=
  throatRadiusSolutionCertificateReady g /\
  g.conditionalEmbeddingMapReady /\
  g.xPlusMinusUnconditionalReady

theorem radius_solution_certificate_requires_matter_flux_block
    (g : ThroatRadiusSolutionFrontierGate)
    (hReady : throatRadiusSolutionCertificateReady g) :
    g.matterFluxBlockReduced := by
  exact hReady.2.2.1

theorem radius_solution_certificate_requires_counterterm_block
    (g : ThroatRadiusSolutionFrontierGate)
    (hReady : throatRadiusSolutionCertificateReady g) :
    g.countertermBlockReduced := by
  exact hReady.2.2.2.1

end P0EFTJanusZ2SigmaThroatRadiusSolutionFrontierGate
end JanusFormal
