namespace JanusFormal
namespace P0EFTCMBProxyPromotionAudit

set_option autoImplicit false

structure CMBProxyPromotionAudit where
  proxyPipelineReady : Prop
  weylSourceValidated : Prop
  visibilityValidated : Prop
  boltzmannHierarchyValidated : Prop
  spectraLikelihoodValidated : Prop

def allProxyReplacementsValidated (a : CMBProxyPromotionAudit) : Prop :=
  a.weylSourceValidated /\
  a.visibilityValidated /\
  a.boltzmannHierarchyValidated /\
  a.spectraLikelihoodValidated

def directCMBPredictionReady (a : CMBProxyPromotionAudit) : Prop :=
  a.proxyPipelineReady /\
  allProxyReplacementsValidated a

theorem proxy_pipeline_alone_does_not_close_direct_cmb
    (a : CMBProxyPromotionAudit)
    (hMissing : Not (allProxyReplacementsValidated a)) :
    Not (directCMBPredictionReady a) := by
  intro h
  exact hMissing h.right

theorem validated_replacements_promote_proxy_pipeline
    (a : CMBProxyPromotionAudit)
    (hProxy : a.proxyPipelineReady)
    (hWeyl : a.weylSourceValidated)
    (hVis : a.visibilityValidated)
    (hBoltz : a.boltzmannHierarchyValidated)
    (hSpectra : a.spectraLikelihoodValidated) :
    directCMBPredictionReady a := by
  exact And.intro hProxy (And.intro hWeyl (And.intro hVis (And.intro hBoltz hSpectra)))

end P0EFTCMBProxyPromotionAudit
end JanusFormal
