namespace JanusFormal
namespace P0EFTCMBCMBPostFixValidityAudit

set_option autoImplicit false

structure CMBPostFixValidityAudit where
  zeroAmplitudeBugRecorded : Prop
  preFixReportsInvalidated : Prop
  postFixReportsSeparated : Prop
  noInvalidatedReportCited : Prop

def validityAuditComplete (a : CMBPostFixValidityAudit) : Prop :=
  a.zeroAmplitudeBugRecorded /\
  a.preFixReportsInvalidated /\
  a.postFixReportsSeparated /\
  a.noInvalidatedReportCited

theorem invalidated_reports_cannot_support_no_fit_claim
    (a : CMBPostFixValidityAudit)
    (h : validityAuditComplete a) :
    a.noInvalidatedReportCited := by
  exact h.right.right.right

end P0EFTCMBCMBPostFixValidityAudit
end JanusFormal
