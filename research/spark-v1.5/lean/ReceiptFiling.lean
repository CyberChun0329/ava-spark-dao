import RecognisedV15.Workflow

namespace SparkReceiptFiling

open SourceV14 SourceV14.Workflow SourceV14.Workflow.Materials

/-- Administrative filing preserves the availability of every verified material receipt. -/
theorem verifiedReceiptAt_after_filing (history : History) (filed query : PostedPayment)
    (filedAt point : Moment) :
    (history.fileReceipt filed filedAt).hasVerifiedReceiptAt query point =
      history.hasVerifiedReceiptAt query point := by
  simp only [History.fileReceipt, History.hasVerifiedReceiptAt, List.any_map]
  congr 1
  funext entry
  simp only [Function.comp_apply]

  split <;> rfl

/-- Filing changes neither the input receipts nor the recognised cleared-original predicate. -/
theorem paidOriginalCharge_after_filing (history : History) (filed : PostedPayment)
    (filedAt : Moment) (payments : PaymentHistory) (estimate : Operations.PendingMaterialsShare)
    (checkedAt : Moment) (principal : MaterialsPrincipalContext) :
    (history.fileReceipt filed filedAt).paidOriginalCharge payments estimate checkedAt principal =
      history.paidOriginalCharge payments estimate checkedAt principal := by
  unfold History.paidOriginalCharge
  simp only [verifiedReceiptAt_after_filing]
  rfl

#print axioms verifiedReceiptAt_after_filing
#print axioms paidOriginalCharge_after_filing

end SparkReceiptFiling
