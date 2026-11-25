import SourceV14.Workflow

/-! §4.4. Checked filing of actual transfers to the service guarantee reserve. -/

namespace SourceV14.FidelityServiceReserveChecks

open Workflow ServiceReserve

private def due : PaymentPart := ⟨⟨42, 7, 1, .tutorPay 9⟩, .person 9 none, 30⟩
private def prior : PostedPayment :=
  ⟨5, ⟨due.ref, .person 9, 4, 15, ⟨4, 0⟩⟩, some 11⟩
private def verifiedFees : CurrentLessonFunds where
  lesson := 42
  provider := 3
  checkedAt := ⟨8, 0⟩
  entries := [⟨1, .lessonFees, .spendable, 80, 0, 0⟩,
    ⟨2, .providerFunds, .spendable, 200, 0, 0⟩]
private def account : Account := ⟨verifiedFees, [due], 20, []⟩

/-- From net lesson fees of 80, protect 15 still owed and 20 of spendable
compensation credit. Neither the tutor's earlier receipt nor provider funds add
to the balance transferred to the guarantee reserve. -/
theorem takesOnlyTheAvailableLessonBalance :
    account.transferable { payments := ⟨[prior], [], []⟩, temporary := [], formal := [], lifts := [] } ⟨8, 0⟩ = 45 := by
  decide +kernel

private def original : PaymentPart := { due with amount := 40 }
private def corrected : PaymentPart := { due with ref := { due.ref with portion := 2 } }
private def correction : HoldPartRevision := ⟨original, corrected, 1, 2, ⟨2, 0⟩, ⟨6, 0⟩, ⟨6, 0⟩⟩
private def originalPaid : PostedPayment :=
  ⟨6, ⟨original.ref, .person 9, 4, 20, ⟨4, 0⟩⟩, some 12⟩
private def misdirected : PostedPayment :=
  { originalPaid with instruction := { originalPaid.instruction with destination := .person 99 } }
private def revisedAccount : Account := ⟨verifiedFees, [corrected], 0, []⟩
private def revisedHistory : HoldHistory :=
  { payments := ⟨[originalPaid], [], []⟩, temporary := [], formal := [], lifts := [],
    partRevisions := [correction] }

theorem correctionRetainsActualReceipt :
    revisedAccount.transferable revisedHistory ⟨8, 0⟩ = 70 ∧
    revisedAccount.transferable
      { revisedHistory with payments := ⟨[misdirected], [], []⟩ } ⟨8, 0⟩ = 50 := by
  decide +kernel

theorem correctionNotYetRecordedDoesNotSupplyLineage :
    revisedAccount.transferable
      { revisedHistory with partRevisions := [{ correction with recordedAt := ⟨9, 0⟩ }] }
      ⟨8, 0⟩ = 50 := by
  decide +kernel

theorem rootUsesCorrectedReserveAmount (s after : State) (entry : Filing)
    (accountIs : entry.account = revisedAccount)
    (historyIs : s.holds = revisedHistory)
    (timeIs : entry.transfer.point = ⟨8, 0⟩)
    (edge : Step s (.fileServiceReserve entry) after) : entry.transfer.postedAmount = 70 := by
  cases edge with
  | fileServiceReserve accounted _ _ _ =>
    have amount := accounted.2.2.2.2.2.2.2.2.2.2
    rw [accountIs, historyIs, timeIs] at amount
    exact amount.trans correctionRetainsActualReceipt.1

theorem cannotRepeatTheSameOccurrence (s after : State) (entry earlier : Filing)
    (retained : earlier ∈ s.serviceReserveFilings)
    (sameTime : earlier.transfer.point = entry.transfer.point) :
    ¬Step s (.fileServiceReserve entry) after := by
  intro transitioned
  cases transitioned with
  | fileServiceReserve _ _ _ fresh => exact (fresh earlier retained).2 sameTime

theorem cannotFileWhileAReceivedRefundChoiceIsUnresolved (s after : State) (entry : Filing)
    (request : DirectRefundRequest) (retained : request ∈ s.redress.requests)
    (sameLesson : request.lesson = entry.transfer.lesson)
    (received : request.receivedAt.by entry.transfer.point)
    (outstanding : ∀ assessment ∈ s.redress.assessments,
      AssessedRefund.coversChoice assessment request entry.transfer.point →
      ¬AssessedRefund.completedAt assessment s.review (s.course entry.form.lesson.id)
        entry.transfer.point) :
    ¬Step s (.fileServiceReserve entry) after := by
  intro transitioned
  cases transitioned with
  | fileServiceReserve accounted _ _ _ =>
    have disposed := accounted.2.2.2.2.2.2.2.2.2.1.2.2.2 request retained sameLesson received
    obtain ⟨assessment, found, covers, completed⟩ := disposed
    exact outstanding assessment found covers completed

#print axioms correctionRetainsActualReceipt
#print axioms correctionNotYetRecordedDoesNotSupplyLineage
#print axioms rootUsesCorrectedReserveAmount
#print axioms takesOnlyTheAvailableLessonBalance
#print axioms cannotRepeatTheSameOccurrence
#print axioms cannotFileWhileAReceivedRefundChoiceIsUnresolved

end SourceV14.FidelityServiceReserveChecks
