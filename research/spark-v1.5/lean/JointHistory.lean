import PendingCase
import TNormal
import JointMProof

/-! Joint research history. Frozen declarations are imported and consumed.
M's supplied institutional prehistory is the one used in the locked M3 witness. -/

namespace SparkJoint
open SourceV14 SourceV14.Workflow
open SourceV14.FidelityMaterialsProvisionChecks
open SourceV14.CreditEvidence

private abbrev DirectPath := RecognisedV15.Workflow.Path Step

theorem append {s m t : State} {first rest : List Event}
    (prefixPath : DirectPath s first m) (suffix : DirectPath m rest t) :
    DirectPath s (first ++ rest) t := by
  induction prefixPath with
  | nil => exact suffix
  | next h _ ih => exact .next h (ih suffix)

def receiptMatter : ReviewMatter := ⟨901, 42, [2, 3]⟩

def mAppointment : ReviewAppointment := ⟨receiptMatter, 90, 71, tick 42⟩

/-- In this fixture the authority register names the disinterested handler.
The two right holders have an interest in the receipt decision. -/
def mVerificationAuthority : ReviewAuthorities :=
  { authority with
    interest := fun matter actor _ ↦
      ⟨decide (matter = receiptMatter ∧ (actor = 2 ∨ actor = 3)), false, false, false⟩ }

def eligibleSlot (point : Moment) : Prop :=
  mAppointment.applies mVerificationAuthority receiptMatter 71 point ∧
  (point = tick 44 ∨ point = tick 46)

theorem eligibleEarly : eligibleSlot (tick 44) := by
  refine ⟨⟨rfl, rfl, by decide, ⟨rfl, by decide⟩, ?_⟩, Or.inl rfl⟩
  simp [mVerificationAuthority, receiptMatter, ReviewAuthorities.disinterested, DirectInterest.affected]

theorem eligibleLate : eligibleSlot (tick 46) := by
  refine ⟨⟨rfl, rfl, by decide, ⟨rfl, by decide⟩, ?_⟩, Or.inr rfl⟩
  simp [mVerificationAuthority, receiptMatter, ReviewAuthorities.disinterested, DirectInterest.affected]

theorem payeeNotDisinterested :
    ¬ mVerificationAuthority.disinterested receiptMatter 3 (tick 44) := by
  simp [mVerificationAuthority, receiptMatter, ReviewAuthorities.disinterested, DirectInterest.affected]

def decisions : DecisionRecords :=
  { authorities := authority
    terms := pendingTerms
    appointments := []
    faultOutcomes := []
    faultMatterCovers := fun _ _ ↦ False
    wasResponsibleTutor := fun _ _ ↦ False
    originalAttendanceTime := fun _ _ _ ↦ False }

def commonStart : State :=
  JointM.start 44 (JointT.freshT decisions)
    (JointT.preTopUpCredit JointM.openingPayments JointM.materialAuthority) eligibleSlot

def topped : State :=
  { commonStart with credit :=
      JointT.initialCredit JointM.openingPayments JointM.materialAuthority }

def booked : State := JointT.booked topped

def prefixEvents : List Event :=
  [.credit (.topUp JointT.topUpReceipt JointT.topUpPosting), JointT.bookingEvent]

theorem commonPrefix : DirectPath commonStart prefixEvents booked := by
  refine .next (m := topped) ?_ (.next ?_ (.nil _))
  · exact JointT.topUpStep _ _ _ rfl (by exact ⟨by decide, by decide⟩)
  · refine JointT.bookingStep _ decisions JointM.openingPayments JointM.materialAuthority
      rfl rfl (by exact ⟨by decide, by decide⟩) ?_ ?_ ?_
    · decide +kernel
    · apply JointT.noMaterialBudgetForFreshLesson
      exact JointM.startProvisionsForM 44 (JointT.freshT decisions)
        (JointT.preTopUpCredit JointM.openingPayments JointM.materialAuthority) eligibleSlot
    · apply JointT.noFundingReceiptsBeforeT
      intro row existsInHistory
      change row ∈ ([] : List PostedPayment) at existsInHistory
      simp at existsInHistory

theorem initialReservations : booked.activeReserves = [mInitial, tInitial] := rfl

theorem deliveryReady :
    booked.course JointT.lesson.id = JointT.teachingInput booked.credit decisions :=
  JointT.bookedTeachingInput topped rfl

def delivered : State := JointT.afterTeaching booked

def awaitingVerification : State := pending delivered

theorem pendingBeforeRelease :
    DirectPath commonStart (prefixEvents ++ JointT.teachingEvents ++ [publishEvent, intakeEvent])
      awaitingVerification := by
  refine append (append commonPrefix (JointT.teachingPath booked deliveryReady)) ?_
  exact pendingIntake rfl List.mem_cons_self

def afterPendingReceipt : State := JointM.afterEarlierPayment awaitingVerification

theorem pendingReceiptPath : DirectPath commonStart
    (prefixEvents ++ JointT.teachingEvents ++ [publishEvent, intakeEvent, JointM.earlierPaymentEvent])
    afterPendingReceipt := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append, afterPendingReceipt] using append pendingBeforeRelease
    (.next (JointM.postEarlierPayment awaitingVerification rfl) (.nil _))

theorem checkedPartial : checkedPartialReceipt afterPendingReceipt partialReceipt := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  exact List.mem_cons_self

def checkedAndReleased : State :=
  { afterPendingReceipt with activeReserves := [mInitial, tAt 6] }

def onlyTeachingReleased : State :=
  { afterPendingReceipt with activeReserves := [mInitial, tAt 8] }

def pendingEvents : List Event :=
  prefixEvents ++ JointT.teachingEvents ++ [publishEvent, intakeEvent, JointM.earlierPaymentEvent,
    .reserveReleased pendingRelease (verifiesPendingRelease afterPendingReceipt)]

theorem pendingPath : DirectPath commonStart pendingEvents checkedAndReleased := by
  apply append pendingReceiptPath
  refine .next (releaseWhileTutorDecisionOpen ?_ rfl) (.nil _)
  refine ⟨checkedPartial, rfl, ?_⟩
  simp [authority, pendingMatter, providerCheck, ReviewAuthorities.disinterested,
    DirectInterest.affected]

theorem onlyTeachingPath : DirectPath commonStart
    (prefixEvents ++ JointT.teachingEvents ++ [publishEvent, intakeEvent, JointM.earlierPaymentEvent,
      .reserveReleased teachingOnlyRelease (verifiesTeachingOnlyRelease afterPendingReceipt)])
    onlyTeachingReleased := by
  apply append pendingReceiptPath
  exact .next (releaseAfterTeachingOnly checkedPartial rfl) (.nil _)

/-- Provider cash does not include the customer's separate top-up ledger. The bank's
external debit is from the common provider entry and is not permission to reallocate
encumbered money. The material cash leg is the actual recorded old payment. -/
def grossAtCheck (bank : BankCorrection) : Amount :=
  accountGross JointM.earlierPayment.instruction.amount bank

theorem cashAtCheck :
    grossAtCheck lowerBankCut = 16 ∧ grossAtCheck upperBankCut = 18 ∧
    JointM.earlierPayment.instruction.atTime = tick 40 := by
  exact ⟨accountCuts.1, accountCuts.2.1, JointM.earlierPaymentAmountAndTime.2⟩

abbrev MReady (s : State) := JointM.HasMaterialEvidence s 44 none eligibleSlot

theorem pendingMReady : MReady checkedAndReleased := ⟨rfl, rfl, rfl, rfl⟩
theorem onlyTeachingMReady : MReady onlyTeachingReleased := ⟨rfl, rfl, rfl, rfl⟩
theorem originalProtectionMReady : MReady afterPendingReceipt := ⟨rfl, rfl, rfl, rfl⟩

theorem verify44 {s : State} (ready : MReady s) :
    Step s (JointM.verificationEvent 44) (JointM.afterVerification s 44) :=
  JointM.verifyEarlierPayment s 44 44 ready (by decide) eligibleEarly (by decide) (by decide)

theorem verify46 {s : State} (ready : MReady s) :
    Step s (JointM.verificationEvent 46) (JointM.afterVerification s 46) :=
  JointM.verifyEarlierPayment s 44 46 ready (by decide) eligibleLate (by decide) (by decide)

theorem paymentMenu (s : State) (bank : BankCorrection) (retained : Amount)
    (cut : JointM.ReceiptStatus)
    (ready : JointM.HasMaterialEvidence s 44 cut.point eligibleSlot)
    (reserve : s.activeReserves = [mInitial, tAt retained]) (nonneg : 0 ≤ retained) :
    (∃ next, Step s (JointM.paymentEvent (grossAtCheck bank) retained) next) ↔
      cut.requiredFunds ≤ grossAtCheck bank - retained := by
  constructor
  · rintro ⟨next, step⟩
    by_cases enough : cut.requiredFunds ≤ grossAtCheck bank - retained
    · exact enough
    · exact (JointM.insufficientFundsBlockMaterialsPayment s next 44 cut _ _ ready enough
        step).elim
  · intro enough
    refine ⟨_, JointM.enoughFundsForMaterialsPayment s 44 cut _ _ ready ?_ nonneg enough⟩
    rw [reserve]
    change ((0 : Amount) + retained) ≤ retained
    rw [Rat.zero_add]
    exact Rat.le_refl

theorem earlyPayments {s : State} {history : List Event} {retained : Amount}
    (path : DirectPath commonStart history s) (ready : MReady s)
    (reserve : s.activeReserves = [mInitial, tAt retained]) (nonneg : 0 ≤ retained)
    (enough : 10 ≤ grossAtCheck lowerBankCut - retained) :
    DirectPath commonStart
      (history ++ [JointM.verificationEvent 44, JointM.paymentEvent (grossAtCheck lowerBankCut) retained])
      (JointM.afterPaymentAt45 (JointM.afterVerification s 44) (grossAtCheck lowerBankCut) retained) := by
  apply append path
  refine .next (verify44 ready) (.next ?_ (.nil _))
  refine JointM.enoughFundsForMaterialsPayment _ 44 .verified44 _ _
    (JointM.retainsVerification s 44 44 ready) ?_ nonneg enough
  change Reserves.occupiedElsewhere s.activeReserves _ 1 ≤ retained
  rw [reserve]
  change ((0 : Amount) + retained) ≤ retained
  rw [Rat.zero_add]
  exact Rat.le_refl

theorem pendingPaysAt45 :
    DirectPath commonStart
      (pendingEvents ++ [JointM.verificationEvent 44, JointM.paymentEvent 16 6])
      (JointM.afterPaymentAt45 (JointM.afterVerification checkedAndReleased 44) 16 6) :=
  by simpa only [cashAtCheck.1] using
    earlyPayments pendingPath pendingMReady rfl (by decide) (by decide +kernel)

theorem pendingCannotPayAt45WithoutVerification (next : State) :
    ¬ Step checkedAndReleased (JointM.paymentEvent 16 6) next := by
  exact JointM.insufficientFundsBlockMaterialsPayment _ _ 44 .unverified _ _
    pendingMReady (by decide +kernel)

theorem pendingCanVerifyAt46 :
    DirectPath commonStart (pendingEvents ++ [JointM.verificationEvent 46])
      (JointM.afterVerification checkedAndReleased 46) :=
  append pendingPath (.next (verify46 pendingMReady) (.nil _))

theorem samePendingHistoryInRecognised :
    RecognisedV15.Workflow.Path RecognisedV15.Workflow.Step
      (RecognisedV15.Workflow.State.fromDirect commonStart)
      (pendingEvents ++ [JointM.verificationEvent 44, JointM.paymentEvent 16 6])
      (RecognisedV15.Workflow.State.fromDirect
        (JointM.afterPaymentAt45 (JointM.afterVerification checkedAndReleased 44) 16 6)) :=
  RecognisedV15.Workflow.path_from_direct pendingPaysAt45

#print axioms pendingPath
#print axioms pendingPaysAt45
#print axioms pendingCannotPayAt45WithoutVerification
#print axioms samePendingHistoryInRecognised

end SparkJoint
