import JointHistory
import TFault

namespace SparkJoint
open SourceV14 SourceV14.Workflow
open SourceV14.FidelityMaterialsProvisionChecks
open SourceV14.Course SourceV14.Booking SourceV14.Operations SourceV14.CreditEvidence SourceV14.Settlement

private abbrev DirectPath := RecognisedV15.Workflow.Path Step

def normal := JointT.normalFinal booked decisions

theorem normalPath : DirectPath commonStart (prefixEvents ++ JointT.normalEvents decisions) normal := by
  apply append commonPrefix
  exact JointT.normalPath booked deliveryReady
    ⟨rfl, ⟨by decide, by decide⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl

def normalAfterReceipt := JointM.afterEarlierPayment normal

def normalRelease := release 8 (tick 41) 1181

def verifiesNormalRelease (s : State) (r : Reserves.Release) : Prop :=
  r = normalRelease ∧ s.settlement.fees = [JointT.normalFee decisions] ∧
  s.settlement.tutors = [JointT.normalDue] ∧ s.settlement.tutorPayments = [] ∧
  s.review.intakes = [] ∧ s.redress.remedies = [] ∧ JointT.normalDue.net = 2

def normalReleased : State :=
  { normalAfterReceipt with activeReserves := [mInitial, tAt 2] }

theorem normalReleaseStep : Step normalAfterReceipt
    (.reserveReleased normalRelease (verifiesNormalRelease normalAfterReceipt)) normalReleased := by
  have amount : (10 - (8 : Amount)) = 2 := by decide +kernel
  unfold normalReleased
  rw [← amount]
  refine releaseUpdates (first := [mInitial]) (last := []) rfl rfl ?_ ?_
  · unfold normalRelease release Reserves.Release.matches
    decide +kernel
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def normalEvents : List Event :=
  (prefixEvents ++ JointT.normalEvents decisions) ++ [JointM.earlierPaymentEvent,
    .reserveReleased normalRelease (verifiesNormalRelease normalAfterReceipt)]

theorem normalReservedPath : DirectPath commonStart normalEvents normalReleased := by
  apply append normalPath
  exact .next (JointM.postEarlierPayment normal rfl) (.next normalReleaseStep (.nil _))

theorem normalPaysWithoutEarlyVerification :
    DirectPath commonStart (normalEvents ++ [JointM.paymentEvent 16 2])
      (JointM.afterPaymentAt45 normalReleased 16 2) := by
  apply append normalReservedPath
  exact .next (JointM.enoughFundsForMaterialsPayment _ 44 .unverified 16 2
    ⟨rfl, rfl, rfl, rfl⟩ (by decide +kernel) (by decide) (by decide +kernel)) (.nil _)

theorem normalSameHistoryInRecognised :
    RecognisedV15.Workflow.Path RecognisedV15.Workflow.Step
      (RecognisedV15.Workflow.State.fromDirect commonStart)
      (normalEvents ++ [JointM.paymentEvent 16 2])
      (RecognisedV15.Workflow.State.fromDirect (JointM.afterPaymentAt45 normalReleased 16 2)) :=
  RecognisedV15.Workflow.path_from_direct normalPaysWithoutEarlyVerification

#print axioms normalPaysWithoutEarlyVerification
#print axioms normalSameHistoryInRecognised

def faultStart : State := JointT.afterNotices booked

theorem noticeAndStart :
    DirectPath commonStart (prefixEvents ++ JointT.noticeEvents) faultStart ∧
    faultStart.startPermitted JointT.lesson JointT.schedule JointT.startAt [JointT.place.student] := by
  refine ⟨append commonPrefix (JointT.noticePath booked deliveryReady), ?_⟩
  exact JointT.noticeStartPermitted booked deliveryReady
    (payments := JointM.openingPayments) (authorities := JointM.materialAuthority)
    rfl ⟨by decide, by decide⟩ rfl

theorem faultReady : JointTFault.Ready faultStart := by
  constructor <;> first | rfl | exact ⟨rfl, rfl⟩

def fault := JointTFault.final faultStart

theorem acceptedFaultPath : DirectPath commonStart
    ((prefixEvents ++ JointT.noticeEvents) ++ JointTFault.events faultStart) fault :=
  append noticeAndStart.1 (JointTFault.path _ faultReady)

def faultAfterReceipt := JointM.afterEarlierPayment fault

def faultRelease := release 4 (tick 41) 1182

def verifiesFaultRelease (s : State) (r : Reserves.Release) : Prop :=
  r = faultRelease ∧
    (∃ assessed ∈ s.redress.assessments, assessed.amount.form = JointT.form ∧
      assessed.amount.principal = 2) ∧
    s.redress.remedies ≠ [] ∧
    JointTFault.creditPosting ∈ s.credit.ledger ∧
    refundBalanceDue JointT.place s.credit.ledger (tick 41) 2 (some 1004) = 2 ∧
    balanceBefore s.credit.openingCredit s.credit.ledger 103 (tick 41) = 4

def faultReleased : State :=
  { faultAfterReceipt with activeReserves := [mInitial, tAt 6] }

theorem faultReleaseStep : Step faultAfterReceipt
    (.reserveReleased faultRelease (verifiesFaultRelease faultAfterReceipt)) faultReleased := by
  have newBalance : (10 - (4 : Amount)) = 6 := by decide +kernel
  unfold faultReleased
  rw [← newBalance]
  refine releaseUpdates (first := [mInitial]) (last := []) rfl rfl ?_ ?_
  · unfold faultRelease release Reserves.Release.matches
    decide +kernel
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · change ∃ assessed ∈ [_], _
      exact ⟨_, List.mem_cons_self, rfl, rfl⟩
    · change [_] ≠ []
      simp
    · rw [show faultAfterReceipt.credit.ledger = [JointT.topUpPosting, JointT.debit,
        JointTFault.creditPosting] from JointTFault.ledger _ faultReady]
      simp
    · decide +kernel
    · decide +kernel

def faultEvents : List Event :=
  ((prefixEvents ++ JointT.noticeEvents) ++ JointTFault.events faultStart) ++ [JointM.earlierPaymentEvent,
    .reserveReleased faultRelease (verifiesFaultRelease faultAfterReceipt)]

theorem faultReservedPath : DirectPath commonStart faultEvents faultReleased := by
  apply append acceptedFaultPath
  exact .next (JointM.postEarlierPayment fault rfl) (.next faultReleaseStep (.nil _))

theorem faultPaysAt45 :
    DirectPath commonStart (faultEvents ++ [JointM.verificationEvent 44, JointM.paymentEvent 16 6])
      (JointM.afterPaymentAt45 (JointM.afterVerification faultReleased 44) 16 6) := by
  simpa only [cashAtCheck.1] using
    earlyPayments faultReservedPath ⟨rfl, rfl, rfl, rfl⟩ rfl (by decide) (by decide +kernel)

theorem faultCannotPayAt45WithoutVerification (next : State) :
    ¬ Step faultReleased (JointM.paymentEvent 16 6) next := by
  exact JointM.insufficientFundsBlockMaterialsPayment _ _ 44 .unverified _ _
    ⟨rfl, rfl, rfl, rfl⟩ (by decide +kernel)

theorem faultSameHistoryInRecognised :
    RecognisedV15.Workflow.Path RecognisedV15.Workflow.Step
      (RecognisedV15.Workflow.State.fromDirect commonStart)
      (faultEvents ++ [JointM.verificationEvent 44, JointM.paymentEvent 16 6])
      (RecognisedV15.Workflow.State.fromDirect
        (JointM.afterPaymentAt45 (JointM.afterVerification faultReleased 44) 16 6)) :=
  RecognisedV15.Workflow.path_from_direct faultPaysAt45

#print axioms acceptedFaultPath
#print axioms faultPaysAt45
#print axioms faultSameHistoryInRecognised

end SparkJoint
