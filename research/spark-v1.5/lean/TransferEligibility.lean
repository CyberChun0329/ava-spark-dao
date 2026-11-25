import RecognisedV15.Workflow

/-! A two-person research case for the transfer terms and qualification checks of v1.5.
The 0/50 sensitivity of each judgement, the roster, absences of other interests,
time slots, fees and protected amounts are independent inputs of the fork. -/

namespace TransferCase

open SourceV14
open SourceV14.Confirmation

inductive Expert where | O | N deriving DecidableEq, Repr
inductive Task where | teaching | oldReview deriving DecidableEq, Repr
inductive Policy where | retain | assign deriving DecidableEq, Repr

def who : Expert → ActorId | .O => 40 | .N => 31
def tick (n : Nat) : Moment := ⟨n, 0⟩
def mat : MaterialId := 7
def seat : PlaceId := 1
def lessonId : Task → LessonId | .teaching => 100 | .oldReview => 90
def ref : Task → String | .teaching => "C1 material" | .oldReview => "C0 material"
def matter (q : Task) : ReviewMatter := ⟨lessonId q, lessonId q, [who .O, who .N]⟩
def lesson (q : Task) : Lesson := ⟨lessonId q, .oneToOne, 10, 20, 30, 2⟩

def sole (material : MaterialId) (expert : Expert) : MaterialsAllocation material :=
  ⟨if expert = .O then "signed O allocation" else "signed N allocation", [who expert],
    fun _ _ base ↦ base⟩

def agreement (q : Task) : MaterialsTerms where
  lesson := lessonId q
  adoptedBy := 10
  agreedAt := tick 0
  agreementReference := "agreed material terms"
  accountingAndPaymentParty := 10
  materialsOrBundle := "contribution"
  contact := "coordinator"
  licensedUse := (· = mat)
  sharesAndAdjustmentsReference := "initial sole O allocation"
  sharesInForce := fun m _ ↦ some (sole m .O)
  contributors := fun _ ↦ [who .O]
  consents := [⟨mat, who .O, "agreed material terms", tick 0⟩]
  ordinaryShareTime := fun _ _ firstUse _ ↦ firstUse
  paymentDue := tick 65
  paymentDeadline := tick 72
  pricing := .standardBundle [⟨mat, 1 / 10⟩]

def oldReceipt : PostedPayment :=
  ⟨501, ⟨⟨lessonId .oldReview, 501, 1, .materialsShare mat (who .O)⟩,
    .person (who .O), 10, 50, tick 28⟩, some 1501⟩

def wage : PaymentPart := ⟨⟨89, 580, 1, .tutorPay 81⟩, .person 81 none, 80⟩
def wageTerms : PaymentTerms := ⟨.fixed (tick 25), .fixed (tick 29)⟩
def openingPayments : PaymentHistory := ⟨[oldReceipt], [], []⟩

/-- These are two signed O-to-N documents of disjoint scope. The first governs only C1;
the optional second governs the C0 shortfall. Both parties' assent is supplied data. -/
def signedRow (q : Task) : SourceV14.Workflow.Materials.Transfer :=
  let atTime := match q with | .teaching => tick 40 | .oldReview => tick 42
  let title := match q with | .teaching => "O/N C1" | .oldReview => "O/N C0 supplement"
  let rights : MaterialsTransfer mat :=
    ⟨who .O, who .N, .voluntaryTransfer, atTime,
      if q = .teaching then .otherwiseAgreed (sole mat .N) else .sharesAtFirstUse,
      sole mat .O, if q = .oldReview then sole mat .N else sole mat .O⟩
  let signedBy : List ActorId := [who .O, who .N]
  { material := mat
    record :=
      { transfer := rights
        reference := title
        verifiedTerms := fun document content ↦
          document = title ∧ content = rights ∧ who .O ∈ signedBy ∧ who .N ∈ signedBy
        transferorShareTime := tick 1
        applicableOwnershipTime := (· = tick 1)
        voluntary := who .O ∈ signedBy
        publishedTermsSatisfied := True
        governs := fun lid identity place ↦ lid = lessonId q ∧ identity = ref q ∧ place = seat
        originalCollections := fun lid identity place ↦
          if q = .oldReview ∧ lid = lessonId q ∧ identity = ref q ∧ place = seat then
            [⟨who .O, oldReceipt.instruction.amount, oldReceipt.instruction.atTime⟩] else []
        shortfallCollections := fun _ _ _ _ ↦ [] }
    sparkDao := 10
    recordedAt := atTime }

/-- Finite case projection. The initial C0 share survives when the first, C1-scoped
document is the only transfer. The C1 use precedes its still-unsettled disposition. -/
def allocation (policy : Policy) : Task → MaterialsAllocation mat
  | .teaching =>
    match (signedRow .teaching).record.transfer.priorUseUnsettled with
    | .otherwiseAgreed agreed => agreed
    | .sharesAtFirstUse => sole mat .O
  | .oldReview =>
    match policy with
    | .retain => sole mat .O
    | .assign => (signedRow .oldReview).record.transfer.laterShortfall

def delta (policy : Policy) (q : Task) (actor : ActorId) (awarded : Bool) : Amount :=
  (allocation policy q).portion actor seat (if awarded then 50 else 0)

theorem scopeAndDisposition (policy : Policy) :
    (signedRow .teaching).record.governs (lessonId .teaching) (ref .teaching) seat ∧
    ¬(signedRow .teaching).record.governs (lessonId .oldReview) (ref .oldReview) seat ∧
    (signedRow .oldReview).record.governs (lessonId .oldReview) (ref .oldReview) seat ∧
    ¬(signedRow .oldReview).record.governs (lessonId .teaching) (ref .teaching) seat ∧
    (signedRow .teaching).record.transfer.priorUnsettledAllocation (tick 33)
      (fun point a ↦ (agreement .teaching).sharesInForce mat point = some a)
      (allocation policy .teaching) ∧
    (agreement .oldReview).sharesInForce mat (tick 10) = some (allocation .retain .oldReview) ∧
    (signedRow .oldReview).record.transfer.laterShortfall = allocation .assign .oldReview :=
  ⟨⟨rfl, rfl, rfl⟩, (fun h ↦ by cases h.1), ⟨rfl, rfl, rfl⟩, (fun h ↦ by cases h.1),
    rfl, rfl, rfl⟩

/-- An unestablished claim affects a handler exactly when the two stipulated adjudicated
amounts differ for that handler. The three other interest dimensions are case facts. -/
def interest (policy : Policy) (m : ReviewMatter) (actor : ActorId) : DirectInterest :=
  let affected (q : Task) := decide (delta policy q actor false ≠ delta policy q actor true)
  ⟨if m = matter .teaching then affected .teaching
    else if m = matter .oldReview then affected .oldReview else false,
    false, false, false⟩

def authority (policy : Policy) : ReviewAuthorities where
  corePartner := fun person _ ↦ person = 10
  initialFinding := fun m person _ ↦ m = matter .teaching ∧ (person = who .O ∨ person = who .N)
  reviewer := fun m person _ ↦ m = matter .oldReview ∧ (person = who .O ∨ person = who .N)
  approvesPayment := fun _ _ _ ↦ False
  interest := fun m actor _ ↦ interest policy m actor
  originalDecisionMaker := fun m ↦ if m = matter .oldReview then some 77 else none
  originalSettlementProposers := fun _ ↦ []
  originalSettlementApprovers := fun _ ↦ []

def terms : ReviewTerms := ⟨30, 41, who .N, .exact (tick 70), tick 72, tick 65, tick 66, 50⟩
def appointment (q : Task) (a : Expert) : ReviewAppointment := ⟨matter q, 10, who a, tick 46⟩
def initial (a : Expert) : InitialFinding :=
  ⟨matter .teaching, .otherDisputedFact, who a, tick 50, "separate teaching evidence", []⟩
def reviewed (a : Expert) : ReviewFinding :=
  ⟨matter .oldReview, who a, tick 51, "separate review evidence", 1201, true⟩
def priorFinding : InitialFinding :=
  ⟨matter .oldReview, .otherDisputedFact, 77, tick 20, "original C0 finding", []⟩

/-- Candidate evaluation uses the source's finding gates. The teaching lead is N;
if that lead has an interest, O needs an applicable core-partner appointment. The old
reviewer must also differ from the original decision-maker, 77. -/
def eligible (policy : Policy) (q : Task) (a : Expert) : Prop :=
  match q with
  | .teaching => initialFindingRecordedConforms (authority policy) terms none
      [appointment .teaching a] [initial a] (initial a)
  | .oldReview => reviewFindingRecordedConforms (authority policy) none
      [appointment .oldReview a] [priorFinding] [reviewed a] (reviewed a)

def oldReviewer : Policy → Expert | .retain => .N | .assign => .O

def chosen (policy : Policy) : Task → Expert | .teaching => .O | .oldReview => oldReviewer policy

theorem interestFromAmounts (policy : Policy) (q : Task) (a : Expert) :
    (authority policy).disinterested (matter q) (who a) (tick 50) ↔
      delta policy q (who a) true = delta policy q (who a) false := by
  cases policy <;> cases q <;> cases a <;>
    unfold ReviewAuthorities.disinterested DirectInterest.affected <;> decide +kernel

theorem roleMenu (policy : Policy) (q : Task) (a : Expert) :
    eligible policy q a ↔ a = chosen policy q := by
  cases policy <;> cases q <;> cases a <;>
    simp [eligible, initialFindingRecordedConforms, initialFindingConformsWithContacts,
      reviewFindingRecordedConforms, reviewFindingConformsWithContacts, independentReviewer,
      didNotMakeOriginalFinding, ReviewAuthorities.disinterested, DirectInterest.affected,
      ReviewAppointment.applies, ReviewAuthorities.mayDecideDispute, initial, reviewed, priorFinding,
      appointment, terms, authority, interest, delta, allocation, signedRow, sole,
      MaterialsAllocation.portion, chosen, oldReviewer, who, matter, lessonId, ReviewMatter.sameCase,
      tick, Moment.by, Moment.before, mat, ref, seat]

/-- An allocation of one indivisible service per task is determined by its two assignees.
The slots must be of the required length, nonoverlapping per person and available to either task. -/
def count (i t c : Expert) : Nat := (if t = i then 1 else 0) + (if c = i then 1 else 0)
def fee : Expert → Nat | .O => 2 | .N => 5
def protectedCash : Nat := 50 + 80
def plan (policy : Policy) (oSlots nSlots balance : Nat) (t c : Expert) : Prop :=
  eligible policy .teaching t ∧ eligible policy .oldReview c ∧
    count .O t c ≤ oSlots ∧ count .N t c ≤ nSlots ∧ protectedCash + fee t + fee c ≤ balance

theorem capacityAndCash (policy : Policy) (oSlots nSlots balance : Nat) :
    (∃ t c, plan policy oSlots nSlots balance t c) ↔
      match policy with
      | .retain => 1 ≤ oSlots ∧ 1 ≤ nSlots ∧ 137 ≤ balance
      | .assign => 2 ≤ oSlots ∧ 134 ≤ balance := by
  cases policy <;>
    simp [plan, roleMenu, chosen, oldReviewer, count, fee, protectedCash]

theorem oneSlotReversal (balance : Nat) :
    (∃ t c, plan .retain 1 1 137 t c) ∧ ¬ (∃ t c, plan .assign 1 1 balance t c) ∧
    (∃ t c, plan .assign 2 1 134 t c) ∧ ¬ (∃ t c, plan .retain 2 1 134 t c) := by
  simp [capacityAndCash]

theorem commonSigner :
    ¬(∃ a, eligible .retain .teaching a ∧ eligible .retain .oldReview a) ∧
    (∃ a, eligible .assign .teaching a ∧ eligible .assign .oldReview a) := by
  simp [roleMenu, chosen, oldReviewer]

#print axioms scopeAndDisposition
#print axioms interestFromAmounts
#print axioms roleMenu
#print axioms capacityAndCash
#print axioms oneSlotReversal
#print axioms commonSigner

end TransferCase
