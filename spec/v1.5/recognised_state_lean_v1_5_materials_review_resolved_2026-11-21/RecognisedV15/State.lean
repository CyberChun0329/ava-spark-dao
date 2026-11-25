import RecognisedV15.Evidence
import RecognisedV15.Payments

namespace RecognisedV15

open SourceV14

universe u

/-- The two independent aggregate inputs to the direct rules. Where a direct
rule requires their information to match, that rule still checks the match. -/
structure DirectInputs where
  lesson : Course.StartEvidence
  payment : HoldHistory

/-- Local evidence for the same rules. These fields include evidence of
breaches and payments to the wrong recipient. -/
structure State where
  lesson : LessonEvidence
  payment : PaymentEvidence

def State.fromDirect (inputs : DirectInputs) : State :=
  ⟨LessonEvidence.fromDirect inputs.lesson, PaymentEvidence.fromDirect inputs.payment⟩

def State.toDirect (state : State) : DirectInputs :=
  ⟨state.lesson.toDirect, state.payment.toDirect⟩

@[simp] theorem State.toDirect_fromDirect (inputs : DirectInputs) :
    (fromDirect inputs).toDirect = inputs := by
  cases inputs
  simp [fromDirect, toDirect]

@[simp] theorem State.fromDirect_toDirect (state : State) :
    fromDirect state.toDirect = state := by
  cases state
  simp [fromDirect, toDirect]

def Related (inputs : DirectInputs) (state : State) : Prop :=
  state.toDirect = inputs

theorem state_correspondence (inputs : DirectInputs) (state : State) :
    Related inputs state ↔ State.fromDirect inputs = state := by
  constructor
  · intro matched
    simpa using (congrArg State.fromDirect matched).symm
  · intro matched
    simp [Related, ← matched]

/-- A source consumer can inspect the lesson and payment records together.
Its other arguments, including externally supplied evidence, are fixed by
the caller in the same way on either side. -/
def State.read {α : Sort u} (state : State) (consumer : DirectInputs → α) : α :=
  consumer state.toDirect

theorem observation_equal {α : Sort u} {inputs : DirectInputs} {state : State}
    (related : Related inputs state) (consumer : DirectInputs → α) :
    state.read consumer = consumer inputs := by
  rw [State.read, related]

theorem judgment_iff {inputs : DirectInputs} {state : State}
    (related : Related inputs state) (judgment : DirectInputs → Prop) :
    state.read judgment ↔ judgment inputs :=
  Iff.of_eq (observation_equal related judgment)

/-- Read two observations together. They can concern different points, and
the source consumer keeps both histories and their time and identity tests. -/
theorem history_comparison_equal {α : Sort u}
    {before after : DirectInputs} {earlier later : State}
    (relatedBefore : Related before earlier) (relatedAfter : Related after later)
    (consumer : DirectInputs → DirectInputs → α) :
    consumer earlier.toDirect later.toDirect = consumer before after := by
  rw [relatedBefore, relatedAfter]

theorem observations_through_equal {α : Type u}
    (history : List DirectInputs) (consumer : DirectInputs → α) :
    (history.map State.fromDirect).map (fun state ↦ state.read consumer) =
      history.map consumer := by
  simp [List.map_map, State.read, Function.comp_def]

end RecognisedV15
