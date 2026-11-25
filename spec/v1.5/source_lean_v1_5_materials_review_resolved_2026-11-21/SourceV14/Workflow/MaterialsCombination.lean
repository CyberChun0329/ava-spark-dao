import SourceV14.Operations

namespace SourceV14.Workflow.Materials

open Confirmation Course

/-- One agreement's place-by-place contribution to a proposed lesson combination. -/
structure CombinationPart where
  terms : MaterialsTerms
  places : List PlaceMaterials
  affectedRightsHolders : List MaterialsAdjustment := []
  consents : List MaterialsConsent := []

def CombinationPart.coversUse (part : CombinationPart) (terms : MaterialsTerms)
    (place : Place) (material : MaterialId) : Prop :=
  part.terms = terms ∧ ∃ row ∈ part.places, row.place = place ∧ material ∈ row.materials

def CombinationPart.agreedAdjustments (part : CombinationPart) (checkedAt : Moment) : Prop :=
  ∀ affected ∈ part.affectedRightsHolders,
    part.terms.pricing.covers affected.material ∧
    (∃ allocation, part.terms.sharesInForce affected.material affected.shareTime =
      some allocation ∧ affected.holder ∈ allocation.holders) ∧
    ∃ consent ∈ part.terms.consents ++ part.consents,
      consent.material = affected.material ∧ consent.actor = affected.holder ∧
      consent.termsReference = part.terms.agreementReference ∧
      affected.shareTime.by consent.point ∧ consent.point.by checkedAt

/-- A §5.3 check of the known scope at the time. Each option is a whole priced
combination, including any earlier use it builds on and any other applicable places. -/
structure CombinationCheck where
  lesson : Lesson
  checkedAt : Moment
  recordedAt : Moment
  reference : String
  options : List (List CombinationPart)
  /-- Evidence verifies the performed check and its complete then-known scope,
  including the applicable pricing options and the affected holders' assents. -/
  verifiesScope : String → Lesson → Moment → List (List CombinationPart) → Prop

def CombinationCheck.conforms (check : CombinationCheck) (ev : StartEvidence)
    (adopted : List MaterialsTerms) : Prop :=
  check.reference ≠ "" ∧ check.checkedAt.by check.recordedAt ∧ check.options ≠ [] ∧
  check.verifiesScope check.reference check.lesson check.checkedAt check.options ∧
  (∃ roster forms, ev.arrangementFormsAt check.lesson check.checkedAt roster forms ∧
    ∀ parts ∈ check.options, ∀ part ∈ parts, ∀ row ∈ part.places,
      ∃ form ∈ forms, form.place = row.place ∧ form.confirmedAt.by check.checkedAt ∧
        form.materialsOrBundle = some part.terms.materialsOrBundle ∧
        form.materialsTermsRef = some part.terms.agreementReference ∧
        form.materialsPayer = some part.terms.accountingAndPaymentParty) ∧
  ∀ parts ∈ check.options,
    (parts.map (·.terms.agreementReference)).Nodup ∧
    (parts.flatMap (fun part ↦ part.places.flatMap (fun row ↦
      row.materials.map (row.place.id, ·)))).Nodup ∧
    (∀ part ∈ parts, part.terms ∈ adopted ∧ part.terms.lesson = check.lesson.id ∧
      part.terms.agreedAt.by check.checkedAt ∧ part.places ≠ [] ∧
      (part.places.map (·.place.id)).Nodup ∧
      (∀ row ∈ part.places, row.materials ≠ []) ∧
      part.terms.covers part.places ∧ part.agreedAdjustments check.checkedAt) ∧
    let places := parts.flatMap CombinationPart.places
    let charges := parts.flatMap (fun part ↦ part.terms.pricing.charges part.places)
    (∀ charge ∈ charges, 0 ≤ charge.amount) ∧
      sumAmounts charges MaterialsCharge.amount ≤ materialsCapRate * materialsCapBase places

end SourceV14.Workflow.Materials
