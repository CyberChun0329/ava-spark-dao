#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
spec="$(cd "$here/../../../spec/v1.5" && pwd)"
direct=source_lean_v1_5_materials_review_resolved_2026-11-21
recognised=recognised_state_lean_v1_5_materials_review_resolved_2026-11-21
material=SourceV14/Workflow/Materials.lean
stage="$(mktemp -d "${TMPDIR:-/tmp}/spark-v15-witnesses.XXXXXX")"
trap 'rm -rf "$stage"' EXIT
mode="${1:-all}"
case "$mode" in all|hold|frozen|revised) ;; *) echo "Usage: bash check.sh [all|hold|frozen|revised]" >&2; exit 2;; esac

check_version() {
  printf '%s  %s\n' "$1" "$2" | shasum -a 256 -c -
}

check_hold() (
  work="$stage/hold"
  mkdir "$work"
  cp "$spec/$direct/"{SourceV14.lean,lakefile.toml,lake-manifest.json,lean-toolchain} "$work/"
  mkdir "$work/SourceV14"
  cp "$spec/$direct/SourceV14/"*.lean "$work/SourceV14/"
  cd "$work"
  git apply "$here/hold-candidate-input.diff"
  shasum -a 256 -c "$here/hold-candidate-input.sha256"
  lean --version
  lake build --wfail
  echo "== hold: Continuous_Hold_Release_Witness =="
  lake env lean -DwarningAsError=true "$here/Continuous_Hold_Release_Witness.lean"
)

check_witnesses() (
  version="$1"
  work="$stage/$version"
  proofs="$work/witnesses"
  mkdir -p "$proofs" "$work/$direct" "$work/$recognised"
  cp -R "$spec/$direct/SourceV14" "$work/$direct/"
  cp -R "$spec/$recognised/RecognisedV15" "$work/$recognised/"
  for file in lakefile.toml lake-manifest.json lean-toolchain; do
    cp "$spec/$direct/$file" "$work/$direct/"
    cp "$spec/$recognised/$file" "$work/$recognised/"
  done
  cp "$spec/$direct/SourceV14.lean" "$work/$direct/"
  cp "$spec/$recognised/RecognisedV15.lean" "$work/$recognised/"
  cp "$here/"*.lean "$proofs/"

  echo "== $version model =="
  check_version ef7540d6fef81b4b7bae3a1b24979f9a8a602ce45107ba04f005e29d91d321c5 "$work/$direct/$material"
  if [[ "$version" = frozen ]]; then
    (cd "$work/$direct" && git apply --reverse "$here/G3.actual.diff")
    check_version 6b4e206d83c048db7495cadf6bcc5e95e7bf41b19000ab275da58840d67f1651 "$work/$direct/$material"
  fi
  check_version 225a518d8951853db403ddb651562d33bf4502a9011a7a3a513b9033ad17f498 \
    "$work/$recognised/RecognisedV15/Workflow.lean"

  cat "$spec/$direct/FidelityMaterialsProvisionChecks.lean" "$here/ProvisionFixtureExports.lean.inc" \
    > "$proofs/ProvisionWitnessFixture.lean"
  cd "$work/$recognised"
  lean --version
  lake build --wfail

  run() {
    LEAN_PATH="$proofs" lake env lean --root="$proofs" -DwarningAsError=true "$@"
  }

  check_module() {
    module="$1"
    echo "== $version: $module =="
    run -o "$proofs/$module.olean" "$proofs/$module.lean"
  }

  check_module ProvisionWitnessFixture
  if [[ "$version" = revised ]]; then
    check_module G3SameSecond
    exit
  fi

  cat "$spec/$direct/FidelityMaterialsProvisionChecks.lean" "$here/JointM.delta.lean" \
    > "$proofs/JointMProof.lean"
  sed -e 's/^namespace TransferCase$/namespace TimedTransferCase/' \
    -e 's/^end TransferCase$/end TimedTransferCase/' \
    -e 's/^open SourceV14 SourceV14.Workflow$/open SourceV14 SourceV14.Workflow TransferCase/' \
    -e 's/tick 60/tick 51/g' -e 's/tick 55/tick 51/g' -e 's/tick 52/tick 51/g' \
    "$here/TransferPortions.lean" > "$proofs/TimedTransferPortions.lean"

  for name in TPrefix TNormal TFault JointMProof PendingReserve \
    PendingProjection PendingCase JointHistory OtherBranches Menu TransferEligibility TransferReviewPath \
    TimedTransferPortions ReviewInterestCandidate CostProjection EvidencePayment AcceptedRetainedFees \
    SplitReceipt CompetingPrefunding ReceiptFiling TransferReserve; do
    check_module "$name"
  done
)

case "$mode" in
  all) check_hold; check_witnesses frozen; check_witnesses revised ;;
  hold) check_hold ;;
  *) check_witnesses "$mode" ;;
esac
