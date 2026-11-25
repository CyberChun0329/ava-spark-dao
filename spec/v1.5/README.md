# Spark DAO v1.5 specification

Follow the rules from their [English text](Spark_DAO_Teaching_and_Research_Rules_v1_5_bilingual.md) through the [direct Lean translation](source_lean_v1_5_materials_review_resolved_2026-11-21/SourceV14.lean) and the [recognised-state Lean model and proofs](recognised_state_lean_v1_5_materials_review_resolved_2026-11-21/RecognisedV15/Workflow.lean) to the [Spark DAO App on AVA Core and SDK](../../README.md).

The rules file reproduces the bilingual v1.5 text. The English text governs the translation. The rules refer to separate written lesson terms and a confirmation form. Those documents are outside this bundle and remain inputs wherever the rules call for them.

The adjacent Lean projects are the G3 revision dated 2026-11-25. The revision addresses whether a later transfer can change the treatment of previously settled original material charges. It corrects the formal reading of the existing v1.5 rules. The earlier frozen pair is the historical baseline used in the research record. The direct project retains its existing `SourceV14` module name and the recognised-state project uses it as a relative Lake dependency.

The workflow theorems `step_iff`, `bisimulation`, and `path_iff` relate the two Lean models over their common formal domain. The app has separate engineering evidence from its [installation and business tests](../../README.md#run-the-tests). Those tests exercise app interfaces and selected workflows. A proof that the whole app refines either Lean model is outside the scope of this bundle.

## Build the models

Use Lean 4.36.0, as pinned by both projects. From this directory run:

```sh
cd recognised_state_lean_v1_5_materials_review_resolved_2026-11-21
lake build
lake env lean WorkflowChecks.lean
```

The recognised-state build compiles the adjacent direct project through its Lake dependency.
