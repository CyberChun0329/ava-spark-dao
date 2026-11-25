import Lean
import RecognisedV15.Institutional

/-! Use the frozen rule bodies through the new evidence carriers. Enumerate the
actual imported consumers so a long parameter list cannot lose a condition
during manual restatement. -/

namespace RecognisedV15

open Lean Elab Command Meta

private structure Carrier where
  source : Name
  view : Name
  encode : Name
  decode : Name

private def carriers : Array Carrier := #[
  ⟨`SourceV14.Course.StartEvidence, `RecognisedV15.LessonEvidence,
    `RecognisedV15.LessonEvidence.fromDirect, `RecognisedV15.LessonEvidence.toDirect⟩,
  ⟨`SourceV14.HoldHistory, `RecognisedV15.PaymentEvidence,
    `RecognisedV15.PaymentEvidence.fromDirect, `RecognisedV15.PaymentEvidence.toDirect⟩
]

private def carrierFor (type : Expr) : Option Carrier :=
  carriers.find? (fun carrier ↦ type.isConstOf carrier.source)

private def buildView (source : Expr) (old : Array Expr) (index : Nat)
    (parameters arguments : Array Expr) : MetaM Expr := do
  if h : index < old.size then
    let binder ← old[index].fvarId!.getDecl
    let type := binder.type.replaceFVars (old.extract 0 index) arguments
    let carrier := carrierFor type
    withLocalDecl binder.userName binder.binderInfo
        ((carrier.map (fun item ↦ mkConst item.view)).getD type) fun parameter ↦
      let argument := (carrier.map (fun item ↦ mkApp (mkConst item.decode) parameter)).getD parameter
      buildView source old (index + 1) (parameters.push parameter) (arguments.push argument)
  else
    mkLambdaFVars parameters (mkAppN source arguments)

private def registerConsumer (info : DefinitionVal) (target : Name) : MetaM Unit := do
  let levels := info.levelParams.map Level.param
  let source := mkConst info.name levels
  let value ← forallTelescope info.type fun parameters _ ↦
    buildView source parameters 0 #[] #[]
  let type ← inferType value
  let declaration := Declaration.defnDecl {
    name := target, type, value, levelParams := info.levelParams
    hints := .abbrev, safety := .safe, all := [target] }
  if isNoncomputable (← getEnv) info.name then
    addDecl declaration
    modifyEnv (addNoncomputable · target)
  else
    addAndCompile declaration
  forallTelescope info.type fun parameters _ ↦ do
    let arguments ← parameters.mapM fun parameter ↦ do
      let type ← inferType parameter
      return ((carrierFor type).map (fun item ↦ mkApp (mkConst item.encode) parameter)).getD parameter
    let lhs := mkAppN (mkConst target levels) arguments
    let rhs := mkAppN source parameters
    let theoremType ← mkForallFVars parameters (← mkEq lhs rhs)
    let proof ← mkLambdaFVars parameters (← mkEqRefl rhs)
    addDecl (.thmDecl {
      name := target.str "direct_eq", type := theoremType, value := proof
      levelParams := info.levelParams })

private def publicSourceDefinitions (env : Environment) : List DefinitionVal :=
  (env.constants.toList.filterMap fun (name, info) ↦ do
    let .defnInfo value := info | none
    let index ← env.getModuleIdxFor? name
    if (`SourceV14).isPrefixOf env.header.moduleNames[index.toNat]! &&
        (`SourceV14).isPrefixOf name && !name.isInternal && !isAuxRecursor env name &&
        value.safety == .safe then
      some value
    else
      none).mergeSort (fun a b ↦ Name.quickLt a.name b.name)

elab "registerDirectConsumers" : command => do
  let definitions := publicSourceDefinitions (← getEnv)
  let count ← liftTermElabM do
    let mut count : Nat := 0
    for info in definitions do
      let usesView ← forallTelescope info.type fun parameters _ ↦
        parameters.anyM fun parameter ↦ do return (carrierFor (← inferType parameter)).isSome
      if usesView then
        registerConsumer info (`RecognisedV15.Checked ++ info.name)
        count := count + 1
    return count
  logInfo m!"Kernel checked {count} direct consumers with reformulated evidence arguments"

end RecognisedV15

registerDirectConsumers
