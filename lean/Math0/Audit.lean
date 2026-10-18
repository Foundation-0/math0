/-
Copyright 2026 The math0 Authors. Licensed under the Apache License, Version 2.0.
-/
import Lean

/-!
# Audit commands

Every result in math0 is checked by two commands, which fail the build on any problem.

* `#math0_audit foo` fails unless the axioms used by `foo` are among `propext`,
  `Classical.choice` and `Quot.sound`. In particular it rejects `sorryAx`,
  `Lean.ofReduceBool` / `Lean.trustCompiler` (from `native_decide`), and custom axioms.
* `#math0_proves foo bar` fails unless the type of `foo` is syntactically identical to the type
  of `bar` (the published upstream statement), and `#math0_refutes foo bar` fails unless the
  type of `foo` is exactly `¬` (type of `bar`). The comparison is up to metadata annotations and
  nothing else: no unfolding, no defeq.
-/

namespace Math0.Audit

open Lean Elab Command Meta

/-- The only axioms a math0 result may depend on. -/
def permittedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Remove every `mdata` node, so that annotations do not affect comparisons. -/
partial def stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | .app f a => .app (stripMData f) (stripMData a)
  | .lam n t b bi => .lam n (stripMData t) (stripMData b) bi
  | .forallE n t b bi => .forallE n (stripMData t) (stripMData b) bi
  | .letE n t v b nd => .letE n (stripMData t) (stripMData v) (stripMData b) nd
  | .proj s i e => .proj s i (stripMData e)
  | e => e

/-- Fail unless `n` depends only on the permitted axioms. -/
def auditAxioms (n : Name) : CommandElabM Unit := do
  let axioms ← liftCoreM <| collectAxioms n
  let bad := axioms.filter (· ∉ permittedAxioms)
  unless bad.isEmpty do
    throwError "math0 audit failed: '{n}' depends on non-permitted axioms {bad.toList}"
  logInfo m!"math0 audit: '{n}' depends on axioms {axioms.toList.mergeSort (·.toString < ·.toString)}"

elab "#math0_audit " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  auditAxioms n

/-- Fail unless `ours` has exactly the type `f theirs.type` and the same universe parameters. -/
def checkStatement (ours theirs : Name) (f : Expr → Expr) (verb : String) : CommandElabM Unit := do
  let o ← getConstInfo ours
  let t ← getConstInfo theirs
  unless o.levelParams == t.levelParams do
    throwError "math0 statement check failed: universe parameters differ for '{ours}' and '{theirs}'"
  unless stripMData o.type == f (stripMData t.type) do
    throwError "math0 statement check failed: '{ours}' does not {verb} '{theirs}'.\n\
      ours:   {o.type}\ntheirs: {t.type}"
  auditAxioms ours
  logInfo m!"math0 statement check: '{ours}' {verb}s '{theirs}'"

elab "#math0_proves " ours:ident ppSpace theirs:ident : command => do
  let o ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ours
  let t ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo theirs
  checkStatement o t id "prove"

elab "#math0_refutes " ours:ident ppSpace theirs:ident : command => do
  let o ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ours
  let t ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo theirs
  checkStatement o t mkNot "refute"

/-- For a value question: the upstream statement mentions an unknown `theirAns` (declared upstream
as `def theirAns : T := sorry`). `ours` must have exactly the upstream type with every occurrence
of the constant `theirAns` replaced by the constant `ourAns`, which must not depend on `sorryAx`. -/
elab "#math0_answers " ours:ident ppSpace theirs:ident " with " theirAns:ident " := " ourAns:ident :
    command => do
  let o ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ours
  let t ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo theirs
  let ta ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo theirAns
  let oa ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ourAns
  auditAxioms oa
  checkStatement o t (fun e => e.replace fun
    | .const n us => if n == ta then some (.const oa us) else none
    | _ => none) "answer"

/-- Misformalization reports for value questions: `ours` must have exactly the type
`∀ a, ¬ (upstream type with the unknown `theirAns` replaced by `a`)`, i.e. the upstream statement
is false whatever value is chosen for its unknown. -/
elab "#math0_refutes_every_answer " ours:ident ppSpace theirs:ident " with " theirAns:ident :
    command => do
  let o ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ours
  let t ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo theirs
  let ta ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo theirAns
  let oi ← getConstInfo o
  let ti ← getConstInfo t
  let ai ← getConstInfo ta
  unless oi.levelParams == ti.levelParams && ai.levelParams.isEmpty do
    throwError "math0 statement check failed: universe parameters differ or the unknown is polymorphic"
  let expected ← liftTermElabM do
    withLocalDeclD `a ai.type fun a => do
      let body := (stripMData ti.type).replace fun
        | .const n _ => if n == ta then some a else none
        | _ => none
      mkForallFVars #[a] (mkNot body)
  unless stripMData oi.type == stripMData expected do
    throwError "math0 statement check failed: '{o}' does not refute '{t}' for every value of '{ta}'.\n\
      ours:     {oi.type}\nexpected: {expected}"
  auditAxioms o
  logInfo m!"math0 statement check: '{o}' refutes '{t}' for every value of '{ta}'"

/-- For statements that math0 formalizes itself (they live in `Math0/Statements/`, each a
`def statement : Prop` written and reviewed before any proof attempt): `ours` must have type exactly
`stmt` or exactly `¬ stmt`, and both `stmt` and `ours` must use only the permitted axioms (so the
statement cannot hide a `sorry`). -/
elab "#math0_settles " ours:ident ppSpace stmt:ident : command => do
  let o ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ours
  let s ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stmt
  let si ← getConstInfo s
  unless si.levelParams.isEmpty && stripMData si.type == .sort .zero do
    throwError "math0 statement check failed: '{s}' must be a universe-monomorphic definition of type Prop"
  unless si matches .defnInfo _ do
    throwError "math0 statement check failed: '{s}' must be a definition"
  auditAxioms s
  let ty := stripMData (← getConstInfo o).type
  let verb ← if ty == .const s [] then pure "proves"
    else if ty == mkNot (.const s []) then pure "refutes"
    else throwError "math0 statement check failed: the type of '{o}' is neither '{s}' nor '¬ {s}'"
  auditAxioms o
  logInfo m!"math0 statement check: '{o}' {verb} '{s}'"

end Math0.Audit
