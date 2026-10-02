import Lean




open Lean Meta Elab Command

namespace EventTransport

structure St where
  needs : NameMap Bool := {}
  done : NameMap Name := {}
  busy : NameSet := {}
  log : Array Name := #[]
  failed : Array (Name × String) := #[]

/-- Module indices that import (transitively) one of `targets`. -/
def relevantModules (env : Environment) (targets : Array Name) : Std.HashSet Nat := Id.run do
  let names := env.header.moduleNames
  let mut idx : Std.HashMap Name Nat := {}
  for i in [0:names.size] do
    idx := idx.insert names[i]! i
  let tmods : Std.HashSet Nat := targets.foldl (init := {}) fun s c =>
    match env.getModuleIdxFor? c with
    | some m => s.insert m.toNat
    | none => s
  let mut rel : Std.HashSet Nat := {}
  for i in [0:names.size] do
    if tmods.contains i then
      rel := rel.insert i
    else
      let imps := env.header.moduleData[i]!.imports
      if imps.any (fun imp => match idx.get? imp.module with
          | some j => rel.contains j
          | none => false) then
        rel := rel.insert i
  return rel

partial def needs (repl : NameMap Name) (rel : Std.HashSet Nat) (c : Name) :
    StateRefT St CoreM Bool := do
  if repl.contains c then return true
  if let some b := (← get).needs.find? c then return b
  let env ← getEnv
  -- constants from modules that cannot see any replaced constant never need transport
  if let some m := env.getModuleIdxFor? c then
    unless rel.contains m.toNat do
      modify fun s => { s with needs := s.needs.insert c false }
      return false
  modify fun s => { s with needs := s.needs.insert c false }  -- provisional (cycles)
  let some ci := env.find? c | return false
  let mut cs := ci.type.getUsedConstants
  if let .defnInfo di := ci then
    cs := cs ++ di.value.getUsedConstants
  let mut b := false
  for k in cs do
    if ← needs repl rel k then
      b := true
      break
  modify fun s => { s with needs := s.needs.insert c b }
  return b

/-- Kernel-check `decl` synchronously (`Kernel.Environment.addDecl`, current options, so the
default heartbeat budget); on success add it with `addDecl`, on failure record it and skip. -/
def checkedAdd (c : Name) (decl : Declaration) : StateRefT St CoreM Unit := do
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl with
  | .ok _ => addDecl decl
  | .error e =>
    let msg ← (e.toMessageData (← getOptions)).toString
    modify fun s => { s with failed := s.failed.push (c, msg) }

def newName (pfx : Name) (c : Name) : Name :=
  pfx ++ (privateToUserName? c |>.getD c)

partial def transportConst (pfx : Name) (repl : NameMap Name) (rel : Std.HashSet Nat)
    (dry : Bool) (c : Name) : StateRefT St CoreM Name := do
  if let some c' := repl.find? c then return c'
  unless ← needs repl rel c do return c
  if let some c' := (← get).done.find? c then return c'
  if (← get).busy.contains c then
    throwError "EventTransport: cycle at {c}"
  modify fun s => { s with busy := s.busy.insert c }
  let env ← getEnv
  let some ci := env.find? c | throwError "EventTransport: unknown {c}"
  let cNew := newName pfx c
  let rw (e : Expr) : StateRefT St CoreM Expr := do
    let mut m : NameMap Name := {}
    for k in e.getUsedConstants do
      if ← needs repl rel k then
        m := m.insert k (← transportConst pfx repl rel dry k)
    return e.replace fun
      | .const k ls => (m.find? k).map fun k' => .const k' ls
      | _ => none
  let newTy ← rw ci.type
  match ci with
  | .thmInfo ti =>
    let newVal ← rw ti.value
    unless dry do
      checkedAdd c (.thmDecl (TheoremVal.mk (ConstantVal.mk cNew ti.levelParams newTy)
        newVal [cNew]))
  | .defnInfo di =>
    let newVal ← rw di.value
    unless dry do
      checkedAdd c (.defnDecl (DefinitionVal.mk (ConstantVal.mk cNew di.levelParams newTy)
        newVal di.hints di.safety [cNew]))
  | _ => throwError "EventTransport: cannot transport non-theorem/definition {c}"
  modify fun s =>
    { s with done := s.done.insert c cNew, busy := s.busy.erase c, log := s.log.push c }
  return cNew

/-- Transport `roots`; returns the log and the failures. -/
def run (pfx : Name) (repl : List (Name × Name)) (roots : List Name) (dry : Bool) :
    CoreM (Array Name × Array (Name × String) × NameMap Name) := do
  let replMap : NameMap Name := repl.foldl (init := {}) fun m (a, b) => m.insert a b
  let rel := relevantModules (← getEnv) (repl.map (·.1)).toArray
  let act : StateRefT St CoreM Unit := do
    for r in roots do
      discard <| transportConst pfx replMap rel dry r
  let ((), s) ← act.run {}
  return (s.log, s.failed, s.done)

end EventTransport
