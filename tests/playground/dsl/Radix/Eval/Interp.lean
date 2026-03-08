/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Eval.Expr

/-! # Radix Fuel-Based Interpreter

Executable interpreter using fuel to guarantee termination. This is the
"runnable" counterpart to the relational `BigStep` semantics -- useful for
testing and `#guard` assertions, but not the subject of the correctness proofs.

The interpreter is marked `partial` and returns `Option Value` to propagate
`ret` statements: `none` means normal completion, `some v` means a return
was encountered. Errors (type mismatches, missing variables, etc.) are
reported via `ExceptT String`.
-/

namespace Radix

/-- The interpreter monad: mutable `PState` with string error reporting. -/
abbrev InterpM := ExceptT String (StateM PState)

def evalExpr (e : Expr) : InterpM Value := do
  match e.eval (← get) with
  | some v => return v
  | none => throw s!"failed to evaluate expression"

def evalArgs (args : List Expr) : InterpM (List Value) :=
  args.mapM evalExpr

private def mkFrame (params : List (String × Ty)) (args : List Value) : Except String Frame := do
  if params.length ≠ args.length then
    throw s!"arity mismatch: expected {params.length} args, got {args.length}"
  let env := (params.zip args).foldl (fun e (p, v) => e.set p.1 v) Env.empty
  return { env }

/-- Fuel-based interpreter. Returns `none` for normal completion,
`some v` when a `ret` statement is reached. -/
partial def Stmt.interp (fuel : Nat) (s : Stmt) : InterpM (Option Value) := do
  match fuel with
  | 0 => throw "out of fuel"
  | fuel + 1 =>
    match s with
    | .skip => return none

    | .assign x e =>
      let v ← evalExpr e
      let σ ← get
      match σ.setVar x v with
      | some σ' => set σ'; return none
      | none => throw s!"assign: no active frame"

    | .decl x _ty e =>
      let v ← evalExpr e
      let σ ← get
      match σ.setVar x v with
      | some σ' => set σ'; return none
      | none => throw s!"decl: no active frame"

    | .seq s₁ s₂ =>
      match ← s₁.interp fuel with
      | some v => return some v
      | none => s₂.interp fuel

    | .ite c t f =>
      let v ← evalExpr c
      match v with
      | .bool true => t.interp fuel
      | .bool false => f.interp fuel
      | _ => throw "if: condition must be bool"

    | .while c b =>
      let v ← evalExpr c
      match v with
      | .bool true =>
        match ← b.interp fuel with
        | some v => return some v
        | none => s.interp fuel
      | .bool false => return none
      | _ => throw "while: condition must be bool"

    | .alloc x _ty szExpr =>
      let v ← evalExpr szExpr
      match v with
      | .uint64 sz =>
        let σ ← get
        let (a, heap') := σ.heap.alloc (Array.replicate sz.toNat (.uint64 0))
        let σ' := { σ with heap := heap' }
        match σ'.setVar x (.addr a) with
        | some σ'' => set σ''; return none
        | none => throw "alloc: no active frame"
      | _ => throw "alloc: size must be uint64"

    | .free e =>
      let v ← evalExpr e
      match v with
      | .addr a =>
        let σ ← get
        match σ.heap.free a with
        | some heap' => set { σ with heap := heap' }; return none
        | none => throw s!"free: invalid address {a}"
      | _ => throw "free: expected address"

    | .arrSet arr idx val =>
      let va ← evalExpr arr
      let vi ← evalExpr idx
      let vv ← evalExpr val
      match va, vi with
      | .addr a, .uint64 i =>
        let σ ← get
        match σ.heap.write a i.toNat vv with
        | some heap' => set { σ with heap := heap' }; return none
        | none => throw s!"arrSet: write failed at addr {a} index {i}"
      | _, _ => throw "arrSet: expected address and uint64 index"

    | .ret e =>
      let v ← evalExpr e
      return some v

    | .block stmts =>
      let rec go : List Stmt → InterpM (Option Value)
        | [] => return none
        | stmt :: rest => do
          match ← stmt.interp fuel with
          | some v => return some v
          | none => go rest
      go stmts

    | .callStmt name args =>
      let σ ← get
      match σ.lookupFun name with
      | none => throw s!"undefined function: {name}"
      | some fd =>
        let vs ← evalArgs args
        match mkFrame fd.params vs with
        | .error msg => throw msg
        | .ok frame =>
          modify fun σ => σ.pushFrame frame
          let _retVal ← fd.body.interp fuel  -- return value discarded for void calls
          let σ' ← get
          match σ'.popFrame with
          | some (_, σ'') => set σ''; return none
          | none => throw "callStmt: frame stack underflow"

    | .scope params args body =>
      let vs ← evalArgs args
      match mkFrame params vs with
      | .error msg => throw msg
      | .ok frame =>
        modify fun σ => σ.pushFrame frame
        let _retVal ← body.interp fuel
        let σ' ← get
        match σ'.popFrame with
        | some (_, σ'') => set σ''; return none
        | none => throw "scope: frame stack underflow"

/-- Run a program with the given fuel. -/
def Program.run (p : Program) (fuel : Nat := 1000) : Except String PState :=
  let σ := PState.initFromProgram p
  match p.main.interp fuel |>.run σ with
  | (.ok _, σ') => .ok σ'
  | (.error msg, _) => .error msg

/-- Run a standalone statement with initial state. -/
def Stmt.run (s : Stmt) (fuel : Nat := 1000) : Except String PState :=
  match s.interp fuel |>.run {} with
  | (.ok _, σ') => .ok σ'
  | (.error msg, _) => .error msg

end Radix
