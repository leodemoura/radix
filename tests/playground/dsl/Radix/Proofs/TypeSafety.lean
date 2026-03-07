/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.TypeCheck
import Std.Data.HashMap
import Radix.Eval.Stmt

/-! # Type Safety

Progress and preservation theorems for the Radix type system.

The remaining `sorry` values are semantic:
- `arrGet`: requires a heap typing invariant
- `progress`: requires heap liveness guarantees
-/

namespace Radix
open Std

/-- A value is well-typed if it matches the expected type. -/
def Value.hasType : Value → Ty → Prop
  | .uint64 _, .uint64 => True
  | .bool _,   .bool   => True
  | .unit,     .unit    => True
  | .str _,    .string  => True
  | .addr _,   .array _ => True
  | _, _ => False

/-- Literal values have the type assigned by `typeOf`. -/
private theorem lit_hasType (v : Value) (ty : Ty)
    (hty : Expr.typeOf Γ sigs (.lit v) = some ty) :
    Value.hasType v ty := by
  unfold Expr.typeOf at hty
  cases v <;> simp at hty <;> subst_vars <;> simp [Value.hasType]

/-- Variables in a well-typed environment evaluate to well-typed values. -/
private theorem var_hasType (x : String) (ty : Ty) (v : Value) (σ : PState)
    (henv : ∀ x ty, Γ.get? x = some ty → ∃ v, σ.getVar x = some v ∧ Value.hasType v ty)
    (hty : Expr.typeOf Γ sigs (.var x) = some ty)
    (heval : Expr.eval σ (.var x) = some v) :
    Value.hasType v ty := by
  unfold Expr.typeOf at hty; unfold Expr.eval at heval
  have ⟨w, hw, hhas⟩ := henv x ty hty
  simp [hw] at heval; subst heval; exact hhas

/-- Binary operation evaluation preserves types. -/
private theorem BinOp.eval_preserves_type {op : BinOp} {vl vr v : Value} {tl tr ty : Ty}
    (hvl : vl.hasType tl) (hvr : vr.hasType tr)
    (hty : op.typeOfResult tl tr = some ty)
    (hev : op.eval vl vr = some v) :
    v.hasType ty := by
  cases op
  all_goals (first
    | (-- eq and ne: eval works on any values, typeOfResult needs tl == tr
       simp [BinOp.eval] at hev; subst hev
       simp [BinOp.typeOfResult] at hty; obtain ⟨_, rfl⟩ := hty
       simp [Value.hasType])
    | (-- arithmetic without guards (add, sub, mul) and comparisons/logic
       cases tl <;> cases tr <;> simp [BinOp.typeOfResult] at hty
       subst hty
       cases vl <;> simp [Value.hasType] at hvl
       cases vr <;> simp [Value.hasType] at hvr
       simp [BinOp.eval] at hev; subst hev; simp [Value.hasType])
    | (-- div, mod: have an if guard
       cases tl <;> cases tr <;> simp [BinOp.typeOfResult] at hty
       subst hty
       cases vl <;> simp [Value.hasType] at hvl
       cases vr <;> simp [Value.hasType] at hvr
       simp [BinOp.eval] at hev; obtain ⟨_, rfl⟩ := hev; simp [Value.hasType]))

/-- Unary operation evaluation preserves types. -/
private theorem UnaryOp.eval_preserves_type {op : UnaryOp} {v w : Value} {t ty : Ty}
    (hv : v.hasType t)
    (hty : op.typeOfResult t = some ty)
    (hev : op.eval v = some w) :
    w.hasType ty := by
  cases op <;> cases t <;> simp [UnaryOp.typeOfResult] at hty <;>
    subst ty <;> cases v <;> simp [Value.hasType] at hv <;>
    simp [UnaryOp.eval] at hev <;> subst hev <;> simp [Value.hasType]

/-- Type preservation: if a well-typed expression evaluates to a value,
    that value has the expected type. -/
theorem Expr.preservation (Γ : TyEnv) (sigs : FunSigs) (σ : PState)
    (e : Expr) (ty : Ty) (v : Value)
    (henv : ∀ x ty, Γ.get? x = some ty → ∃ v, σ.getVar x = some v ∧ Value.hasType v ty)
    (hty : Expr.typeOf Γ sigs e = some ty)
    (heval : Expr.eval σ e = some v) :
    Value.hasType v ty := by
  induction e generalizing ty v with
  | lit val =>
    simp [Expr.eval] at heval; subst heval
    exact lit_hasType val ty hty
  | var x => exact var_hasType x ty v σ henv hty heval
  | binop op l r ihl ihr =>
    simp only [Expr.typeOf] at hty
    simp only [bind, Option.bind] at hty
    cases htl : Expr.typeOf Γ sigs l <;> simp [htl] at hty
    rename_i tl
    cases htr : Expr.typeOf Γ sigs r <;> simp [htr] at hty
    rename_i tr
    simp only [Expr.eval] at heval
    simp only [bind, Option.bind] at heval
    cases hvl : Expr.eval σ l <;> simp [hvl] at heval
    rename_i vl
    cases hvr : Expr.eval σ r <;> simp [hvr] at heval
    rename_i vr
    exact BinOp.eval_preserves_type (ihl tl vl htl hvl) (ihr tr vr htr hvr) hty heval
  | unop op e ih =>
    simp only [Expr.typeOf] at hty
    simp only [bind, Option.bind] at hty
    cases ht : Expr.typeOf Γ sigs e <;> simp [ht] at hty
    rename_i t
    simp only [Expr.eval] at heval
    simp only [bind, Option.bind] at heval
    cases hw : Expr.eval σ e <;> simp [hw] at heval
    rename_i w
    exact UnaryOp.eval_preserves_type (ih t w ht hw) hty heval
  | arrGet arr idx _ _ =>
    -- Requires a heap typing invariant: if the array handle is well-typed
    -- with element type `elemTy`, then all values stored in the heap at
    -- that address have type `elemTy`. This is beyond our current framework.
    sorry
  | arrLen arr _ =>
    -- typeOf returns .uint64, eval produces .uint64 _
    simp only [Expr.typeOf] at hty
    simp only [bind, Option.bind] at hty
    cases h1 : Expr.typeOf Γ sigs arr <;> simp [h1] at hty
    rename_i aty; cases aty <;> simp at hty; subst ty
    simp only [Expr.eval] at heval
    simp only [bind, Option.bind] at heval
    cases h2 : Expr.eval σ arr <;> simp [h2] at heval
    rename_i va; cases va <;> simp at heval
    rename_i a
    cases h3 : Heap.arraySize σ.heap a <;> simp [h3] at heval
    subst heval; simp [Value.hasType]
  | strLen s _ =>
    simp only [Expr.typeOf] at hty
    simp only [bind, Option.bind] at hty
    cases h1 : Expr.typeOf Γ sigs s <;> simp [h1] at hty
    rename_i st; cases st <;> simp at hty; subst ty
    simp only [Expr.eval] at heval
    simp only [bind, Option.bind] at heval
    cases h2 : Expr.eval σ s <;> simp [h2] at heval
    rename_i vs; cases vs <;> simp at heval
    subst heval; simp [Value.hasType]
  | strGet s idx _ _ =>
    simp only [Expr.typeOf] at hty
    simp only [bind, Option.bind] at hty
    cases h1 : Expr.typeOf Γ sigs s <;> simp [h1] at hty
    rename_i st; cases st <;> simp at hty
    cases h4 : Expr.typeOf Γ sigs idx <;> simp [h4] at hty
    rename_i it; cases it <;> simp at hty; subst ty
    simp only [Expr.eval] at heval
    simp only [bind, Option.bind] at heval
    cases h2 : Expr.eval σ s <;> simp [h2] at heval
    rename_i vs; cases vs <;> simp at heval
    cases h3 : Expr.eval σ idx <;> simp [h3] at heval
    rename_i vi; cases vi <;> simp at heval
    obtain ⟨_, rfl⟩ := heval
    simp [Value.hasType]

/-- Progress: a well-typed expression evaluates to some value.

This theorem as stated is not provable without additional assumptions:
- Division/modulo by zero: `e / 0` is well-typed but `eval` returns `none`.
- Array access: requires heap liveness and bounds checking invariants.
- String access: requires string index bounds invariants.

A correct formulation would either exclude partial operations from the
type system, add a totality/definedness judgment, or strengthen the
preconditions with heap and bounds invariants. -/
theorem Expr.progress (Γ : TyEnv) (sigs : FunSigs) (σ : PState)
    (e : Expr) (ty : Ty)
    (henv : ∀ x ty, Γ.get? x = some ty → ∃ v, σ.getVar x = some v ∧ Value.hasType v ty)
    (hty : Expr.typeOf Γ sigs e = some ty) :
    ∃ v, Expr.eval σ e = some v := by
  sorry

end Radix
