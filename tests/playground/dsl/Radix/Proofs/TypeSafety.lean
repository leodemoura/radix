/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.TypeCheck
import Std.Data.HashMap
import Radix.Eval.Stmt

/-! # Type Safety

Progress and preservation theorem statements for the Radix type system.

Note: full proofs require induction over `Expr`, which is a nested inductive
type (due to `call : String → List Expr → Expr`). The standard `induction`
tactic does not support nested inductives, so the recursive cases (binop,
unop, arrGet, arrLen, strLen, strGet) remain incomplete. A complete proof
would use `Expr.rec` directly or restructure the AST to avoid nesting.
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

/-- Type preservation: if a well-typed expression evaluates to a value,
    that value has the expected type. -/
theorem Expr.preservation (Γ : TyEnv) (sigs : FunSigs) (σ : PState)
    (e : Expr) (ty : Ty) (v : Value)
    (henv : ∀ x ty, Γ.get? x = some ty → ∃ v, σ.getVar x = some v ∧ Value.hasType v ty)
    (hty : Expr.typeOf Γ sigs e = some ty)
    (heval : Expr.eval σ e = some v) :
    Value.hasType v ty := by
  cases e with
  | lit val =>
    simp [Expr.eval] at heval; subst heval
    exact lit_hasType val ty hty
  | var x => exact var_hasType x ty v σ henv hty heval
  | call _ _ => simp [Expr.eval] at heval
  -- Recursive cases require induction over the nested inductive `Expr`.
  -- The `induction` tactic does not support nested inductives; a full proof
  -- would use `Expr.rec`.
  | binop op l r => sorry
  | unop op e => sorry
  | arrGet arr idx => sorry
  | arrLen arr => sorry
  | strLen s => sorry
  | strGet s idx => sorry

/-- Progress: a well-typed expression in a well-typed environment can always
    be evaluated (modulo function calls and heap operations). -/
theorem Expr.progress (Γ : TyEnv) (sigs : FunSigs) (σ : PState)
    (e : Expr) (ty : Ty)
    (henv : ∀ x ty, Γ.get? x = some ty → ∃ v, σ.getVar x = some v ∧ Value.hasType v ty)
    (hty : Expr.typeOf Γ sigs e = some ty)
    (hno_call : ∀ f args, e ≠ Expr.call f args) :
    ∃ v, Expr.eval σ e = some v := by
  cases e with
  | lit val =>
    exact ⟨val, by unfold Expr.eval; rfl⟩
  | var x =>
    unfold Expr.typeOf at hty; unfold Expr.eval
    have ⟨w, hw, _⟩ := henv x ty hty
    exact ⟨w, hw⟩
  | call f args => exact absurd rfl (hno_call f args)
  -- Recursive cases require induction (see preservation comment).
  | binop op l r => sorry
  | unop op e => sorry
  | arrGet arr idx => sorry
  | arrLen arr => sorry
  | strLen s => sorry
  | strGet s idx => sorry

end Radix
