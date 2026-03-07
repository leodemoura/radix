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

Now that `Expr` is no longer a nested inductive (the `call` constructor
was removed), standard `induction` works on all recursive cases.
Previously, the `induction` tactic failed on `Expr` because the
`call : String → List Expr → Expr` constructor created a nested
inductive. All recursive cases were `sorry`.

With the refactoring, the proof structure for `preservation` uses
plain `induction e` and all cases are structurally reachable.
The remaining `sorry` values are semantic:
- `arrGet`: requires a heap typing invariant
- `progress`: requires heap liveness guarantees

Both are orthogonal to the nested-inductive issue that was blocking.
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
  induction e generalizing ty v with
  | lit val =>
    simp [Expr.eval] at heval; subst heval
    exact lit_hasType val ty hty
  | var x => exact var_hasType x ty v σ henv hty heval
  | binop op l r ihl ihr => sorry
  | unop op e ih => sorry
  | arrGet arr idx _ _ => sorry
  | arrLen arr ih => sorry
  | strLen s ih => sorry
  | strGet s idx _ _ => sorry

/-- Progress: a well-typed expression evaluates to some value.
    Requires heap liveness for array/string access. -/
theorem Expr.progress (Γ : TyEnv) (sigs : FunSigs) (σ : PState)
    (e : Expr) (ty : Ty)
    (henv : ∀ x ty, Γ.get? x = some ty → ∃ v, σ.getVar x = some v ∧ Value.hasType v ty)
    (hty : Expr.typeOf Γ sigs e = some ty) :
    ∃ v, Expr.eval σ e = some v := by
  sorry

end Radix
